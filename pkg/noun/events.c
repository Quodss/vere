//! @file events.c
//!
//! incremental, orthogonal, paginated loom snapshots
//!
//! ### components
//!
//!   - page: 16KB chunk of the loom.
//!   - north segment (u3e_image, north.bin): low contiguous loom pages,
//!     (in practice, the home road heap). indexed from low to high:
//!     in-order on disk. in a file-backed mapping by default.
//!   - south segment (u3e_image, south.bin): high contiguous loom pages,
//!     (in practice, the home road stack). indexed from high to low:
//!     reversed on disk.
//!   - patch memory (memory.bin): new or changed pages since the last snapshot
//!   - patch control (u3e_control control.bin): patch metadata, watermarks,
//!     and indices/mugs for pages in patch memory.
//!
//! ### initialization (u3e_live())
//!
//!   - with the loom already mapped, all pages are marked dirty in a bitmap.
//!   - if snapshot is missing or partial, empty segments are created.
//!   - if a patch is present, it's applied (crash recovery).
//!   - snapshot segments are mapped or copied onto the loom;
//!     all included pages are marked clean and protected (read-only).
//!
//! #### page faults (u3e_fault())
//!
//!   - stores into protected pages generate faults (currently SIGSEGV,
//!     handled outside this module).
//!   - faults are handled by dirtying the page and switching protections to
//!     read/write.
//!   - a guard page is initially placed in the approximate middle of the free
//!     space between the heap and stack at the time of the first page fault.
//!     when a fault is detected in the guard page, the guard page is recentered
//!     in the free space of the current road. if the guard page cannot be
//!     recentered, then memory exhaustion has occurred.
//!
//! ### updates (u3e_save())
//!
//!   - all updates to a snapshot are made through a patch.
//!   - high/low watermarks for the north/south segments are established,
//!     and dirty pages below/above them are added to the patch.
//!     - modifications have been caught by the fault handler.
//!     - newly-used pages are automatically included (preemptively dirtied).
//!     - unused, innermost pages are reclaimed (segments are truncated to the
//!       high/low watermarks; the last page in each is always adjacent to the
//!       contiguous free space).
//!   - patch pages are written to memory.bin, metadata to control.bin.
//!   - the patch is applied to the snapshot segments, in-place.
//!   - segments are fsync'd; patch files are deleted.
//!   - memory protections (and file-backed mappings) are re-established.
//!
//! ### invariants
//!
//!  definitions:
//!    - a clean page is PROT_READ and 0 in the bitmap
//!    - a dirty page is (PROT_READ|PROT_WRITE) and 1 in the bitmap
//!    - the guard page is PROT_NONE and 1 in the bitmap
//!
//!  assumptions:
//!    - all memory access patterns are outside-in, a page at a time
//!      - ad-hoc exceptions are supported by calling u3e_ward()
//!
//!  - there is a single guard page, between the segments
//!  - dirty pages only become clean by being:
//!    - loaded from a snapshot during initialization
//!    - present in a snapshot after save
//!  - clean pages only become dirty by being:
//!    - modified (and caught by the fault handler)
//!    - orphaned due to segment truncation (explicitly dirtied)
//!  - at points of quiescence (initialization, after save)
//!    - all pages of the north and south segments are clean
//!    - all other pages are dirty
//!
//! ### limitations
//!
//!   - loom page size is fixed (16 KB), and must be a multiple of the
//!     system page size.
//!   - update atomicity is crucial:
//!     - patch application must either completely succeed or
//!       leave on-disk segments (memory image) intact.
//!     - unapplied patches can be discarded (triggering event replay),
//!       but once patch application begins it must succeed.
//!     - may require integration into the overall signal-handling regime.
//!   - any errors are handled with assertions; error messages are poor;
//!     failed/partial writes are not retried.
//!
//! ### enhancements
//!
//!   - use platform specific page fault mechanism (mach rpc, userfaultfd, &c).
//!   - parallelism (conflicts with demand paging)
//!

#include "events.h"

#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>

#include "log.h"
#include "manage.h"
#include "options.h"
#include "retrieve.h"
#include "types.h"

/* _ce_len:       byte length of pages
** _ce_len_words: word length of pages
** _ce_page:      byte length of a single page
** _ce_ptr:       void pointer to a page
*/
#define _ce_len(i)        ((size_t)(i) << (u3a_page + 2))
#define _ce_len_words(i)  ((size_t)(i) << u3a_page)
#define _ce_page          _ce_len(1)
#define _ce_ptr(i)        ((void *)((c3_c*)u3_Loom + _ce_len(i)))

/// Snapshotting system.
u3e_pool u3e_Pool;

static c3_l
_ce_mug_page(void* ptr_v)
{
  //  XX trailing zeros
  // return u3r_mug_bytes(ptr_v, _ce_page);
  return u3r_mug_words(ptr_v, _ce_len_words(1));
}

#ifdef U3_SNAPSHOT_VALIDATION
/* Image check.
*/
struct {
  c3_n nor_n;
  c3_n sou_n;
  c3_m mug_m[u3a_pages]; // note dozreg: way too big for VERE_64
} u3K;

/* u3e_check(): compute a checksum on all memory within the watermarks.
*/
void
u3e_check(c3_c* cap_c)
{
  c3_n nor_n = 0;
  c3_n sou_n = 0;

  {
    u3_post low_p, hig_p;
    u3m_water(&low_p, &hig_p);

    nor_n = (low_p + (_ce_len_words(1) - 1)) >> u3a_page;
    sou_n = u3P.pag_n - (hig_p >> u3a_page);
  }

  /* compute checksum over active pages.
  */
  {
    c3_n i_n, sum_n;
    c3_m mug_m;

    sum_n = 0;
    for ( i_n = 0; i_n < nor_n; i_n++ ) {
      mug_m = _ce_mug_page(_ce_ptr(i_n));
      if ( strcmp(cap_c, "boot") ) {
        u3_assert(mug_m == u3K.mug_m[i_n]);
      }
      sum_n += mug_m;
    }
    for ( i_n = 0; i_n < sou_n; i_n++ ) {
      mug_m = _ce_mug_page(_ce_ptr((u3P.pag_n - (i_n + 1))));
      if ( strcmp(cap_c, "boot") ) {
        u3_assert(mug_m == u3K.mug_m[(u3P.pag_n - (i_n + 1))]);
      }
      sum_n += mug_m;
    }
    u3l_log("%s: sum %x (%x, %x)", cap_c, sum_n, nor_n, sou_n);
  }
}
#endif

/* _ce_flaw_mmap(): remap non-guard page after fault.
*/
static inline c3_i
_ce_flaw_mmap(c3_n pag_n)
{
  // NB: must be static, since the stack is grown via page faults, and
  // we're already in a page fault handler.
  //
  static c3_y con_y[_ce_page];

  // save contents of page, to be restored after the mmap
  //
  memcpy(con_y, _ce_ptr(pag_n), _ce_page);

  // map the dirty page into the ephemeral file
  //
  if ( MAP_FAILED == mmap(_ce_ptr(pag_n),
                          _ce_page,
                          (PROT_READ | PROT_WRITE),
                          (MAP_FIXED | MAP_SHARED),
                          u3P.eph_i, _ce_len(pag_n)) )
  {
    fprintf(stderr, "loom: fault mmap failed (%u): %s\r\n",
                     pag_n, strerror(errno));
    return 1;
  }

  // restore contents of page
  //
  memcpy(_ce_ptr(pag_n), con_y, _ce_page);

  return 0;
}

/* _ce_flaw_mprotect(): protect page after fault.
*/
static inline c3_i
_ce_flaw_mprotect(c3_n pag_n)
{
  if ( 0 != mprotect(_ce_ptr(pag_n), _ce_page, (PROT_READ | PROT_WRITE)) ) {
    fprintf(stderr, "loom: fault mprotect (%u): %s\r\n",
                     pag_n, strerror(errno));
    return 1;
  }

  return 0;
}

#ifdef U3_GUARD_PAGE
/* _ce_ward_protect(): protect the guard page.
*/
static inline c3_i
_ce_ward_protect(void)
{
  if ( 0 != mprotect(_ce_ptr(u3P.gar_n), _ce_page, PROT_NONE) ) {
    fprintf(stderr, "loom: failed to protect guard page (%u): %s\r\n",
                    u3P.gar_n, strerror(errno));
    return 1;
  }

  return 0;
}

/* _ce_ward_post(): set the guard page.
*/
static inline c3_i
_ce_ward_post(c3_n nop_n, c3_n sop_n)
{
  u3P.gar_n = nop_n + ((sop_n - nop_n) / 2);
  return _ce_ward_protect();
}

/* _ce_ward_clip(): hit the guard page.
*/
static inline u3e_flaw
_ce_ward_clip(c3_n nop_n, c3_n sop_n)
{
  c3_n old_n = u3P.gar_n;

  if ( !u3P.gar_n || ((nop_n < u3P.gar_n) && (sop_n > u3P.gar_n)) ) {
    fprintf(stderr, "loom: ward bogus (>%u %u %u<)\r\n",
                    nop_n, u3P.gar_n, sop_n);
    return u3e_flaw_sham;
  }

  if ( sop_n <= (nop_n + 1) ) {
    return u3e_flaw_meme;
  }

  if ( _ce_ward_post(nop_n, sop_n) ) {
    return u3e_flaw_base;
  }

  u3_assert( old_n != u3P.gar_n );

  return u3e_flaw_good;
}
#endif /* ifdef U3_GUARD_PAGE */

/* u3e_fault(): handle a memory fault.
*/
u3e_flaw
u3e_fault(u3_post low_p, u3_post hig_p, u3_post off_p)
{
  c3_n pag_n = off_p >> u3a_page;
  c3_n blk_n = pag_n >> 5;
  c3_w_tmp bit_w = pag_n & 31;

#ifdef U3_GUARD_PAGE
  c3_n gar_n = u3P.gar_n;

  if ( pag_n == gar_n ) {
    u3e_flaw fal_e = _ce_ward_clip(low_p >> u3a_page, hig_p >> u3a_page);

    if ( u3e_flaw_good != fal_e ) {
      return fal_e;
    }

    if ( !(u3P.dit_w[blk_n] & ((c3_w_tmp)1 << bit_w)) ) {
      fprintf(stderr, "loom: strange guard (%d)\r\n", pag_n);
      return u3e_flaw_sham;
    }

    if ( _ce_flaw_mprotect(pag_n) ) {
      return u3e_flaw_base;
    }

    return u3e_flaw_good;
  }
#endif

  if ( u3P.dit_w[blk_n] & ((c3_w_tmp)1 << bit_w) ) {
    fprintf(stderr, "loom: strange page (%d): %x\r\n", pag_n, off_p);
    return u3e_flaw_sham;
  }

  u3P.dit_w[blk_n] |= ((c3_n)1 << bit_w);

  if ( u3P.eph_i ) {
    if ( _ce_flaw_mmap(pag_n) ) {
      return u3e_flaw_base;
    }
  }
  else if ( _ce_flaw_mprotect(pag_n) ) {
    return u3e_flaw_base;
  }

  return u3e_flaw_good;
}

typedef enum {
  _ce_img_good = 0,
  _ce_img_fail = 1,
  _ce_img_size = 2
} _ce_img_stat;

/* _ce_image_stat(): measure image.
*/
static _ce_img_stat
_ce_image_stat(u3e_image* img_u, c3_n* pgs_n)
{
  struct stat buf_u;

  if ( -1 == fstat(img_u->fid_i, &buf_u) ) {
    fprintf(stderr, "loom: stat %s: %s\r\n", img_u->nam_c, strerror(errno));
    u3_assert(0);
    return _ce_img_fail;
  }
  else {
    c3_z siz_z = buf_u.st_size;
    c3_z pgs_z = (siz_z + (_ce_page - 1)) >> (u3a_page + 2);

    if ( !siz_z ) {
      *pgs_n = 0;
      return _ce_img_good;
    }
    else if ( siz_z != _ce_len(pgs_z) ) {
      fprintf(stderr, "loom: %s corrupt size %zu\r\n", img_u->nam_c, siz_z);
      return _ce_img_size;
    }
    else if ( pgs_z > u3e_note_max ) {
      fprintf(stderr, "loom: %s overflow %zu\r\n", img_u->nam_c, siz_z);
      return _ce_img_fail;
    }
    else {
      *pgs_n = (c3_n)pgs_z;
      return _ce_img_good;
    }
  }
}

/* _ce_ephemeral_open(): open or create ephemeral file
*/
static c3_o
_ce_ephemeral_open(c3_i* eph_i)
{
  c3_i mod_i = O_RDWR | O_CREAT;
  c3_c ful_c[8193];

  if ( u3C.eph_c == 0 ) {
    snprintf(ful_c, 8192, "%s", u3P.dir_c);
    c3_mkdir(ful_c, 0700);

    snprintf(ful_c, 8192, "%s/.urb", u3P.dir_c);
    c3_mkdir(ful_c, 0700);

    snprintf(ful_c, 8192, "%s/.urb/chk", u3P.dir_c);
    c3_mkdir(ful_c, 0700);

    snprintf(ful_c, 8192, "%s/.urb/chk/limbo.bin", u3P.dir_c);
    u3C.eph_c = strdup(ful_c);
  }

  if ( -1 == (*eph_i = c3_open(u3C.eph_c, mod_i, 0666)) ) {
    fprintf(stderr, "loom: ephemeral c3_open %s: %s\r\n", u3C.eph_c,
            strerror(errno));
    return c3n;
  }

  if ( ftruncate(*eph_i, _ce_len(u3P.pag_n)) < 0 ) {
    fprintf(stderr, "loom: ephemeral ftruncate %s: %s\r\n", u3C.eph_c,
            strerror(errno));
    return c3n;
  }
  return c3y;
}

/* _ce_image_open(): open or create image.
*/
static _ce_img_stat
_ce_image_open(u3e_image* img_u, c3_c* ful_c)
{
  c3_i mod_i = O_RDWR | O_CREAT;

  c3_c pax_c[8192];
  snprintf(pax_c, 8192, "%s/%s.bin", ful_c, img_u->nam_c);
  if ( -1 == (img_u->fid_i = c3_open(pax_c, mod_i, 0666)) ) {
    fprintf(stderr, "loom: c3_open %s: %s\r\n", pax_c, strerror(errno));
    return _ce_img_fail;
  }

  return _ce_image_stat(img_u, &img_u->pgs_n);
}

/* _ce_patch_write_control(): write control block file.
*/
static void
_ce_patch_write_control(u3_ce_patch* pat_u)
{
  ssize_t ret_i;
  c3_n    len_n = sizeof(u3e_control) +
                  (pat_u->con_u->pgs_n * sizeof(u3e_line));

  if ( len_n != (ret_i = write(pat_u->ctl_i, pat_u->con_u, len_n)) ) {
    if ( 0 < ret_i ) {
      fprintf(stderr, "loom: patch ctl partial write: %zu\r\n", (size_t)ret_i);
    }
    else {
      fprintf(stderr, "loom: patch ctl write: %s\r\n", strerror(errno));
    }
    u3_assert(0);
  }
}

/* _ce_patch_read_control(): read control block file.
*/
static c3_o
_ce_patch_read_control(u3_ce_patch* pat_u)
{
  c3_n len_n;

  u3_assert(0 == pat_u->con_u);
  {
    struct stat buf_u;

    if ( -1 == fstat(pat_u->ctl_i, &buf_u) ) {
      u3_assert(0);
      return c3n;
    }
    len_n = (c3_n) buf_u.st_size;
  }

  if (0 == len_n) {
    return c3n;
  }
  
  pat_u->con_u = c3_malloc(len_n);
  if ( (len_n != read(pat_u->ctl_i, pat_u->con_u, len_n)) ||
        (len_n != sizeof(u3e_control) +
                  (pat_u->con_u->pgs_n * sizeof(u3e_line))) )
  {
    c3_free(pat_u->con_u);
    pat_u->con_u = 0;
    return c3n;
  }
  return c3y;
}

/* _ce_patch_create(): create patch files.
*/
static void
_ce_patch_create(u3_ce_patch* pat_u)
{
  c3_c ful_c[8193];

  snprintf(ful_c, 8192, "%s", u3P.dir_c);
  c3_mkdir(ful_c, 0700);

  snprintf(ful_c, 8192, "%s/.urb", u3P.dir_c);
  c3_mkdir(ful_c, 0700);

  snprintf(ful_c, 8192, "%s/.urb/chk/control.bin", u3P.dir_c);
  if ( -1 == (pat_u->ctl_i = c3_open(ful_c, O_RDWR | O_CREAT | O_EXCL, 0600)) ) {
    fprintf(stderr, "loom: patch c3_open control.bin: %s\r\n", strerror(errno));
    u3_assert(0);
  }

  snprintf(ful_c, 8192, "%s/.urb/chk/memory.bin", u3P.dir_c);
  if ( -1 == (pat_u->mem_i = c3_open(ful_c, O_RDWR | O_CREAT | O_EXCL, 0600)) ) {
    fprintf(stderr, "loom: patch c3_open memory.bin: %s\r\n", strerror(errno));
    u3_assert(0);
  }
}

/* _ce_patch_delete(): delete a patch.
*/
static void
_ce_patch_delete(void)
{
  c3_c ful_c[8193];

  snprintf(ful_c, 8192, "%s/.urb/chk/control.bin", u3P.dir_c);
  if ( unlink(ful_c) ) {
    fprintf(stderr, "loom: failed to delete control.bin: %s\r\n",
                    strerror(errno));
  }

  snprintf(ful_c, 8192, "%s/.urb/chk/memory.bin", u3P.dir_c);
  if ( unlink(ful_c) ) {
    fprintf(stderr, "loom: failed to remove memory.bin: %s\r\n",
                    strerror(errno));
  }
}

/* _ce_patch_verify(): check patch data mug.
*/
static c3_o
_ce_patch_verify(u3_ce_patch* pat_u)
{
  c3_n  pag_n;
  c3_m  mug_m;
  c3_y  buf_y[_ce_page];
  c3_zs ret_zs;
  c3_o  sou_o = c3n;  // south seen

  if ( U3P_VERLAT != pat_u->con_u->ver_w ) {
    fprintf(stderr, "loom: patch version mismatch: have %"PRIc3_w", need %u\r\n",
                    pat_u->con_u->ver_w,
                    U3P_VERLAT);
    return c3n;
  }

  if ( pat_u->con_u->sou_n > 1 ) {
    fprintf(stderr, "loom: patch strange south size: %u\r\n",
                    pat_u->con_u->sou_n);
    return c3n;
  }

  for ( c3_z i_z = 0; i_z < pat_u->con_u->pgs_n; i_z++ ) {
    pag_n = pat_u->con_u->mem_u[i_z].pag_n;
    mug_m = pat_u->con_u->mem_u[i_z].mug_m;

    if ( _ce_page !=
         (ret_zs = pread(pat_u->mem_i, buf_y, _ce_page, _ce_len(i_z))) )
    {
      if ( 0 < ret_zs ) {
        fprintf(stderr, "loom: patch partial read: %"PRIc3_zs"\r\n", ret_zs);
      }
      else {
        fprintf(stderr, "loom: patch read: fail %s\r\n", strerror(errno));
      }
      return c3n;
    }

    {
      c3_m nug_m = _ce_mug_page(buf_y);

      if ( mug_m != nug_m ) {
        fprintf(stderr, "loom: patch mug mismatch"
                        " %"PRIc3_w"/%"PRIc3_z"; (%"PRIxc3_w", %"PRIxc3_w")\r\n",
                        pag_n, i_z, mug_m, nug_m);
        return c3n;
      }
#if 0
      else {
        u3l_log("verify: patch %"PRIc3_w"/%"PRIc3_z", %"PRIxc3_w"\r\n", pag_w, i_z, mug_w);
      }
#endif
    }

    if ( pag_n >= pat_u->con_u->nor_n ) {
      if ( c3n == sou_o ) {
        sou_o = c3y;
      }
      else {
        fprintf(stderr, "loom: patch multiple south pages\r\n");
        return c3n;
      }
    }
  }
  return c3y;
}

/* _ce_patch_free(): free a patch.
*/
static void
_ce_patch_free(u3_ce_patch* pat_u)
{
  c3_free(pat_u->con_u);
  close(pat_u->ctl_i);
  close(pat_u->mem_i);
  c3_free(pat_u);
}

/* _ce_patch_open(): open patch, if any.
*/
static u3_ce_patch*
_ce_patch_open(void)
{
  u3_ce_patch* pat_u;
  c3_c ful_c[8193];
  c3_i ctl_i, mem_i;

  snprintf(ful_c, 8192, "%s", u3P.dir_c);
  c3_mkdir(ful_c, 0700);

  snprintf(ful_c, 8192, "%s/.urb", u3P.dir_c);
  c3_mkdir(ful_c, 0700);

  snprintf(ful_c, 8192, "%s/.urb/chk/control.bin", u3P.dir_c);
  if ( -1 == (ctl_i = c3_open(ful_c, O_RDWR)) ) {
    return 0;
  }

  snprintf(ful_c, 8192, "%s/.urb/chk/memory.bin", u3P.dir_c);
  if ( -1 == (mem_i = c3_open(ful_c, O_RDWR)) ) {
    close(ctl_i);

    _ce_patch_delete();
    return 0;
  }
  pat_u = c3_malloc(sizeof(u3_ce_patch));
  pat_u->ctl_i = ctl_i;
  pat_u->mem_i = mem_i;
  pat_u->con_u = 0;

  if ( c3n == _ce_patch_read_control(pat_u) ) {
    close(pat_u->ctl_i);
    close(pat_u->mem_i);
    c3_free(pat_u);

    _ce_patch_delete();
    return 0;
  }
  if ( c3n == _ce_patch_verify(pat_u) ) {
    _ce_patch_free(pat_u);
    _ce_patch_delete();
    return 0;
  }
  return pat_u;
}

/* _ce_patch_write_page(): write a page of patch memory.
*/
static void
_ce_patch_write_page(u3_ce_patch* pat_u,
                     c3_n         pgc_n,
                     c3_w_tmp*        mem_w)
{
  c3_zs ret_zs;

  if ( _ce_page !=
       (ret_zs = pwrite(pat_u->mem_i, mem_w, _ce_page, _ce_len(pgc_n))) )
  {
    if ( 0 < ret_zs ) {
      fprintf(stderr, "loom: patch partial write: %"PRIc3_zs"\r\n", ret_zs);
    }
    else {
      fprintf(stderr, "loom: patch write: fail: %s\r\n", strerror(errno));
    }
    fprintf(stderr, "info: you probably have insufficient disk space");
    u3_assert(0);
  }
}

/* _ce_patch_count_page(): count a page, producing new counter.
*/
static c3_n
_ce_patch_count_page(c3_n pag_n,
                     c3_n pgc_n)
{
  c3_n blk_n = (pag_n >> 5);
  c3_w_tmp bit_w = (pag_n & 31);

  if ( u3P.dit_w[blk_n] & ((c3_w_tmp)1 << bit_w) ) {
    pgc_n += 1;
  }
  return pgc_n;
}

/* _ce_patch_save_page(): save a page, producing new page counter.
*/
static c3_n
_ce_patch_save_page(u3_ce_patch* pat_u,
                    c3_n         pag_n,
                    c3_n         pgc_n)
{
  c3_n  blk_n = (pag_n >> 5);
  c3_w_tmp  bit_w = (pag_n & 31);

  if ( u3P.dit_w[blk_n] & ((c3_w_tmp)1 << bit_w) ) {
    c3_w_tmp* mem_w = _ce_ptr(pag_n);

    pat_u->con_u->mem_u[pgc_n].pag_n = pag_n;
    pat_u->con_u->mem_u[pgc_n].mug_m = _ce_mug_page(mem_w);

#if 0
    fprintf(stderr, "loom: save page %d %x\r\n",
                    pag_w, pat_u->con_u->mem_u[pgc_w].mug_w);
#endif
    _ce_patch_write_page(pat_u, pgc_n, mem_w);

    pgc_n += 1;
  }
  return pgc_n;
}

/* _ce_patch_compose(): make and write current patch.
*/
static u3_ce_patch*
_ce_patch_compose(c3_n nor_n, c3_n sou_n)
{
  c3_n pgs_n = 0;

#ifdef U3_SNAPSHOT_VALIDATION
  u3K.nor_n = nor_n;
  u3K.sou_n = sou_n;
#endif

  /* Count dirty pages.
  */
  {
    c3_n i_n;

    for ( i_n = 0; i_n < nor_n; i_n++ ) {
      pgs_n = _ce_patch_count_page(i_n, pgs_n);
    }
    for ( i_n = 0; i_n < sou_n; i_n++ ) {
      pgs_n = _ce_patch_count_page((u3P.pag_n - (i_n + 1)), pgs_n);
    }
  }

  if ( !pgs_n ) {
    return 0;
  }
  else {
    u3_ce_patch* pat_u = c3_malloc(sizeof(u3_ce_patch));
    c3_n i_n, pgc_n;

    _ce_patch_create(pat_u);
    pat_u->con_u = c3_malloc(sizeof(u3e_control) + (pgs_n * sizeof(u3e_line)));
    pat_u->con_u->ver_w = U3P_VERLAT;
    pgc_n = 0;

    for ( i_n = 0; i_n < nor_n; i_n++ ) {
      pgc_n = _ce_patch_save_page(pat_u, i_n, pgc_n);
    }
    for ( i_n = 0; i_n < sou_n; i_n++ ) {
      pgc_n = _ce_patch_save_page(pat_u, (u3P.pag_n - (i_n + 1)), pgc_n);
    }

    u3_assert( pgc_n == pgs_n );

    pat_u->con_u->nor_n = nor_n;
    pat_u->con_u->sou_n = sou_n;
    pat_u->con_u->pgs_n = pgc_n;

    _ce_patch_write_control(pat_u);
    return pat_u;
  }
}

/* _ce_patch_sync(): make sure patch is synced to disk.
*/
static void
_ce_patch_sync(u3_ce_patch* pat_u)
{
  if ( -1 == c3_sync(pat_u->ctl_i) ) {
    fprintf(stderr, "loom: control file sync failed: %s\r\n",
                    strerror(errno));
    u3_assert(!"loom: control sync");
  }

  if ( -1 == c3_sync(pat_u->mem_i) ) {
    fprintf(stderr, "loom: patch file sync failed: %s\r\n",
                    strerror(errno));
    u3_assert(!"loom: patch sync");
  }
}

/* _ce_image_sync(): make sure image is synced to disk.
*/
static c3_o
_ce_image_sync(u3e_image* img_u)
{
  if ( -1 == c3_sync(img_u->fid_i) ) {
    fprintf(stderr, "loom: image (%s) sync failed: %s\r\n",
                    img_u->nam_c, strerror(errno));
    return c3n;
  }

  return c3y;
}

/* _ce_image_resize(): resize image, truncating if it shrunk.
*/
static void
_ce_image_resize(u3e_image* img_u, c3_n pgs_n)
{
  c3_z  off_z = _ce_len(pgs_n);
  off_t off_i = (off_t)off_z;

  if ( img_u->pgs_n > pgs_n ) {
    if ( off_z != (size_t)off_i ) {
      fprintf(stderr, "loom: image (%s) truncate: "
                      "offset overflow (%" PRId64 ") for page %u\r\n",
                      img_u->nam_c, (c3_ds)off_i, pgs_n);
      u3_assert(0);
    }

    if ( ftruncate(img_u->fid_i, off_i) ) {
      fprintf(stderr, "loom: image (%s) truncate: %s\r\n",
                      img_u->nam_c, strerror(errno));
      u3_assert(0);
    }
  }

  img_u->pgs_n = pgs_n;
}

/* _ce_patch_apply(): apply patch to images.
*/
static void
_ce_patch_apply(u3_ce_patch* pat_u)
{
  c3_zs ret_zs;
  c3_n     i_n;

  //  resize images
  //
  _ce_image_resize(&u3P.nor_u, pat_u->con_u->nor_n);
  _ce_image_resize(&u3P.sou_u, pat_u->con_u->sou_n);

  //  seek to begining of patch
  //
  if ( -1 == lseek(pat_u->mem_i, 0, SEEK_SET) ) {
    fprintf(stderr, "loom: patch apply seek: %s\r\n", strerror(errno));
    u3_assert(0);
  }

  //  write patch pages into the appropriate image
  //
  for ( i_n = 0; i_n < pat_u->con_u->pgs_n; i_n++ ) {
    c3_n pag_n = pat_u->con_u->mem_u[i_n].pag_n;
    c3_y buf_y[_ce_page];
    c3_i fid_i;
    c3_z off_z;

    if ( pag_n < pat_u->con_u->nor_n ) {
      fid_i = u3P.nor_u.fid_i;
      off_z = _ce_len(pag_n);
    }
    //  NB: this assumes that there never more than one south page,
    //  as enforced by _ce_patch_verify()
    //
    else {
      fid_i = u3P.sou_u.fid_i;
      off_z = 0;
    }

    if ( _ce_page != (ret_zs = read(pat_u->mem_i, buf_y, _ce_page)) ) {
      if ( 0 < ret_zs ) {
        fprintf(stderr, "loom: patch apply partial read: %"PRIc3_zs"\r\n",
                        ret_zs);
      }
      else {
        fprintf(stderr, "loom: patch apply read: %s\r\n", strerror(errno));
      }
      u3_assert(0);
    }
    else {
      if ( _ce_page !=
           (ret_zs = pwrite(fid_i, buf_y, _ce_page, off_z)) )
      {
        if ( 0 < ret_zs ) {
          fprintf(stderr, "loom: patch apply partial write: %"PRIc3_zs"\r\n",
                          ret_zs);
        }
        else {
          fprintf(stderr, "loom: patch apply write: %s\r\n", strerror(errno));
        }
        fprintf(stderr, "info: you probably have insufficient disk space");
        u3_assert(0);
      }
    }
#if 0
    u3l_log("apply: %d, %x", pag_n, _ce_mug_page(buf_y));
#endif
  }
}

/* _ce_loom_track_sane(): quiescent page state invariants.
*/
static c3_o
_ce_loom_track_sane(void)
{
  c3_n blk_n, max_n, i_n = 0;
  c3_w_tmp bit_w;
  c3_o san_o = c3y;

  max_n = u3P.nor_u.pgs_n;

  for ( ; i_n < max_n; i_n++ ) {
    blk_n = i_n >> 5;
    bit_w = i_n & 31;

    if ( u3P.dit_w[blk_n] & ((c3_w_tmp)1 << bit_w) ) {
      fprintf(stderr, "loom: insane north %u\r\n", i_n);
      san_o = c3n;
    }
  }

  max_n = u3P.pag_n - u3P.sou_u.pgs_n;

  for ( ; i_n < max_n; i_n++ ) {
    blk_n = i_n >> 5;
    bit_w = i_n & 31;

    if ( !(u3P.dit_w[blk_n] & ((c3_w_tmp)1 << bit_w)) ) {
      fprintf(stderr, "loom: insane open %u\r\n", i_n);
      san_o = c3n;
    }
  }

  max_n = u3P.pag_n;

  for ( ; i_n < max_n; i_n++ ) {
    blk_n = i_n >> 5;
    bit_w = i_n & 31;

    if ( u3P.dit_w[blk_n] & ((c3_w_tmp)1 << bit_w) ) {
      fprintf(stderr, "loom: insane south %u\r\n", i_n);
      san_o = c3n;
    }
  }

  return san_o;
}

/* _ce_loom_track_north(): [pgs_n] clean, followed by [dif_n] dirty.
*/
void
_ce_loom_track_north(c3_n pgs_n, c3_n dif_n)
{
  c3_n blk_n, i_n = 0, max_n = pgs_n;
  c3_w_tmp bit_w;

  for ( ; i_n < max_n; i_n++ ) {
    blk_n = i_n >> 5;
    bit_w = i_n & 31;
    u3P.dit_w[blk_n] &= ~((c3_w_tmp)1 << bit_w);
  }

  max_n += dif_n;

  for ( ; i_n < max_n; i_n++ ) {
    blk_n = i_n >> 5;
    bit_w = i_n & 31;
    u3P.dit_w[blk_n] |= ((c3_w_tmp)1 << bit_w);
  }
}

/* _ce_loom_track_south(): [pgs_w] clean, preceded by [dif_w] dirty.
*/
void
_ce_loom_track_south(c3_n pgs_n, c3_n dif_n)
{
  c3_n blk_n, i_n = u3P.pag_n - 1, max_n = u3P.pag_n - pgs_n;
  c3_w_tmp bit_w;

  for ( ; i_n >= max_n; i_n-- ) {
    blk_n = i_n >> 5;
    bit_w = i_n & 31;
    u3P.dit_w[blk_n] &= ~((c3_w_tmp)1 << bit_w);
  }

  max_n -= dif_n;

  for ( ; i_n >= max_n; i_n-- ) {
    blk_n = i_n >> 5;
    bit_w = i_n & 31;
    u3P.dit_w[blk_n] |= ((c3_w_tmp)1 << bit_w);
  }
}

/* _ce_loom_protect_north(): protect/track pages from the bottom of memory.
*/
static void
_ce_loom_protect_north(c3_n pgs_n, c3_n old_n)
{
  c3_n dif_n = 0;

  if ( pgs_n ) {
    if ( 0 != mprotect(_ce_ptr(0), _ce_len(pgs_n), PROT_READ) ) {
      fprintf(stderr, "loom: pure north (%u pages): %s\r\n",
                      pgs_n, strerror(errno));
      u3_assert(0);
    }
  }

  if ( old_n > pgs_n ) {
    dif_n = old_n - pgs_n;

    if ( 0 != mprotect(_ce_ptr(pgs_n),
                       _ce_len(dif_n),
                       (PROT_READ | PROT_WRITE)) )
    {
      fprintf(stderr, "loom: foul north (%u pages, %u old): %s\r\n",
                      pgs_n, old_n, strerror(errno));
      u3_assert(0);
    }

#ifdef U3_GUARD_PAGE
    //  protect guard page if clobbered
    //
    //    NB: < pgs_w is precluded by assertion in u3e_save()
    //
    if ( u3P.gar_n < old_n ) {
      fprintf(stderr, "loom: guard on reprotect\r\n");
      u3_assert( !_ce_ward_protect() );
    }
#endif
  }

  _ce_loom_track_north(pgs_n, dif_n);
}

/* _ce_loom_protect_south(): protect/track pages from the top of memory.
*/
static void
_ce_loom_protect_south(c3_n pgs_n, c3_n old_n)
{
  c3_n dif_n = 0;

  if ( pgs_n ) {
    if ( 0 != mprotect(_ce_ptr(u3P.pag_n - pgs_n),
                       _ce_len(pgs_n),
                       PROT_READ) )
    {
      fprintf(stderr, "loom: pure south (%u pages): %s\r\n",
                      pgs_n, strerror(errno));
      u3_assert(0);
    }
  }

  if ( old_n > pgs_n ) {
    c3_n off_n = u3P.pag_n - old_n;
    dif_n = old_n - pgs_n;

    if ( 0 != mprotect(_ce_ptr(off_n),
                       _ce_len(dif_n),
                       (PROT_READ | PROT_WRITE)) )
    {
      fprintf(stderr, "loom: foul south (%u pages, %u old): %s\r\n",
                      pgs_n, old_n, strerror(errno));
      u3_assert(0);
    }

#ifdef U3_GUARD_PAGE
    //  protect guard page if clobbered
    //
    //    NB: >= pgs_n is precluded by assertion in u3e_save()
    //
    if ( u3P.gar_n >= off_n ) {
      fprintf(stderr, "loom: guard on reprotect\r\n");
      u3_assert( !_ce_ward_protect() );
    }
#endif
  }

  _ce_loom_track_south(pgs_n, dif_n);
}

/* _ce_loom_mapf_ephemeral(): map entire loom into ephemeral file
*/
static void
_ce_loom_mapf_ephemeral(void)
{
  if ( MAP_FAILED == mmap(_ce_ptr(0),
                          _ce_len(u3P.pag_n),
                          (PROT_READ | PROT_WRITE),
                          (MAP_FIXED | MAP_SHARED),
                          u3P.eph_i, 0) )
  {
    fprintf(stderr, "loom: initial ephemeral mmap failed (%u pages): %s\r\n",
                    u3P.pag_n, strerror(errno));
    u3_assert(0);
  }
}

/* _ce_loom_mapf_north(): map [pgs_n] of [fid_i] into the bottom of memory
**                        (and ephemeralize [old_n - pgs_n] after if needed).
**
**   NB: _ce_loom_mapf_south() is possible, but it would make separate mappings
**       for each page since the south segment is reversed on disk.
**       in practice, the south segment is a single page (and always dirty);
**       a file-backed mapping for it is just not worthwhile.
*/
static void
_ce_loom_mapf_north(c3_i fid_i, c3_n pgs_n, c3_n old_n)
{
  c3_n dif_n = 0;

  if ( pgs_n ) {
    if ( MAP_FAILED == mmap(_ce_ptr(0),
                            _ce_len(pgs_n),
                            PROT_READ,
                            (MAP_FIXED | MAP_PRIVATE),
                            fid_i, 0) )
    {
      fprintf(stderr, "loom: file-backed mmap failed (%u pages): %s\r\n",
                      pgs_n, strerror(errno));
      u3_assert(0);
    }
  }

  if ( old_n > pgs_n ) {
    dif_n = old_n - pgs_n;

    if ( u3C.wag_w & u3o_swap ) {
      if ( MAP_FAILED == mmap(_ce_ptr(pgs_n),
                              _ce_len(dif_n),
                              (PROT_READ | PROT_WRITE),
                              (MAP_FIXED | MAP_SHARED),
                              u3P.eph_i, _ce_len(pgs_n)) )
      {
        fprintf(stderr, "loom: ephemeral mmap failed (%u pages, %u old): %s\r\n",
                        pgs_n, old_n, strerror(errno));
        u3_assert(0);
      }
    }
    else {
      if ( MAP_FAILED == mmap(_ce_ptr(pgs_n),
                              _ce_len(dif_n),
                              (PROT_READ | PROT_WRITE),
                              (MAP_ANON | MAP_FIXED | MAP_PRIVATE),
                              -1, 0) )
      {
        fprintf(stderr, "loom: anonymous mmap failed (%u pages, %u old): %s\r\n",
                        pgs_n, old_n, strerror(errno));
        u3_assert(0);
      }
    }

#ifdef U3_GUARD_PAGE
    //  protect guard page if clobbered
    //
    //    NB: < pgs_n is precluded by assertion in u3e_save()
    //
    if ( u3P.gar_n < old_n ) {
      fprintf(stderr, "loom: guard on remap\r\n");
      u3_assert( !_ce_ward_protect() );
    }
#endif
  }

  _ce_loom_track_north(pgs_n, dif_n);
}

/* _ce_loom_blit_north(): apply pages, in order, from the bottom of memory.
*/
static void
_ce_loom_blit_north(c3_i fid_i, c3_n pgs_n)
{
  c3_n    i_n;
  void* ptr_v;
  c3_zs ret_zs;

  for ( i_n = 0; i_n < pgs_n; i_n++ ) {
    ptr_v = _ce_ptr(i_n);

    if ( _ce_page != (ret_zs = pread(fid_i, ptr_v, _ce_page, _ce_len(i_n))) ) {
      if ( 0 < ret_zs ) {
        fprintf(stderr, "loom: blit north partial read: %"PRIc3_zs"\r\n",
                        ret_zs);
      }
      else {
        fprintf(stderr, "loom: blit north read %s\r\n", strerror(errno));
      }
      u3_assert(0);
    }
  }

  _ce_loom_protect_north(pgs_n, 0);
}

/* _ce_loom_blit_south(): apply pages, reversed, from the top of memory.
*/
static void
_ce_loom_blit_south(c3_i fid_i, c3_n pgs_n)
{
  c3_n    i_n;
  void* ptr_v;
  c3_zs ret_zs;

  for ( i_n = 0; i_n < pgs_n; i_n++ ) {
    ptr_v = _ce_ptr(u3P.pag_n - (i_n + 1));

    if ( _ce_page != (ret_zs = pread(fid_i, ptr_v, _ce_page, _ce_len(i_n))) ) {
      if ( 0 < ret_zs ) {
        fprintf(stderr, "loom: blit south partial read: %"PRIc3_zs"\r\n",
                        ret_zs);
      }
      else {
        fprintf(stderr, "loom: blit south read: %s\r\n", strerror(errno));
      }
      u3_assert(0);
    }
  }

  _ce_loom_protect_south(pgs_n, 0);
}

#ifdef U3_SNAPSHOT_VALIDATION
/* _ce_page_fine(): compare page in memory and on disk.
*/
static c3_o
_ce_page_fine(u3e_image* img_u, c3_n pag_n, c3_z off_z)
{
  ssize_t ret_i;
  c3_y    buf_y[_ce_page];

  if ( _ce_page !=
       (ret_i = pread(img_u->fid_i, buf_y, _ce_page, off_z)) )
  {
    if ( 0 < ret_i ) {
      fprintf(stderr, "loom: image (%s) fine partial read: %zu\r\n",
                      img_u->nam_c, (size_t)ret_i);
    }
    else {
      fprintf(stderr, "loom: image (%s) fine read: %s\r\n",
                      img_u->nam_c, strerror(errno));
    }
    u3_assert(0);
  }

  {
    c3_m mug_m = _ce_mug_page(_ce_ptr(pag_n));
    c3_m fug_m = _ce_mug_page(buf_y);

    if ( mug_m != fug_m ) {
      fprintf(stderr, "loom: image (%s) mismatch: "
                      "page %d, mem_w %x, fil_w %x, K %x\r\n",
                      img_u->nam_c, pag_n, mug_m, fug_m, u3K.mug_m[pag_n]);
      return c3n;
    }
  }

  return c3y;
}

/* _ce_loom_fine(): compare clean pages in memory and on disk.
*/
static c3_o
_ce_loom_fine(void)
{
  c3_n blk_n, pag_n, i_n;
  c3_w_tmp bit_w;
  c3_o fin_o = c3y;

  for ( i_n = 0; i_n < u3P.nor_u.pgs_n; i_n++ ) {
    pag_n = i_n;
    blk_n = pag_n >> 5;
    bit_w = pag_n & 31;

    if ( !(u3P.dit_w[blk_n] & ((c3_w_tmp)1 << bit_w)) ) {
      fin_o = c3a(fin_o, _ce_page_fine(&u3P.nor_u, pag_n, _ce_len(pag_n)));
    }
  }

  for ( i_n = 0; i_n < u3P.sou_u.pgs_n; i_n++ ) {
    pag_n = u3P.pag_n - (i_n + 1);
    blk_n = pag_n >> 5;
    bit_w = pag_n & 31;

    if ( !(u3P.dit_w[blk_n] & ((c3_w_tmp)1 << bit_w)) ) {
      fin_o = c3a(fin_o, _ce_page_fine(&u3P.sou_u, pag_n, _ce_len(i_n)));
    }
  }

  return fin_o;
}
#endif

/* _ce_image_copy(): copy all of [fom_u] to [tou_u]
*/
static c3_o
_ce_image_copy(u3e_image* fom_u, u3e_image* tou_u)
{
  ssize_t ret_i;
  c3_n      i_n;

  //  resize images
  //
  _ce_image_resize(tou_u, fom_u->pgs_n);

  //  seek to begining of patch and images
  //
  if (  (-1 == lseek(fom_u->fid_i, 0, SEEK_SET))
     || (-1 == lseek(tou_u->fid_i, 0, SEEK_SET)) )
  {
    fprintf(stderr, "loom: image (%s) copy seek: %s\r\n",
                    fom_u->nam_c,
                    strerror(errno));
    return c3n;
  }

  //  copy pages into destination image
  //
  for ( i_n = 0; i_n < fom_u->pgs_n; i_n++ ) {
    c3_y buf_y[_ce_page];
    c3_n off_n = i_n;

    if ( _ce_page != (ret_i = read(fom_u->fid_i, buf_y, _ce_page)) ) {
      if ( 0 < ret_i ) {
        fprintf(stderr, "loom: image (%s) copy partial read: %zu\r\n",
                        fom_u->nam_c, (size_t)ret_i);
      }
      else {
        fprintf(stderr, "loom: image (%s) copy read: %s\r\n",
                        fom_u->nam_c, strerror(errno));
      }
      return c3n;
    }
    else {
      if ( -1 == lseek(tou_u->fid_i, _ce_len(off_n), SEEK_SET) ) {
        fprintf(stderr, "loom: image (%s) copy seek: %s\r\n",
                        tou_u->nam_c, strerror(errno));
        return c3n;
      }
      if ( _ce_page != (ret_i = write(tou_u->fid_i, buf_y, _ce_page)) ) {
        if ( 0 < ret_i ) {
          fprintf(stderr, "loom: image (%s) copy partial write: %zu\r\n",
                          tou_u->nam_c, (size_t)ret_i);
        }
        else {
          fprintf(stderr, "loom: image (%s) copy write: %s\r\n",
                          tou_u->nam_c, strerror(errno));
        }
        fprintf(stderr, "info: you probably have insufficient disk space");
        return c3n;
      }
    }
  }

  return c3y;
}

/* u3e_backup(): copy snapshot from [pux_c] to [pax_c],
 * overwriting optionally. note that image files must
 * be named "north" and "south".
*/
c3_o
u3e_backup(c3_c* pux_c, c3_c* pax_c, c3_o ovw_o)
{
  //  source image files from [pux_c]
  u3e_image nux_u = { .nam_c = "north", .pgs_n = 0 };
  u3e_image sux_u = { .nam_c = "south", .pgs_n = 0 };

  //  destination image files to [pax_c]
  u3e_image nax_u = { .nam_c = "north", .pgs_n = 0 };
  u3e_image sax_u = { .nam_c = "south", .pgs_n = 0 };

  c3_i mod_i = O_RDWR | O_CREAT;

  if ( !pux_c || !pax_c ) {
    fprintf(stderr, "loom: image backup: bad path\r\n");
    return c3n;
  }

  if ( (c3n == ovw_o) && c3_mkdir(pax_c, 0700) ) {
    if ( EEXIST != errno ) {
      fprintf(stderr, "loom: image backup: %s\r\n", strerror(errno));
    }
    return c3n;
  }

  //  open source image files if they exist
  //
  c3_c nux_c[8193];
  snprintf(nux_c, 8192, "%s/%s.bin", pux_c, nux_u.nam_c);
  if (  (0 != access(nux_c, F_OK))
     || (_ce_img_good != _ce_image_open(&nux_u, pux_c)) )
  {
    fprintf(stderr, "loom: couldn't open north image at %s\r\n", pux_c);
    return c3n;
  }

  c3_c sux_c[8193];
  snprintf(sux_c, 8192, "%s/%s.bin", pux_c, sux_u.nam_c);
  if (  (0 != access(sux_c, F_OK))
     || (_ce_img_good != _ce_image_open(&sux_u, pux_c)) )
  {
    fprintf(stderr, "loom: couldn't open south image at %s\r\n", pux_c);
    return c3n;
  }

  //  open destination image files
  c3_c nax_c[8193];
  snprintf(nax_c, 8192, "%s/%s.bin", pax_c, nax_u.nam_c);
  if ( -1 == (nax_u.fid_i = c3_open(nax_c, mod_i, 0666)) ) {
    fprintf(stderr, "loom: c3_open %s: %s\r\n", nax_c, strerror(errno));
    return c3n;
  }
  c3_c sax_c[8193];
  snprintf(sax_c, 8192, "%s/%s.bin", pax_c, sax_u.nam_c);
  if ( -1 == (sax_u.fid_i = c3_open(sax_c, mod_i, 0666)) ) {
    fprintf(stderr, "loom: c3_open %s: %s\r\n", sax_c, strerror(errno));
    return c3n;
  }

  if (  (c3n == _ce_image_copy(&nux_u, &nax_u))
     || (c3n == _ce_image_copy(&sux_u, &sax_u))
     || (c3n == _ce_image_sync(&nax_u))
     || (c3n == _ce_image_sync(&sax_u)) )
  {
    c3_unlink(nax_c);
    c3_unlink(sax_c);
    fprintf(stderr, "loom: image backup failed\r\n");
    return c3n;
  }

  close(nax_u.fid_i);
  close(sax_u.fid_i);
  fprintf(stderr, "loom: image backup complete\r\n");
  return c3y;
}

/*
  u3e_save(): save current changes.

  If we are in dry-run mode, do nothing.

  First, call `_ce_patch_compose` to write all dirty pages to disk and
  clear protection and dirty bits. If there were no dirty pages to write,
  then we're done.

  - Sync the patch files to disk.
  - Verify the patch (because why not?)
  - Write the patch data into the image file (This is idempotent.).
  - Sync the image file.
  - Delete the patchfile and free it.

  Once we've written the dirty pages to disk (and have reset their dirty bits
  and protection flags), we *could* handle the rest of the checkpointing
  process in a separate thread, but we'd need to wait until that finishes
  before we try to make another snapshot.
*/
void
u3e_save(u3_post low_p, u3_post hig_p)
{
  u3_ce_patch* pat_u;
  c3_n nod_n = u3P.nor_u.pgs_n;
  c3_n sod_n = u3P.sou_u.pgs_n;

  if ( u3C.wag_w & u3o_dryrun ) {
    return;
  }

  {
    c3_n nop_n = (low_p >> u3a_page);
    c3_n nor_n = (low_p + (_ce_len_words(1) - 1)) >> u3a_page;
    c3_n sop_n = hig_p >> u3a_page;

    u3_assert( (u3P.gar_n > nop_n) && (u3P.gar_n < sop_n) );

    if ( !(pat_u = _ce_patch_compose(nor_n, u3P.pag_n - sop_n)) ) {
      return;
    }
  }

  //  attempt to avoid propagating anything insane to disk
  //
  u3a_loom_sane();

  if ( u3C.wag_w & u3o_verbose ) {
    u3a_print_memory(stderr, "sync: save", pat_u->con_u->pgs_n << u3a_page);
  }

  _ce_patch_sync(pat_u);

  if ( c3n == _ce_patch_verify(pat_u) ) {
    u3_assert(!"loom: save failed");
  }

#ifdef U3_SNAPSHOT_VALIDATION
  //  check that clean pages are correct
  //
  u3_assert( c3y == _ce_loom_fine() );
#endif

  _ce_patch_apply(pat_u);

  u3_assert( c3y == _ce_image_sync(&u3P.nor_u) );
  u3_assert( c3y == _ce_image_sync(&u3P.sou_u) );

  _ce_patch_free(pat_u);
  _ce_patch_delete();

#ifdef U3_SNAPSHOT_VALIDATION
  {
    c3_n pgs_n;
    u3_assert( _ce_img_good == _ce_image_stat(&u3P.nor_u, &pgs_n) );
    u3_assert( pgs_n == u3P.nor_u.pgs_n );
    u3_assert( _ce_img_good == _ce_image_stat(&u3P.sou_u, &pgs_n) );
    u3_assert( pgs_n == u3P.sou_u.pgs_n );
  }
#endif

  _ce_loom_protect_south(u3P.sou_u.pgs_n, sod_n);

#ifdef U3_SNAPSHOT_VALIDATION
  //  check that all pages in the north/south segments are clean,
  //  all between are dirty, and clean pages are *fine*
  //
  //    since total finery requires total cleanliness,
  //    pages of the north segment are protected twice.
  //
  _ce_loom_protect_north(u3P.nor_u.pgs_n, nod_n);

  u3_assert( c3y == _ce_loom_track_sane() );
  u3_assert( c3y == _ce_loom_fine() );
#endif

  if ( u3C.wag_w & u3o_no_demand ) {
#ifndef U3_SNAPSHOT_VALIDATION
    _ce_loom_protect_north(u3P.nor_u.pgs_n, nod_n);
#endif
  }
  else {
    _ce_loom_mapf_north(u3P.nor_u.fid_i, u3P.nor_u.pgs_n, nod_n);
  }

  u3e_toss(low_p, hig_p);
}

/* _ce_toss_pages(): discard ephemeral pages.
*/
static void
_ce_toss_pages(c3_n nor_n, c3_n sou_n)
{
  c3_n  pgs_n = u3P.pag_n - (nor_n + sou_n);
  void* ptr_v = _ce_ptr(nor_n);

  if ( -1 == madvise(ptr_v, _ce_len(pgs_n), MADV_DONTNEED) ) {
      fprintf(stderr, "loom: madv_dontneed failed (%u pages at %u): %s\r\n",
                      pgs_n, nor_n, strerror(errno));
  }
}

/* u3e_toss(): discard ephemeral pages.
*/
void
u3e_toss(u3_post low_p, u3_post hig_p)
{
  c3_n nor_n = (low_p + (_ce_len_words(1) - 1)) >> u3a_page;
  c3_n sou_n = u3P.pag_n - (hig_p >> u3a_page);

  _ce_toss_pages(nor_n, sou_n);
}

/* u3e_live(): start the checkpointing system.
*/
c3_o
u3e_live(c3_o nuu_o, c3_c* dir_c)
{
  //  require that our page size is a multiple of the system page size.
  //
  {
    size_t sys_i = sysconf(_SC_PAGESIZE);

    if ( _ce_page % sys_i ) {
      fprintf(stderr, "loom: incompatible system page size (%zuKB)\r\n",
                      sys_i >> 10);
      exit(1);
    }
  }

  u3P.dir_c = dir_c;
  u3P.eph_i = 0;
  u3P.nor_u.nam_c = "north";
  u3P.sou_u.nam_c = "south";
  u3P.pag_n = u3C.wor_i >> u3a_page;

  //  XX review dryrun requirements, enable or remove
  //
#if 0
  if ( u3C.wag_w & u3o_dryrun ) {
    return c3y;
  } else
#endif
  {
    //  Open the ephemeral space file.
    //
    if ( u3C.wag_w & u3o_swap ) {
      if ( c3n == _ce_ephemeral_open(&u3P.eph_i) ) {
        fprintf(stderr, "boot: failed to load ephemeral file\r\n");
        exit(1);
      }
    }

    //  Open image files.
    //
    c3_c chk_c[8193];
    snprintf(chk_c, 8193, "%s/.urb/chk", u3P.dir_c);

    _ce_img_stat nor_e = _ce_image_open(&u3P.nor_u, chk_c);
    _ce_img_stat sou_e = _ce_image_open(&u3P.sou_u, chk_c);

    if ( (_ce_img_fail == nor_e) || (_ce_img_fail == sou_e) ) {
      fprintf(stderr, "boot: image failed\r\n");
      exit(1);
    }
    else {
      u3_ce_patch* pat_u;
      c3_n nor_n, sou_n;

      /* Load any patch files; apply them to images.
      */
      if ( 0 != (pat_u = _ce_patch_open()) ) {
        _ce_patch_apply(pat_u);
        u3_assert( c3y == _ce_image_sync(&u3P.nor_u) );
        u3_assert( c3y == _ce_image_sync(&u3P.sou_u) );
        _ce_patch_free(pat_u);
        _ce_patch_delete();
      }
      else if ( (_ce_img_size == nor_e) || (_ce_img_size == sou_e) ) {
        fprintf(stderr, "boot: image failed (size)\r\n");
        exit(1);
      }

      nor_n = u3P.nor_u.pgs_n;
      sou_n = u3P.sou_u.pgs_n;

      //  detect snapshots from a larger loom
      //
      if ( (nor_n + sou_n + 1) >= u3P.pag_n ) {
        fprintf(stderr, "boot: snapshot too big for loom\r\n");
        exit(1);
      }

      //  mark all pages dirty (pages in the snapshot will be marked clean)
      //
      u3e_foul();

      /* Write image files to memory; reinstate protection.
      */
      {
        if ( u3C.wag_w & u3o_swap ) {
          _ce_loom_mapf_ephemeral();
        }

        if ( u3C.wag_w & u3o_no_demand ) {
          _ce_loom_blit_north(u3P.nor_u.fid_i, nor_n);
        }
        else {
          _ce_loom_mapf_north(u3P.nor_u.fid_i, nor_n, 0);
        }

        _ce_loom_blit_south(u3P.sou_u.fid_i, sou_n);

        u3l_log("boot: protected loom");
      }

      /* If the images were empty, we are logically booting.
      */
      if ( !nor_n && !sou_n ) {
        u3l_log("live: logical boot");
        nuu_o = c3y;
      }
      else if ( u3C.wag_w & u3o_no_demand ) {
        u3a_print_memory(stderr, "live: loaded", _ce_len_words(nor_n + sou_n));
      }
      else {
        u3a_print_memory(stderr, "live: mapped", nor_n << u3a_page);
        u3a_print_memory(stderr, "live: loaded", sou_n << u3a_page);
      }

#ifdef U3_GUARD_PAGE
      u3_assert( !_ce_ward_post(nor_n, u3P.pag_n - sou_n) );
#endif
    }
  }

  return nuu_o;
}

/* u3e_stop(): gracefully stop the persistence system.
*/
void
u3e_stop(void)
{
  if ( u3P.eph_i ) {
    _ce_toss_pages(u3P.nor_u.pgs_n, u3P.sou_u.pgs_n);
    close(u3P.eph_i);
    unlink(u3C.eph_c);
  }

  close(u3P.sou_u.fid_i);
  close(u3P.sou_u.fid_i);
}

/* u3e_yolo(): disable dirty page tracking, read/write whole loom.
*/
c3_o
u3e_yolo(void)
{
  //  NB: u3e_save() will reinstate protection flags
  //
  if ( 0 != mprotect(_ce_ptr(0),
                     _ce_len(u3P.pag_n),
                     (PROT_READ | PROT_WRITE)) )
  {
    //  XX confirm recoverable errors
    //
    fprintf(stderr, "loom: yolo: %s\r\n", strerror(errno));
    return c3n;
  }

  u3_assert( !_ce_ward_protect() );

  return c3y;
}

/* u3e_foul(): dirty all the pages of the loom.
*/
void
u3e_foul(void)
{
  memset((void*)u3P.dit_w, 0xff, sizeof(u3P.dit_w));
}

/* u3e_init(): initialize guard page tracking, dirty loom
*/
void
u3e_init(void)
{
  u3P.pag_n = u3C.wor_i >> u3a_page;

  u3P.nor_u.fid_i = u3P.sou_u.fid_i = -1;

  u3e_foul();

#ifdef U3_GUARD_PAGE
  u3_assert( !_ce_ward_post(0, u3P.pag_n) );
#endif
}

/* u3e_ward(): reposition guard page if needed.
*/
void
u3e_ward(u3_post low_p, u3_post hig_p)
{
#ifdef U3_GUARD_PAGE
  c3_n nop_n = low_p >> u3a_page;
  c3_n sop_n = hig_p >> u3a_page;
  c3_n pag_n = u3P.gar_n;

  if ( !((pag_n > nop_n) && (pag_n < sop_n)) ) {
    u3_assert( !_ce_ward_post(nop_n, sop_n) );
    u3_assert( !_ce_flaw_mprotect(pag_n) );
    u3_assert( u3P.dit_w[pag_n >> 5] & ((c3_w_tmp)1 << (pag_n & 31)) );
  }
#endif
}
