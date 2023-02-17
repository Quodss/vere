//! @file events.c
//!
//! incremental, orthogonal, paginated loom snapshots
//!
//! ### components
//!
//!   - page: 16KB chunk of the loom.
//!   - north segment (u3e_image, north.bin): low contiguous loom pages,
//!     (in practice, the home road heap). indexed from low to high:
//!     in-order on disk.
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
//!   - snapshot segments are copied onto the loom; all included pages
//!     are marked clean and protected (read-only).
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
//!   - patch files are deleted.
//!
//! ### limitations
//!
//!   - loom page size is fixed (16 KB), and must be a multiple of the
//!     system page size. (can the size vary at runtime give south.bin's
//!     reversed order? alternately, if system page size > ours, the fault
//!     handler could dirty N pages at a time.)
//!   - update atomicity is suspect: patch application must either
//!     completely succeed or leave on-disk segments intact. unapplied
//!     patches can be discarded (triggering event replay), but once
//!     patch application begins it must succeed (can fail if disk is full).
//!     may require integration into the overall signal-handling regime.
//!   - any errors are handled with assertions; failed/partial writes are not
//!     retried.
//!
//! ### enhancements
//!
//!   - use platform specific page fault mechanism (mach rpc, userfaultfd, &c).
//!   - implement demand paging / heuristic page-out.
//!   - add a guard page in the middle of the loom to reactively handle stack overflow.
//!   - parallelism
//!

#include "c3.h"
#include "events.h"

#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>

#include "log.h"
#include "manage.h"
#include "options.h"
#include "retrieve.h"
#include "types.h"

/// Snapshotting system.
u3e_pool u3e_Pool;

//! Urbit page size in 4-byte words.
#define pag_wiz_i  ((size_t)1 << u3a_page)

//! Urbit page size in bytes.
#define pag_siz_i  ((size_t)1 << (u3a_page + 2))

#ifdef U3_SNAPSHOT_VALIDATION
/* Image check.
*/
struct {
  c3_w nor_w;
  c3_w sou_w;
  c3_w mug_w[u3a_pages];
} u3K;

/* _ce_check_page(): checksum page.
*/
static c3_w
_ce_check_page(c3_w pag_w)
{
  c3_w* mem_w = u3_Loom + (pag_w << u3a_page);
  c3_w  mug_w = u3r_mug_words(mem_w, (1 << u3a_page));

  return mug_w;
}

/* u3e_check(): compute a checksum on all memory within the watermarks.
*/
void
u3e_check(c3_c* cap_c)
{
  c3_w nor_w = 0;
  c3_w sou_w = 0;

  {
    c3_w nwr_w, swu_w;

    u3m_water(&nwr_w, &swu_w);

    nor_w = (nwr_w + ((1 << u3a_page) - 1)) >> u3a_page;
    sou_w = (swu_w + ((1 << u3a_page) - 1)) >> u3a_page;
  }

  /* Count dirty pages.
  */
  {
    c3_w i_w, sum_w, mug_w;

    sum_w = 0;
    for ( i_w = 0; i_w < nor_w; i_w++ ) {
      mug_w = _ce_check_page(i_w);
      if ( strcmp(cap_c, "boot") ) {
        c3_assert(mug_w == u3K.mug_w[i_w]);
      }
      sum_w += mug_w;
    }
    for ( i_w = 0; i_w < sou_w; i_w++ ) {
      mug_w = _ce_check_page((u3P.pag_w - (i_w + 1)));
      if ( strcmp(cap_c, "boot") ) {
        c3_assert(mug_w == u3K.mug_w[(u3P.pag_w - (i_w + 1))]);
      }
      sum_w += mug_w;
    }
    u3l_log("%s: sum %x (%x, %x)", cap_c, sum_w, nor_w, sou_w);
  }
}
#endif

/* _ce_flaw_protect(): protect page after fault.
*/
static inline c3_i
_ce_flaw_protect(c3_w pag_w)
{
  if ( 0 != mprotect((void *)(u3_Loom + (pag_w << u3a_page)),
                     pag_siz_i,
                     (PROT_READ | PROT_WRITE)) )
  {
    fprintf(stderr, "loom: fault mprotect (%u): %s\r\n",
                     pag_w, strerror(errno));
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
  if ( 0 != mprotect((void *)(u3_Loom + (u3P.gar_w << u3a_page)),
                      pag_siz_i,
                      PROT_NONE) )
  {
    fprintf(stderr, "loom: failed to protect guard page (%u): %s\r\n",
                    u3P.gar_w, strerror(errno));
    return 1;
  }

  return 0;
}

/* _ce_ward_post(): set the guard page.
*/
static inline c3_i
_ce_ward_post(c3_w nop_w, c3_w sop_w)
{
  u3P.gar_w = nop_w + ((sop_w - nop_w) / 2);
  return _ce_ward_protect();
}

/* _ce_ward_clip(): hit the guard page.
*/
static inline u3e_flaw
_ce_ward_clip(c3_w nop_w, c3_w sop_w)
{
  c3_w old_w = u3P.gar_w;

  if ( !u3P.gar_w || ((nop_w < u3P.gar_w) && (sop_w > u3P.gar_w)) ) {
    fprintf(stderr, "loom: ward bogus (>%u %u %u<)\r\n",
                    nop_w, u3P.gar_w, sop_w);
    return u3e_flaw_sham;
  }

  if ( sop_w <= (nop_w + 1) ) {
    return u3e_flaw_meme;
  }

  if ( _ce_ward_post(nop_w, sop_w) ) {
    return u3e_flaw_base;
  }

  c3_assert( old_w != u3P.gar_w );

  return u3e_flaw_good;
}
#endif /* ifdef U3_GUARD_PAGE */

u3e_flaw
u3e_fault(u3_post low_p, u3_post hig_p, u3_post off_p)
{
  c3_w pag_w = off_p >> u3a_page;
  c3_w blk_w = pag_w >> 5;
  c3_w bit_w = pag_w & 31;

#ifdef U3_GUARD_PAGE
  if ( pag_w == u3P.gar_w ) {
    u3e_flaw fal_e = _ce_ward_clip(low_p >> u3a_page, hig_p >> u3a_page);

    if ( u3e_flaw_good != fal_e ) {
      return fal_e;
    }

    if ( !(u3P.dit_w[blk_w] & (1 << bit_w)) ) {
      fprintf(stderr, "loom: strange guard (%d)\r\n", pag_w);
      return u3e_flaw_sham;
    }
  }
  else
#endif
  if ( u3P.dit_w[blk_w] & (1 << bit_w) ) {
    fprintf(stderr, "loom: strange page (%d): %x\r\n", pag_w, off_p);
    return u3e_flaw_sham;
  }

  u3P.dit_w[blk_w] |= (1 << bit_w);

  if ( _ce_flaw_protect(pag_w) ) {
    return u3e_flaw_base;
  }

  return u3e_flaw_good;
}

/* _ce_image_open(): open or create image.
*/
static c3_o
_ce_image_open(u3e_image* img_u)
{
  c3_i mod_i = O_RDWR | O_CREAT;
  c3_c ful_c[8193];

  snprintf(ful_c, 8192, "%s/%s.bin", u3P.dir_c, img_u->nam_c);
  if ( -1 == (img_u->fid_i = c3_open(ful_c, mod_i, 0666)) ) {
    fprintf(stderr, "loom: c3_open %s: %s\r\n", ful_c, strerror(errno));
    return c3n;
  }
  else {
    struct stat buf_u;

    if ( -1 == fstat(img_u->fid_i, &buf_u) ) {
      fprintf(stderr, "loom: stat %s: %s\r\n", ful_c, strerror(errno));
      c3_assert(0);
      return c3n;
    }
    else {
      c3_d siz_d = buf_u.st_size;
      c3_d pgs_d = (siz_d + (c3_d)(pag_siz_i - 1)) >>
                   (c3_d)(u3a_page + 2);

      if ( !siz_d ) {
        return c3y;
      }
      else {
        if ( siz_d != (pgs_d << (c3_d)(u3a_page + 2)) ) {
          fprintf(stderr, "%s: corrupt size %" PRIx64 "\r\n", ful_c, siz_d);
          return c3n;
        }
        img_u->pgs_w = (c3_w) pgs_d;
        c3_assert(pgs_d == (c3_d)img_u->pgs_w);

        return c3y;
      }
    }
  }
}

/* _ce_patch_write_control(): write control block file.
*/
static void
_ce_patch_write_control(u3_ce_patch* pat_u)
{
  ssize_t ret_i;
  c3_w    len_w = sizeof(u3e_control) +
                  (pat_u->con_u->pgs_w * sizeof(u3e_line));

  if ( len_w != (ret_i = write(pat_u->ctl_i, pat_u->con_u, len_w)) ) {
    if ( 0 < ret_i ) {
      fprintf(stderr, "loom: patch ctl partial write: %zu\r\n", (size_t)ret_i);
    }
    else {
      fprintf(stderr, "loom: patch ctl write: %s\r\n", strerror(errno));
    }
    c3_assert(0);
  }
}

/* _ce_patch_read_control(): read control block file.
*/
static c3_o
_ce_patch_read_control(u3_ce_patch* pat_u)
{
  c3_w len_w;

  c3_assert(0 == pat_u->con_u);
  {
    struct stat buf_u;

    if ( -1 == fstat(pat_u->ctl_i, &buf_u) ) {
      c3_assert(0);
      return c3n;
    }
    len_w = (c3_w) buf_u.st_size;
  }

  pat_u->con_u = c3_malloc(len_w);
  if ( (len_w != read(pat_u->ctl_i, pat_u->con_u, len_w)) ||
        (len_w != sizeof(u3e_control) +
                  (pat_u->con_u->pgs_w * sizeof(u3e_line))) )
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

  snprintf(ful_c, 8192, "%s/control.bin", u3P.dir_c);
  if ( -1 == (pat_u->ctl_i = c3_open(ful_c, O_RDWR | O_CREAT | O_EXCL, 0600)) ) {
    fprintf(stderr, "loom: patch c3_open control.bin: %s\r\n", strerror(errno));
    c3_assert(0);
  }

  snprintf(ful_c, 8192, "%s/memory.bin", u3P.dir_c);
  if ( -1 == (pat_u->mem_i = c3_open(ful_c, O_RDWR | O_CREAT | O_EXCL, 0600)) ) {
    fprintf(stderr, "loom: patch c3_open memory.bin: %s\r\n", strerror(errno));
    c3_assert(0);
  }
}

/* _ce_patch_delete(): delete a patch.
*/
static void
_ce_patch_delete(void)
{
  c3_c ful_c[8193];

  snprintf(ful_c, 8192, "%s/control.bin", u3P.dir_c);
  if ( unlink(ful_c) ) {
    fprintf(stderr, "loom: failed to delete control.bin: %s\r\n",
                    strerror(errno));
  }

  snprintf(ful_c, 8192, "%s/memory.bin", u3P.dir_c);
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
  c3_w i_w, pag_w, mug_w;
  c3_w      mem_w[pag_wiz_i];
  size_t    off_i, siz_i = pag_siz_i;
  ssize_t   ret_i;

  if ( u3e_version != pat_u->con_u->ver_y ) {
    fprintf(stderr, "loom: patch version mismatch: have %u, need %u\r\n",
                    pat_u->con_u->ver_y,
                    u3e_version);
    return c3n;
  }

  for ( i_w = 0; i_w < pat_u->con_u->pgs_w; i_w++ ) {
    pag_w = pat_u->con_u->mem_u[i_w].pag_w;
    mug_w = pat_u->con_u->mem_u[i_w].mug_w;
    off_i = (size_t)i_w << (u3a_page + 2);

    if ( siz_i != (ret_i = c3_pread(pat_u->mem_i, mem_w, siz_i, off_i)) ) {
      if ( 0 < ret_i ) {
        fprintf(stderr, "loom: patch partial read: %zu\r\n", (size_t)ret_i);
      }
      else {
        fprintf(stderr, "loom: patch read fail: %s\r\n", strerror(errno));
      }
      return c3n;
    }
    {
      c3_w nug_w = u3r_mug_words(mem_w, pag_wiz_i);

      if ( mug_w != nug_w ) {
        fprintf(stderr, "loom: patch mug mismatch %d/%d; (%x, %x)\r\n",
                        pag_w, i_w, mug_w, nug_w);
        return c3n;
      }
#if 0
      else {
        u3l_log("verify: patch %d/%d, %x\r\n", pag_w, i_w, mug_w);
      }
#endif
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

  snprintf(ful_c, 8192, "%s/control.bin", u3P.dir_c);
  if ( -1 == (ctl_i = c3_open(ful_c, O_RDWR)) ) {
    return 0;
  }

  snprintf(ful_c, 8192, "%s/memory.bin", u3P.dir_c);
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

/* _ce_patch_count_page(): count a page, producing new counter.
*/
static c3_w
_ce_patch_count_page(c3_w pag_w,
                     c3_w pgc_w)
{
  c3_w blk_w = (pag_w >> 5);
  c3_w bit_w = (pag_w & 31);

  if ( u3P.dit_w[blk_w] & (1 << bit_w) ) {
    pgc_w += 1;
  }
  return pgc_w;
}

/* _ce_patch_save_page(): save a page, producing new page counter.
*/
static c3_w
_ce_patch_save_page(u3_ce_patch* pat_u,
                    c3_w         pag_w,
                    c3_w         pgc_w)
{
  c3_w blk_w = (pag_w >> 5);
  c3_w bit_w = (pag_w & 31);

  if ( u3P.dit_w[blk_w] & (1 << bit_w) ) {
    c3_w*  mem_w = u3_Loom + (pag_w << u3a_page);
    size_t off_i = (size_t)pgc_w << (u3a_page + 2);

    pat_u->con_u->mem_u[pgc_w].pag_w = pag_w;
    pat_u->con_u->mem_u[pgc_w].mug_w = u3r_mug_words(mem_w, pag_wiz_i);

    if ( 0 > c3_pwrite(pat_u->mem_i, mem_w, pag_siz_i, off_i) ) {
      fprintf(stderr, "loom: patch save: %s\r\n", strerror(errno));
      c3_assert(0);
    }

    pgc_w += 1;
  }
  return pgc_w;
}

/* _ce_patch_compose(): make and write current patch.
*/
static u3_ce_patch*
_ce_patch_compose(c3_w nor_w, c3_w sou_w)
{
  c3_w pgs_w = 0;

#ifdef U3_SNAPSHOT_VALIDATION
  u3K.nor_w = nor_w;
  u3K.sou_w = sou_w;
#endif

  /* Count dirty pages.
  */
  {
    c3_w i_w;

    for ( i_w = 0; i_w < nor_w; i_w++ ) {
      pgs_w = _ce_patch_count_page(i_w, pgs_w);
    }
    for ( i_w = 0; i_w < sou_w; i_w++ ) {
      pgs_w = _ce_patch_count_page((u3P.pag_w - (i_w + 1)), pgs_w);
    }
  }

  if ( !pgs_w ) {
    return 0;
  }
  else {
    u3_ce_patch* pat_u = c3_malloc(sizeof(u3_ce_patch));
    c3_w i_w, pgc_w;

    _ce_patch_create(pat_u);
    pat_u->con_u = c3_malloc(sizeof(u3e_control) + (pgs_w * sizeof(u3e_line)));
    pat_u->con_u->ver_y = u3e_version;
    pgc_w = 0;

    for ( i_w = 0; i_w < nor_w; i_w++ ) {
      pgc_w = _ce_patch_save_page(pat_u, i_w, pgc_w);
    }
    for ( i_w = 0; i_w < sou_w; i_w++ ) {
      pgc_w = _ce_patch_save_page(pat_u, (u3P.pag_w - (i_w + 1)), pgc_w);
    }

    pat_u->con_u->nor_w = nor_w;
    pat_u->con_u->sou_w = sou_w;
    pat_u->con_u->pgs_w = pgc_w;

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
    c3_assert(!"loom: control sync");
  }

  if ( -1 == c3_sync(pat_u->mem_i) ) {
    fprintf(stderr, "loom: patch file sync failed: %s\r\n",
                    strerror(errno));
    c3_assert(!"loom: patch sync");
  }
}

/* _ce_image_sync(): make sure image is synced to disk.
*/
static void
_ce_image_sync(u3e_image* img_u)
{
  if ( -1 == c3_sync(img_u->fid_i) ) {
    fprintf(stderr, "loom: image (%s) sync failed: %s\r\n",
                    img_u->nam_c, strerror(errno));
    c3_assert(!"loom: image sync");
  }
}

/* _ce_image_resize(): resize image, truncating if it shrunk.
*/
static void
_ce_image_resize(u3e_image* img_u, c3_w pgs_w)
{
  off_t off_i = (off_t)pgs_w << (u3a_page + 2);

  if ( img_u->pgs_w > pgs_w ) {
    if ( (off_i >> (u3a_page + 2)) != pgs_w ) {
      fprintf(stderr, "loom: image (%s) truncate: "
                      "offset overflow (%" PRId64 ") for page %u\r\n",
                      img_u->nam_c, (c3_ds)off_i, pgs_w);
      c3_assert(0);
    }

    if ( ftruncate(img_u->fid_i, off_i) ) {
      fprintf(stderr, "loom: image (%s) truncate: %s\r\n",
                      img_u->nam_c, strerror(errno));
      c3_assert(0);
    }
  }

  img_u->pgs_w = pgs_w;
}

/* _ce_patch_apply(): apply patch to images.
*/
static void
_ce_patch_apply(u3_ce_patch* pat_u)
{
  c3_w i_w, pag_w, off_w, mem_w[pag_wiz_i];
  c3_i      fid_i;
  size_t    rof_i, wof_i, siz_i = pag_siz_i;
  ssize_t   ret_i;

  //  resize images
  //
  _ce_image_resize(&u3P.nor_u, pat_u->con_u->nor_w);
  _ce_image_resize(&u3P.sou_u, pat_u->con_u->sou_w);

  //  write patch pages into the appropriate image
  //
  for ( i_w = 0; i_w < pat_u->con_u->pgs_w; i_w++ ) {
    pag_w = pat_u->con_u->mem_u[i_w].pag_w;

    if ( pag_w < pat_u->con_u->nor_w ) {
      fid_i = u3P.nor_u.fid_i;
      off_w = pag_w;
    }
    else {
      fid_i = u3P.sou_u.fid_i;
      off_w = (u3P.pag_w - (pag_w + 1));
    }

    rof_i = (size_t)i_w   << (u3a_page + 2);
    wof_i = (size_t)off_w << (u3a_page + 2);

    if ( siz_i != (ret_i = c3_pread(pat_u->mem_i, mem_w, siz_i, rof_i))) {
      if ( 0 < ret_i ) {
        fprintf(stderr, "loom: patch apply partial read: %zu\r\n",
                        (size_t)ret_i);
      }
      else {
        fprintf(stderr, "loom: patch apply read: %s\r\n", strerror(errno));
      }
      c3_assert(0);
    }

    if ( 0 > c3_pwrite(fid_i, mem_w, siz_i, wof_i) ) {
      fprintf(stderr, "loom: patch apply write: %s\r\n", strerror(errno));
      c3_assert(0);
    }
#if 0
    u3l_log("apply: %d, %x\n", pag_w, u3r_mug_words(mem_w, pag_wiz_i));
#endif
  }
}

/* _ce_loom_track_north(): [pgs_w] clean, followed by [dif_w] dirty.
*/
void
_ce_loom_track_north(c3_w pgs_w, c3_w dif_w)
{
  c3_w blk_w = pgs_w >> 5;
  c3_w bit_w = pgs_w & 31;
  c3_w off_w;

  memset((void*)u3P.dit_w, 0, blk_w << 2);

  if ( bit_w ) {
    c3_w tib_w = 32 - bit_w;
    c3_w dat_w = u3P.dit_w[blk_w];

    dat_w   &= 0xffffffff << bit_w;

    if ( dif_w <= tib_w ) {
      dat_w |= ((1 << dif_w) - 1) << bit_w;
      dif_w  = 0;
    }
    else {
      dat_w |= 0xffffffff << bit_w;
      dif_w -= tib_w;
    }

    u3P.dit_w[blk_w] = dat_w;
    blk_w += 1;
  }

  off_w = blk_w;
  blk_w = dif_w >> 5;
  bit_w = dif_w & 31;

  memset((void*)(u3P.dit_w + off_w), 0xff, blk_w << 2);

  if ( bit_w ) {
    u3P.dit_w[off_w + blk_w] |= (1 << bit_w) - 1;
  }
}

/* _ce_loom_track_south(): [pgs_w] clean, preceded by [dif_w] dirty.
*/
void
_ce_loom_track_south(c3_w pgs_w, c3_w dif_w)
{
  c3_w blk_w = pgs_w >> 5;
  c3_w bit_w = pgs_w & 31;
  c3_w bas_w = ((u3P.pag_w - pgs_w) + 31) >> 5;
  c3_w off_w;

  memset((void*)(u3P.dit_w + bas_w), 0, blk_w << 2);

  //  the following index subtractions (bas_w, off) are safe,
  //  so long as the south segment never includes all pages
  //
  if ( bit_w ) {
    c3_w tib_w = 32 - bit_w;
    c3_w dat_w = u3P.dit_w[--bas_w];

    dat_w   &= 0xffffffff >> bit_w;

    if ( dif_w <= tib_w ) {
      dat_w |= ((1 << dif_w) - 1) << (tib_w - dif_w);
      dif_w  = 0;
    }
    else {
      dat_w |= 0xffffffff >> bit_w;
      dif_w -= tib_w;
    }

    u3P.dit_w[bas_w] = dat_w;
  }

  blk_w = dif_w >> 5;
  bit_w = dif_w & 31;
  off_w = bas_w - blk_w;

  memset((void*)(u3P.dit_w + off_w), 0xff, blk_w << 2);

  if ( bit_w ) {
    u3P.dit_w[off_w - 1] |= ((1 << bit_w) - 1) << (32 - bit_w);
  }
}

/* _ce_loom_protect_north(): protect/track pages from the bottom of memory.
*/
static void
_ce_loom_protect_north(c3_w pgs_w, c3_w old_w)
{
  if ( pgs_w ) {
    if ( 0 != mprotect((void*)u3_Loom,
                       (size_t)pgs_w << (u3a_page + 2),
                       PROT_READ) )
    {
      fprintf(stderr, "loom: pure north (%u pages): %s\r\n",
                      pgs_w, strerror(errno));
      c3_assert(0);
    }
  }

  if ( old_w > pgs_w ) {
    c3_w dif_w = old_w - pgs_w;

    if ( 0 != mprotect((void*)(u3_Loom + (pgs_w << u3a_page)),
                       (size_t)dif_w << (u3a_page + 2),
                       (PROT_READ | PROT_WRITE)) )
    {
      fprintf(stderr, "loom: foul north (%u pages, %u old): %s\r\n",
                      pgs_w, old_w, strerror(errno));
      c3_assert(0);
    }

#ifdef U3_GUARD_PAGE
    //  protect guard page if clobbered
    //
    //    NB: < pgs_w is precluded by assertion in u3e_save()
    //
    if ( u3P.gar_w < old_w ) {
      fprintf(stderr, "loom: guard on reprotect\r\n");
      c3_assert( !_ce_ward_protect() );
    }
#endif

    _ce_loom_track_north(pgs_w, dif_w);
  }
  else {
    _ce_loom_track_north(pgs_w, 0);
  }
}

/* _ce_loom_protect_south(): protect/track pages from the top of memory.
*/
static void
_ce_loom_protect_south(c3_w pgs_w, c3_w old_w)
{
  if ( pgs_w ) {
    if ( 0 != mprotect((void*)(u3_Loom + ((u3P.pag_w - pgs_w) << u3a_page)),
                       (size_t)pgs_w << (u3a_page + 2),
                       PROT_READ) )
    {
      fprintf(stderr, "loom: pure south (%u pages): %s\r\n",
                      pgs_w, strerror(errno));
      c3_assert(0);
    }
  }

  if ( old_w > pgs_w ) {
    c3_w dif_w = old_w - pgs_w;
    c3_w off_w = u3P.pag_w - old_w;

    if ( 0 != mprotect((void*)(u3_Loom + (off_w << u3a_page)),
                       (size_t)dif_w << (u3a_page + 2),
                       (PROT_READ | PROT_WRITE)) )
    {
      fprintf(stderr, "loom: foul south (%u pages, %u old): %s\r\n",
                      pgs_w, old_w, strerror(errno));
      c3_assert(0);
    }

#ifdef U3_GUARD_PAGE
    //  protect guard page if clobbered
    //
    //    NB: >= pgs_w is precluded by assertion in u3e_save()
    //
    if ( u3P.gar_w >= off_w ) {
      fprintf(stderr, "loom: guard on reprotect\r\n");
      c3_assert( !_ce_ward_protect() );
    }
#endif

    _ce_loom_track_south(pgs_w, dif_w);
  }
  else {
    _ce_loom_track_south(pgs_w, 0);
  }
}

/* _ce_loom_mapf_north(): map [pgs_w] of [fid_i] into the bottom of memory
**                        (and anonymize [old_w - pgs_w] after if needed).
**
**   NB: _ce_loom_mapf_south() is possible, but it would make separate mappings
**       for each page since the south segment is reversed on disk.
**       in practice, the south segment is a single page (and always dirty);
**       a file-backed mapping for it is just not worthwhile.
*/
static void
_ce_loom_mapf_north(c3_i fid_i, c3_w pgs_w, c3_w old_w)
{
  //  XX mingw doesn't support MAP_FIXED clobbering;
  //  will require explicit unmapping and related bookkeeping.
  //
  if ( pgs_w ) {
    if ( MAP_FAILED == mmap((void*)u3_Loom,
                            (size_t)pgs_w << (u3a_page + 2),
                            PROT_READ,
                            (MAP_FIXED | MAP_PRIVATE),
                            fid_i, 0) )
    {
      fprintf(stderr, "loom: file-backed mmap failed (%u pages): %s\r\n",
                      pgs_w, strerror(errno));
      c3_assert(0);
    }
  }

  if ( old_w > pgs_w ) {
    c3_w dif_w = old_w - pgs_w;

    if ( MAP_FAILED == mmap((void*)(u3_Loom + (pgs_w << u3a_page)),
                            (size_t)dif_w << (u3a_page + 2),
                            (PROT_READ | PROT_WRITE),
                            (MAP_ANON | MAP_FIXED | MAP_PRIVATE),
                            -1, 0) )
    {
      fprintf(stderr, "loom: anonymous mmap failed (%u pages, %u old): %s\r\n",
                      pgs_w, old_w, strerror(errno));
      c3_assert(0);
    }

#ifdef U3_GUARD_PAGE
    //  protect guard page if clobbered
    //
    //    NB: < pgs_w is precluded by assertion in u3e_save()
    //
    if ( u3P.gar_w < old_w ) {
      fprintf(stderr, "loom: guard on remap\r\n");
      c3_assert( !_ce_ward_protect() );
    }
#endif

    _ce_loom_track_north(pgs_w, dif_w);
  }
  else {
    _ce_loom_track_north(pgs_w, 0);
  }
}

/* _ce_loom_blit_north(): apply pages, in order, from the bottom of memory.
*/
static void
_ce_loom_blit_north(c3_i fid_i, c3_w pgs_w)
{
  size_t  len_i = (size_t)pgs_w << (u3a_page + 2);
  ssize_t ret_i;

  if ( pgs_w ) {
    if ( len_i != (ret_i = c3_pread(fid_i, u3_Loom, len_i, 0)) ) {
      if ( 0 < ret_i ) {
        fprintf(stderr, "loom: blit north partial read: %zu\r\n",
                        (size_t)ret_i);
      }
      else {
        fprintf(stderr, "loom: blit north read: %s\r\n", strerror(errno));
      }
      c3_assert(0);
    }
  }

  _ce_loom_protect_north(pgs_w, 0);
}

/* _ce_loom_blit_south(): apply pages, reversed, from the top of memory.
*/
static void
_ce_loom_blit_south(c3_i fid_i, c3_w pgs_w)
{
  c3_w      i_w;
  c3_w*   ptr_w;
  size_t  off_i;
  ssize_t ret_i;

  for ( i_w = 0; i_w < pgs_w; i_w++ ) {
    off_i = (size_t)i_w << (u3a_page + 2);
    ptr_w = u3_Loom + ((u3P.pag_w - (i_w + 1)) << u3a_page);

    if ( pag_siz_i != (ret_i = c3_pread(fid_i, ptr_w, pag_siz_i, off_i)) ) {
      if ( 0 < ret_i ) {
        fprintf(stderr, "loom: blit south partial read: %zu\r\n",
                        (size_t)ret_i);
      }
      else {
        fprintf(stderr, "loom: blit south read: %s\r\n", strerror(errno));
      }
      c3_assert(0);
    }
  }

  _ce_loom_protect_south(pgs_w, 0);
}

#ifdef U3_SNAPSHOT_VALIDATION
/* _ce_image_fine(): compare image to memory.
*/
static void
_ce_image_fine(u3e_image* img_u,
               c3_w*      ptr_w,
               c3_ws     stp_ws)
{
  c3_w i_w, mem_w, fil_w;
  c3_w      buf_w[pag_wiz_i];
  size_t    off_i, siz_i = pag_siz_i;
  ssize_t   ret_i;

  for ( i_w=0; i_w < img_u->pgs_w; i_w++ ) {
    off_i = (size_t)i_w << (u3a_page + 2);

    if ( siz_i != (ret_i = c3_pread(img_u->fid_i, buf_w, siz_i, off_i)) ) {
      if ( 0 < ret_i ) {
        fprintf(stderr, "loom: image (%s) fine partial read: %zu\r\n",
                        img_u->nam_c, (size_t)ret_i);
      }
      else {
        fprintf(stderr, "loom: image (%s) fine read: %s\r\n",
                        img_u->nam_c, strerror(errno));
      }
      c3_assert(0);
    }

    mem_w = u3r_mug_words(ptr_w, pag_wiz_i);
    fil_w = u3r_mug_words(buf_w, pag_wiz_i);

    if ( mem_w != fil_w ) {
      c3_w pag_w = (ptr_w - u3_Loom) >> u3a_page;

      fprintf(stderr, "loom: image (%s) mismatch: "
                      "page %d, mem_w %x, fil_w %x, K %x\r\n",
                      img_u->nam_c,
                      pag_w,
                      mem_w,
                      fil_w,
                      u3K.mug_w[pag_w]);
      abort();
    }
    ptr_w += stp_ws;
  }
}
#endif

/* _ce_image_copy(): copy all of [fom_u] to [tou_u]
**
**   XX use reflinks a la _king_copy_file()?
*/
static c3_o
_ce_image_copy(u3e_image* fom_u, u3e_image* tou_u)
{
  c3_w    i_w;
  c3_w    mem_w[pag_wiz_i];
  size_t  off_i, siz_i = pag_siz_i;
  ssize_t ret_i;

  //  resize images
  //
  _ce_image_resize(tou_u, fom_u->pgs_w);

  //  copy pages into destination image
  //
  for ( i_w = 0; i_w < fom_u->pgs_w; i_w++ ) {
    off_i = (size_t)i_w << (u3a_page + 2);

    if ( siz_i != (ret_i = c3_pread(fom_u->fid_i, mem_w, siz_i, off_i)) ) {
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

    if ( 0 > c3_pwrite(tou_u->fid_i, mem_w, siz_i, off_i) ) {
      fprintf(stderr, "loom: image (%s) copy write: %s\r\n",
                      tou_u->nam_c, strerror(errno));
      return c3n;
    }
  }

  return c3y;
}

/* u3e_backup(); copy snapshot to .urb/bhk (if it doesn't exist yet).
*/
c3_o
u3e_backup(c3_o ovw_o)
{
  u3e_image nop_u = { .nam_c = "north", .pgs_w = 0 };
  u3e_image sop_u = { .nam_c = "south", .pgs_w = 0 };
  c3_i mod_i = O_RDWR | O_CREAT;
  c3_c ful_c[8193];

  snprintf(ful_c, 8192, "%s/.urb/bhk", u3P.dir_c);

  if ( (c3n == ovw_o) && c3_mkdir(ful_c, 0700) ) {
    if ( EEXIST != errno ) {
      fprintf(stderr, "loom: image backup: %s\r\n", strerror(errno));
    }
    return c3n;
  }

  snprintf(ful_c, 8192, "%s/.urb/bhk/%s.bin", u3P.dir_c, nop_u.nam_c);

  if ( -1 == (nop_u.fid_i = c3_open(ful_c, mod_i, 0666)) ) {
    fprintf(stderr, "loom: c3_open %s: %s\r\n", ful_c, strerror(errno));
    return c3n;
  }

  snprintf(ful_c, 8192, "%s/.urb/bhk/%s.bin", u3P.dir_c, sop_u.nam_c);

  if ( -1 == (sop_u.fid_i = c3_open(ful_c, mod_i, 0666)) ) {
    fprintf(stderr, "loom: c3_open %s: %s\r\n", ful_c, strerror(errno));
    return c3n;
  }

  if (  (c3n == _ce_image_copy(&u3P.nor_u, &nop_u))
     || (c3n == _ce_image_copy(&u3P.sou_u, &sop_u)) )
  {

    c3_unlink(ful_c);
    snprintf(ful_c, 8192, "%s/.urb/bhk/%s.bin", u3P.dir_c, nop_u.nam_c);
    c3_unlink(ful_c);
    snprintf(ful_c, 8192, "%s/.urb/bhk", u3P.dir_c);
    c3_rmdir(ful_c);
  }

  close(nop_u.fid_i);
  close(sop_u.fid_i);
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
  c3_w  nod_w, sod_w;

  if ( u3C.wag_w & u3o_dryrun ) {
    return;
  }

  {
    c3_w nop_w = (low_p >> u3a_page);
    c3_w nor_w = (low_p + (pag_wiz_i - 1)) >> u3a_page;
    c3_w sop_w = hig_p >> u3a_page;

    c3_assert( (u3P.gar_w > nop_w) && (u3P.gar_w < sop_w) );

    if ( !(pat_u = _ce_patch_compose(nor_w, u3P.pag_w - sop_w)) ) {
      return;
    }
  }

  nod_w = u3P.nor_u.pgs_w;
  sod_w = u3P.sou_u.pgs_w;

  _ce_patch_sync(pat_u);

  if ( c3n == _ce_patch_verify(pat_u) ) {
    c3_assert(!"loom: save failed");
  }

  _ce_patch_apply(pat_u);

#ifdef U3_SNAPSHOT_VALIDATION
  {
    _ce_image_fine(&u3P.nor_u,
                   u3_Loom,
                   pag_wiz_i);

    _ce_image_fine(&u3P.sou_u,
                   (u3_Loom + u3C.wor_i) - pag_wiz_i,
                   -(ssize_t)pag_wiz_i);

    c3_assert(u3P.nor_u.pgs_w == u3K.nor_w);
    c3_assert(u3P.sou_u.pgs_w == u3K.sou_w);
  }
#endif

  if ( u3C.wag_w ) {
    _ce_loom_protect_north(u3P.nor_u.pgs_w, nod_w);
  }
  else {
    _ce_loom_mapf_north(u3P.nor_u.fid_i, u3P.nor_u.pgs_w, nod_w);
  }

  _ce_loom_protect_south(u3P.sou_u.pgs_w, sod_w);

  _ce_image_sync(&u3P.nor_u);
  _ce_image_sync(&u3P.sou_u);
  _ce_patch_free(pat_u);
  _ce_patch_delete();

  u3e_backup(c3n);
}

/* u3e_live(): start the checkpointing system.
*/
c3_o
u3e_live(c3_c* dir_c)
{
  c3_o nuu_o = c3n;

  //  require that our page size is a multiple of the system page size.
  //
  {
    size_t sys_i = sysconf(_SC_PAGESIZE);

    if ( pag_siz_i % sys_i ) {
      fprintf(stderr, "loom: incompatible system page size (%zuKB)\r\n",
                      sys_i >> 10);
      exit(1);
    }
  }

  u3P.dir_c = dir_c;
  u3P.nor_u.nam_c = "north";
  u3P.sou_u.nam_c = "south";
  u3P.pag_w = u3C.wor_i >> u3a_page;

  //  XX review dryrun requirements, enable or remove
  //
#if 0
  if ( u3C.wag_w & u3o_dryrun ) {
    return c3y;
  } else
#endif
  {
    //  Open image files.
    //
    if ( (c3n == _ce_image_open(&u3P.nor_u)) ||
         (c3n == _ce_image_open(&u3P.sou_u)) )
    {
      fprintf(stderr, "boot: image failed\r\n");
      exit(1);
    }
    else {
      u3_ce_patch* pat_u;
      c3_w  nor_w, sou_w;

      /* Load any patch files; apply them to images.
      */
      if ( 0 != (pat_u = _ce_patch_open()) ) {
        _ce_patch_apply(pat_u);
        _ce_image_sync(&u3P.nor_u);
        _ce_image_sync(&u3P.sou_u);
        _ce_patch_free(pat_u);
        _ce_patch_delete();
      }

      nor_w = u3P.nor_u.pgs_w;
      sou_w = u3P.sou_u.pgs_w;

      //  detect snapshots from a larger loom
      //
      if ( (nor_w + sou_w + 1) >= u3P.pag_w ) {
        fprintf(stderr, "boot: snapshot too big for loom\r\n");
        exit(1);
      }

      //  mark all pages dirty (pages in the snapshot will be marked clean)
      //
      _ce_loom_track_north(0, u3P.pag_w);

      /* Write image files to memory; reinstate protection.
      */
      {
        if ( u3C.wag_w ) {
          _ce_loom_blit_north(u3P.nor_u.fid_i, nor_w);
        }
        else {
          _ce_loom_mapf_north(u3P.nor_u.fid_i, nor_w, 0);
        }

        _ce_loom_blit_south(u3P.sou_u.fid_i, sou_w);

        u3l_log("boot: protected loom\r\n");
      }

      /* If the images were empty, we are logically booting.
      */
      if ( !nor_w && !sou_w ) {
        u3l_log("live: logical boot\r\n");
        nuu_o = c3y;
      }
      else  if ( u3C.wag_w ) {
        u3a_print_memory(stderr, "live: loaded", (nor_w + sou_w) << u3a_page);
      }
      else {
        u3a_print_memory(stderr, "live: mapped", nor_w << u3a_page);
        u3a_print_memory(stderr, "live: loaded", sou_w << u3a_page);
      }

#ifdef U3_GUARD_PAGE
      c3_assert( !_ce_ward_post(nor_w, u3P.pag_w - sou_w) );
#endif
    }
  }

  return nuu_o;
}

/* u3e_yolo(): disable dirty page tracking, read/write whole loom.
*/
c3_o
u3e_yolo(void)
{
  //  NB: u3e_save() will reinstate protection flags
  //
  if ( 0 != mprotect((void *)u3_Loom,
                     u3C.wor_i << 2,
                     (PROT_READ | PROT_WRITE)) )
  {
    //  XX confirm recoverable errors
    //
    fprintf(stderr, "loom: yolo: %s\r\n", strerror(errno));
    return c3n;
  }

#ifdef U3_GUARD_PAGE
  c3_assert( !_ce_ward_protect() );
#endif

  //  mark all pages dirty
  //
  _ce_loom_track_north(0, u3P.pag_w);

  return c3y;
}

/* u3e_init(): initialize guard page tracking.
*/
void
u3e_init(void)
{
  u3P.pag_w = u3C.wor_i >> u3a_page;

#ifdef U3_GUARD_PAGE
  c3_assert( !_ce_ward_post(0, u3P.pag_w) );
#endif

  _ce_loom_track_north(0, u3P.pag_w);
}

/* u3e_ward(): reposition guard page if needed.
*/
void
u3e_ward(u3_post low_p, u3_post hig_p)
{
#ifdef U3_GUARD_PAGE
  c3_w nop_w = low_p >> u3a_page;
  c3_w sop_w = hig_p >> u3a_page;
  c3_w pag_w = u3P.gar_w;

  if ( !((pag_w > nop_w) && (pag_w < hig_p)) ) {
    c3_assert( !_ce_ward_post(nop_w, sop_w) );
    c3_assert( !_ce_flaw_protect(pag_w) );
    c3_assert( u3P.dit_w[pag_w >> 5] & (1 << (pag_w & 31)) );
  }
#endif
}
