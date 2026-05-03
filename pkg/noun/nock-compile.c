/// @file

#include "nock-compile.h"
#include "nock.h"
#include "direct.h"

#include "allocate.h"
#include "hashtable.h"
#include "imprison.h"
#include "jets.h"
#include "jets/k.h"
#include "jets/q.h"
#include "manage.h"
#include "options.h"
#include "retrieve.h"
#include "trace.h"
#include "vortex.h"
#include "xtract.h"
#include "zave.h"


// define to have each opcode printed as it executes,
// along with some other debugging info
#        undef VERBOSE_BYTECODE

/*
::  %imm - write immediate n to d
::  %mov - copy s to d
::  %inc - increment s and write to d
::  %con - cons h and t into d
::  %hed - write head of s to d. Writes 0 if s is an atom
::  %tal - write tail of s to d. Writes 0 if s is an atom
::  %cel - crash if p is an atom
::  %spy - scry with ref in e, path in p, put in d
::  hint ops (except for %memo):
::
::  %his - static hint prologue
::  %hys - static hint epilogue, product of hinted formula in p
::  %hos - static hint epilogue, no product of hinted formula
::  %hid - arbitrary dynamic hint prologue, product of hint-formula in p
::  %hyd - arbitrary dynamic hint epilogue, product of hint-formula in p,
::         product of hinted formula in q
::  %hod - arbitrary dynamic hint epilogue, product of hint-formula in p (no
::         product of hinted formula)
::  memo instructions:
::    %mem - save noun `r` with key [k s f]
::::::::::::::::::::::::::::::::::::::::::::
::
::  %clq - if s is a cell goto z else goto o
::  %eqq - if l and r equal goto z else goto o
::  %brn - if s is 0 goto z, if 1 goto o, else crash
::  %hop - unconditionally go to t
::  %hip - set comefrom label to c and goto t
::  %lnk - evaluate f against u and put the result in d, then goto t
::  %cal - call the arm a with subject in registers v,
::         put result in d, and then goto t
::  %caf - like call but with fast label
::  %lnt - evaluate f against u in tail position
::  %jmp - call the arm a with subject in registers v, in
::         tail position
::  %jmf - like jmp but with fast label
::  %don - return value in s from current arm
::  %dom - return immediate value r
::  %bom - crash
::  %mim: check triple [k s f], write product to d if available and goto z,
::        else goto o
*/

// All opcodes use VLE immediate arguments (capped at 9 bytes for u64 encoding)
#define OPCODES                                                                 \
  /* instructions in a block */                                                 \
  X(IMM, "imm", &&do_imm), /* [2]: index to literal array -> reg */      \
  X(MOV, "mov", &&do_mov), /* [2], from -> to */                            \
  X(INC, "inc", &&do_inc), /* [2], arg -> prod */                           \
  X(CON, "con", &&do_con), /* [3], (hed, tel) -> prod */                    \
  X(HED, "hed", &&do_hed), /* [2], arg -> prod */                           \
  X(TAL, "tal", &&do_tal), /* [2], arg -> prod */                           \
  X(CEL, "cel", &&do_cel), /* [1] */                                           \
  X(HIS, "his", &&do_his), /* [2], hint, formula */                         \
  X(HOS, "hos", &&do_hos), /* [2], hint, formula */                         \
  X(HID, "hid", &&do_hid), /* [3]: hint, clue, formula */          \
  X(HOD, "hod", &&do_hod), /* [3]: hint, clue, formula */          \
  X(SPY, "spy", &&do_spy), /* [3], (ref, pax) -> out */                     \
  X(MEM, "mem", &&do_mem), /* [3]: [sub sot(fol and cid) res] -> memo */\
  X(CAL, "cal", &&do_cal), /* [2]:  dir -> d */                          \
  X(LNK, "lnk", &&do_lnk), /* [3], Nock(u, f) -> d */                       \
  X(CLQ, "clq", &&do_clq), /* [2]: ?^ (arg, jump) */                                 \
  X(EQQ, "eqq", &&do_eqq), /* [3]: .= */                              \
  X(BRN, "brn", &&do_brn), /* [2]: ?: */                                 \
  X(ADV, "adv", &&do_adv), /* [1]: unconditional jmp */                        \
  X(LNT, "lnt", &&do_lnt), /* [2], Nock(u, f) */                            \
  X(JMP, "jmp", &&do_jmp), /* [1]: dir */                                      \
  X(DON, "don", &&do_don), /* [1]: return */                                   \
  X(DOM, "dom", &&do_dom), /* [1]: lit */                                      \
  X(BOM, "bom", &&do_bom),                                                      \
  X(MIM, "mim", &&do_mim), /* [4]: check [sot sub], write to reg if available, else branch */\
  X(LAST, NULL, NULL),

// Opcodes. Define X to select the enum name from OPCODES.
#define X(opcode, name, indirect_jump) opcode
enum { OPCODES };
#undef X

# define X(opcode, name, indirect_jump) name
static c3_c* opcode_names[] = { OPCODES };
# undef X

static inline c3_w
_nc_of_prog(u3nc_prog *pog_u)
{
  u3_post pog_p = u3of(u3nc_prog, pog_u);
  return pog_p >> u3a_vits;
}

static inline u3nc_prog*
_nc_to_prog(c3_w pog_w)
{
  u3_post pog_p = pog_w << u3a_vits;
  return u3to(u3nc_prog, pog_p);
}

static_assert(LAST < 256);

typedef struct __attribute__((__packed__)) {
  u3nc_prog*  pog_u;
  c3_w        ip_w;
  c3_y        tar_y;
} nc_burnframe;

/* _n_peek(): pointer to noun in the stack slot
 *            off: 0 north, -1 south
 */
static inline u3_noun*
_nc_peek(c3_ys mov, c3_ys off, c3_w sot_w)
{
  return u3to(u3_noun, (u3R->cap_p - mov * sot_w) + off);
}

static inline void
_nc_put(u3_noun* sot_u, u3_noun som)
{
  u3_noun old = *sot_u;
  if ( u3_none != old ) u3z(old);
  *sot_u = som;
}

static void
_nc_move(c3_ys mov, c3_ys off, c3_y num_y)
{
  u3R->cap_p += (mov * num_y);

#ifndef U3_GUARD_PAGE
  if ( 0 == off ) {
    if( !(u3R->cap_p > u3R->hat_p) ) {
      u3m_bail(c3__meme);
    }
  }
  else {
    if( !(u3R->cap_p < u3R->hat_p) ) {
      u3m_bail(c3__meme);
    }
  }
#endif
}

//  RETAINS
static void
static_prologue(u3_noun hint, u3_noun formula)
{

}

//  RETAINS
static void
static_epilogue(u3_noun hint, u3_noun formula)
{

}

//  RETAINS
static void
dynamic_prologue(u3_noun hint, u3_noun formula, u3_noun clue)
{

}

//  RETAINS
static void
dynamic_epilogue(u3_noun hint, u3_noun formula, u3_noun clue)
{

}

static void
_nc_push_args(c3_ys mov, c3_ys off, c3_y tot_y, c3_y len_y, u3_noun* args)
{
  _nc_move(mov, off, tot_y);
  for ( c3_y i_y = 0; i_y < tot_y; i_y++) {
    *_nc_peek(mov, off, i_y) = ( i_y < len_y ) ? args[i_y] : u3_none;
  }
}

u3nc_prog*
_n_bite_direct(u3_noun sock, u3_noun fol, c3_t entry_t);

static u3nc_prog*
_n_find_direct(u3_noun sock_fol)
{
  u3a_road* rod_u = u3R;
  u3_weak pog;
  while ( 1 ) {
    if ( u3_none != (pog = u3h_git(rod_u->byc_direct_p, sock_fol)) ) {
      return _nc_to_prog(pog);
    }
    if ( !rod_u->par_p ) break;
    rod_u = u3to(u3a_road, rod_u->par_p);
  }
  u3nc_prog* pog_u = _n_bite_direct(u3h(sock_fol), u3t(sock_fol), false);
  u3h_put(u3R->byc_direct_p, sock_fol, _nc_of_prog(pog_u));
  return pog_u;
}

static void
_nc_set_pogp_dire(u3nc_dire* dir_u)
{
  dir_u->pog_p = u3of(u3nc_prog, _n_find_direct(dir_u->bell));
}

static c3_d
_vle_read(c3_y* buf_y, c3_w* ip_w)
{
  c3_y byt_y;
  c3_d out_d = 0;
  for (c3_d i_d = 0; i_d < 9; i_d++) {
    byt_y = buf_y[(*ip_w)++];
    out_d |= ((byt_y & 0x7f) << (i_d * 7));
    if ( byt_y < 0x80 ) {
      return out_d;
    }
  }
  u3_assert(!"out of range");
}

static u3_noun
// len_y - number of input args, tot_y - total number of regs
_nc_burn(u3nc_prog* pog_u, u3_noun* args, c3_y len_y, c3_ys mov, c3_ys off)
{
# define X(opcode, name, indirect_jump) indirect_jump
  static void* lab[] = { OPCODES };
# undef X

  c3_y *pog = pog_u->byc_u.ops_y;
  c3_w ip_w = 0;
  u3p(void) empty;
  nc_burnframe* fam;
  u3_noun pro;

  (void)empty;

  empty = u3R->cap_p;
  _nc_push_args(mov, off, pog_u->tot_y, len_y, args);

#ifdef VERBOSE_BYTECODE
  #define BURN() fprintf(stderr, "%s ", opcode_names[pog[ip_w]]); goto *lab[pog[ip_w++]]
#else
  #define BURN() goto *lab[pog[ip_w++]]
#endif

#define VAL()   (_vle_read(pog, &ip_w))
#define PEEK(R) (_nc_peek(mov, off, R))

#define HEAD(som)  ((c3n == u3du(som)) ? 0 : u3h(som))
#define TAIL(som)  ((c3n == u3du(som)) ? 0 : u3t(som))

#define POP_REGS() do {                               \
  for ( c3_y i_y = 0; i_y < pog_u->tot_y; i_y++ ) {   \
        if ( u3_none != *PEEK(i_y) ) u3z(*PEEK(i_y)); \
      }                                               \
      u3R->cap_p -= (mov * pog_u->tot_y);             \
} while (0)

  BURN();
  {
    do_imm: {
      c3_w i_w = VAL();
      c3_w d_w = VAL();
      _nc_put(_nc_peek(mov, off, d_w), u3k(pog_u->lit_u.non[i_w]));
      BURN();
    }

    do_mov: {
      c3_w s_w = VAL(), d_w = VAL();
      _nc_put(PEEK(d_w), u3k(*PEEK(s_w)));
      BURN();
    }

    do_inc: {
      c3_w s_w = VAL(), d_w = VAL();
      _nc_put(PEEK(d_w), u3i_vint(u3k(*PEEK(s_w))));
      BURN();
    }

    do_con: {
      c3_w h_w = VAL(),
           t_w = VAL(),
           d_w = VAL();
      _nc_put(PEEK(d_w), u3nc(u3k(*PEEK(h_w)), u3k(*PEEK(h_w))));
      BURN();
    }

    do_hed: {
      c3_w s_w = VAL(), d_w = VAL();
      if ( c3n == u3du(*PEEK(s_w)) )
      _nc_put(PEEK(d_w), u3k(HEAD(*PEEK(s_w))));
      BURN();
    }

    do_tal: {
      c3_w s_w = VAL(), d_w = VAL();
      _nc_put(PEEK(d_w), u3k(TAIL(*PEEK(s_w))));
      BURN();
    }

    do_cel: {
      if ( c3n == u3du(*PEEK(VAL())) ) {
        u3m_bail(c3__exit);
      }
      BURN();
    }

    do_his: {
      c3_w hin_w = VAL(), fol_w = VAL();
      static_prologue(pog_u->lit_u.non[hin_w], pog_u->lit_u.non[fol_w]);
      BURN();
    }

    do_hos: {
      c3_w hin_w = VAL(), fol_w = VAL();
      static_epilogue(pog_u->lit_u.non[hin_w], pog_u->lit_u.non[fol_w]);
      BURN();
    }

    do_hid: {
      c3_w hin_w = VAL();
      c3_w clu_w = VAL();
      c3_w fol_w = VAL();
      dynamic_prologue(pog_u->lit_u.non[hin_w], pog_u->lit_u.non[fol_w],
        *PEEK(clu_w));
      BURN();
    }

    do_hod: {
      c3_w hin_w = VAL();
      c3_w clu_w = VAL();
      c3_w fol_w = VAL();
      dynamic_epilogue(pog_u->lit_u.non[hin_w], pog_u->lit_u.non[fol_w],
        *PEEK(clu_w));
      BURN();
    }

    do_spy: {
      c3_w ref_w = VAL(),
           pax_w = VAL(),
           des_w = VAL();
      u3_noun x = u3m_soft_esc(u3k(*PEEK(ref_w)), u3k(*PEEK(pax_w)));
      if ( c3n == u3du(x) ) {
        u3m_bail(u3nc(1, *PEEK(pax_w)));
      }
      else if ( c3n == u3du(u3t(x)) ) {
        u3t_push(u3nt(c3__hunk, *PEEK(ref_w), *PEEK(pax_w)));
        u3m_bail(c3__exit);
      }
      else {
        _nc_put(PEEK(des_w), u3k(u3t(u3t(x))));
        u3z(x);
        BURN();
      }
    }

    do_mem: {
      c3_stub;
    }

    do_cal: {
      c3_s dir_w = VAL();
      c3_w des_w = VAL();
      u3nc_dire* dir_u = &pog_u->dir_u.dat_u[dir_w];
      c3_w len_w = dir_u->len_w;
      u3_noun args[len_w];
      for (c3_w i_w = 0; i_w < len_w; i_w++) {
        args[i_w] = u3k(*PEEK(i_w));
      }
      if ( dir_u->ham_u ) {
        u3_weak res = dir_u->ham_u(args);
        if ( u3_none != res ) {
          _nc_put(PEEK(des_w), res);
          for (c3_w i_w = 0; i_w < len_w; i_w++) {
            u3z(args[i_w]);
          }
          BURN();
        }
      }
      fam         = u3to(nc_burnframe, u3R->cap_p) + off + mov;
      u3R->cap_p  = u3of(nc_burnframe, fam - off);

      fam->ip_w   = ip_w;
      fam->pog_u  = pog_u;
      fam->tar_y  = des_w;
      if ( !dir_u->pog_p ) _nc_set_pogp_dire(dir_u);
      pog_u = u3to(u3nc_prog, dir_u->pog_p);
      pog   = pog_u->byc_u.ops_y;
      ip_w  = 0;

      _nc_push_args(mov, off, pog_u->tot_y, len_w, args);
      BURN();
    }

    do_lnk: {
      c3_w sub_w = VAL(),
           fol_w = VAL(),
           des_w = VAL();
      _nc_put(PEEK(des_w), u3n_nock_on(u3k(*PEEK(sub_w)), u3k(*PEEK(fol_w))));
      BURN();
    }

    do_clq: {
      c3_w som_w = VAL();
      c3_w sip_w = VAL();
      ip_w += ( c3y == u3a_is_cell(*PEEK(som_w)) ) ? 0 : sip_w;
      BURN();
    }

    do_eqq: {
      c3_w one_w = VAL(), two_w = VAL();
      c3_w sip_w = VAL();
      ip_w += ( c3y == u3r_sing(*PEEK(one_w), *PEEK(two_w)) ) ? 0 : sip_w;
      BURN();
    }

    do_brn: {
      c3_w som_w = VAL();
      c3_w sip_w = VAL();
      ip_w += ( c3y == u3x_loob(*PEEK(som_w)) ) ? 0 : sip_w;
      BURN();
    }

    do_adv: {
      ip_w += VAL();
      BURN();
    }

    do_lnt: {
      c3_w sub_w = VAL(),
           fol_w = VAL();
      pro = u3n_nock_on(*PEEK(sub_w), *PEEK(fol_w));
      goto done_out;
    }

    do_jmp: {
      c3_w dir_w = VAL();
      u3nc_dire* dir_u = &pog_u->dir_u.dat_u[dir_w];
      c3_w len_w = dir_u->len_w;
      u3_noun args[len_w];  // XX allocate the array on the road?
      for (c3_w i_w = 0; i_w < len_w; i_w++) {
        args[i_w] = u3k(*PEEK(i_w));
      }
      
      if ( dir_u->ham_u ) {
        pro = dir_u->ham_u(args);
        if ( u3_none != pro ) {
          for (c3_y i_y = 0; i_y < len_w; i_y++) {
            u3z(args[i_y]);
          }
          goto done_out;
        }
      }

      POP_REGS();
      
      if ( !dir_u->pog_p ) _nc_set_pogp_dire(dir_u);
      pog_u = u3to(u3nc_prog, dir_u->pog_p);
      pog   = pog_u->byc_u.ops_y;
      ip_w  = 0;

      _nc_push_args(mov, off, pog_u->tot_y, len_w, args);
      BURN();
    }

    do_don: {
      pro = u3k(*PEEK(VAL()));
      goto done_out;
    }

    do_dom: {
      pro = u3k(pog_u->lit_u.non[VAL()]);
      goto done_out;
    }
    
    done_out: {
      u3_assert(u3_none != pro);
      POP_REGS();
      if ( empty == u3R->cap_p ) {
        return pro;
      }
      fam        = u3to(nc_burnframe, u3R->cap_p) + off;
      u3R->cap_p = u3of(nc_burnframe, fam - (mov+off));

      pog_u = fam->pog_u;
      pog   = pog_u->byc_u.ops_y;
      ip_w  = fam->ip_w;
      _nc_put(PEEK(fam->tar_y), pro);
      BURN();
    }

    do_bom: {
      u3m_bail(c3__exit);
    }

    do_mim: {
      c3_stub;
    }
  }
}

static u3_noun
_nc_burn_out(u3nc_prog* pog_u, u3_noun* args, c3_y len_y)
{
  c3_ys mov, off;
  if ( c3y == u3a_is_north(u3R) ) {
    mov = -1;
    off = 0;
  }
  else {
    mov = 1;
    off = -1;
  }
  return _nc_burn(pog_u, args, len_y, mov, off);
}

static inline c3_y
_nc_map_tag_cod(u3_noun tag)
{
  switch ( tag ) {
    default: u3_assert(0);
    case c3__clq: return CLQ;
    case c3__eqq: return EQQ;
    case c3__brn: return BRN;
    case c3__mim: return MIM;
    case c3__jmf:
    case c3__jmp: return JMP;
    case c3__lnt: return LNT;
    case c3__don: return DON;
    case c3__dom: return DOM;
    case c3__bom: return BOM;
    case c3__imm: return IMM;
    case c3__mov: return MOV;
    case c3__hed: return HED;
    case c3__tal: return TAL;
    case c3__cel: return CEL;
    case c3__his: return HIS;
    case c3__hos: return HOS;
    case c3__hid: return HID;
    case c3__hod: return HOD;
    case c3__spy: return SPY;
    case c3__mem: return MEM;
    case c3__lnk: return LNK;
    case c3__caf:
    case c3__cal: return CAL;
    case c3__con: return CON;
    case c3__inc: return INC;
  }
}

//  RETAINS
static c3_w
_nc_table_add(u3_post har_p, u3_noun som)
{
  u3_weak out;
  if ( u3_none == (out = u3h_git(har_p, som)) ) {
    c3_w new_w = u3h_wyt(har_p);
    u3h_put(har_p, som, u3i_word(new_w));
    return new_w;
  }
  return u3r_word(0, out);
}

//  retains
static c3_w
_nc_table_get(u3_post har_p, u3_noun som)
{
  return u3r_word(0, u3x_good(u3h_git(har_p, som)));
}

static void
_vle_write(c3_y** buf_y, c3_d val_d)
{
  if ( c3_likely(val_d < 0xf0) ) {
    *(*buf_y)++ = val_d;
    return;
  }

  do {
    *(*buf_y)++ = 0x80 | (val_d & 0x7f);
    val_d >>= 7;
  } while ( val_d > 0x7f );

  *(*buf_y)++ = val_d;
}

static c3_w
_vle_measure(c3_d val_d)
{
  return (c3_bits_chub(val_d) + 6) / 7;
}

static c3_w
_vle_measure_atom(u3_atom a)
{
  c3_d val_d;
  if ( u3r_chub_fit(&val_d, a) ) {
    return _vle_measure(val_d);
  }
  u3m_bail(c3__fail);
}

inline static u3_atom
_r_atom(u3_noun som)
{
  if ( _(u3ud(som)) ) return som;
  u3m_bail(c3__fail);
}


//  RETAINS
static u3_noun
_nc_nouncode_measure(u3_noun ops, 
  c3_w* ops_w,
  u3_post lit_p,
  c3_w* mem_w,
  c3_w* arg_w,
  c3_w* dir_w)
{
  u3_noun sip = u3_nul;
  u3_noun op, tag, args, z, o;
  c3_y ax_z, ax_o;
  #define MEASURE_REG(SOM)  (*ops_w += _vle_measure_atom(_r_atom(SOM)))
  #define MEASURE_LIT(SOM) (*ops_w += _vle_measure(_nc_table_add(lit_p, SOM)))
  while (u3_nul != ops) {
    u3_assert(c3y == u3r_cell(ops, &op, &ops));
    u3_assert(c3y == u3r_cell(op, &tag, &args));
    *ops_w += 1;
    switch ( tag ) {
      default: u3_assert(0);
      case c3__clq: {
        ax_z = 6;
        ax_o = 7;
        MEASURE_REG(u3h(args));
        goto _branch;
      } break;
      
      case c3__eqq: {
        ax_z = 14;
        ax_o = 15;
        MEASURE_REG(u3h(args));
        MEASURE_REG(u3h(u3t(args)));
        goto _branch;
      } break;
      
      case c3__brn: {
        ax_z = 6;
        ax_o = 7;
        MEASURE_REG(u3h(args));
        goto _branch;
      } break;
      
      case c3__mim: {
        c3_stub;
        goto _branch;
      } break;

      _branch: {
        //  [branch-instruction][args][delta1][y-branch][ADV][delta2][n-branch]
        //                           ^ we are here
        //  delta1 = len(y-branch) + 1 + len(delta2)
        //  delta2 = len(n-branch)
        //
        u3_assert(c3y == u3r_mean(args, {ax_z, &z}, {ax_o, &o}));
        c3_w y_ops_w = 0, n_ops_w = 0;
        u3_noun sip_z = _nc_nouncode_measure(z, &y_ops_w, lit_p, mem_w, arg_w, dir_w);
        u3_noun sip_o = _nc_nouncode_measure(o, &n_ops_w, lit_p, mem_w, arg_w, dir_w);
        c3_w delta2_w = n_ops_w;
        c3_w delta1_w = y_ops_w + 1 + _vle_measure(delta2_w);
        *ops_w += _vle_measure(delta1_w) + delta1_w + delta2_w;
        sip = u3kb_zing(u3nl(
          sip_o,
          u3nc(u3i_word(delta2_w), u3_nul),
          sip_z,
          u3nc(u3i_word(delta1_w), u3_nul),
          sip
        ));
      } break;
      
      case c3__jmf: {
        *arg_w += u3r_word(0, u3qb_lent(u3h(u3t(args))));
        goto _callsite;
      } break;
      
      case c3__jmp: {
        *arg_w += u3r_word(0, u3qb_lent(u3t(args)));
        goto _callsite;
      } break;

      case c3__caf: {
        *arg_w += u3r_word(0, u3qb_lent(u3h(u3t(args))));
        goto _callsite;
      } break;

      case c3__cal: {
        *arg_w += u3r_word(0, u3qb_lent(u3h(u3t(args))));
        goto _callsite;
      } break;

      _callsite: {
        *ops_w += _vle_measure(*dir_w);
        *dir_w += 1;
      } break;
      
      case c3__lnt: {
        MEASURE_REG(u3h(args));
        MEASURE_REG(u3t(args));
      } break;
      
      case c3__don: {
        MEASURE_REG(args);
      } break;
      
      case c3__dom: {
        MEASURE_LIT(args);
      } break;
      
      case c3__bom: {

      } break;
      
      case c3__imm: {
        MEASURE_LIT(u3h(args));
        MEASURE_REG(u3t(args));
      } break;
      
      case c3__mov:
      case c3__inc:
      case c3__hed:
      case c3__tal: {
        MEASURE_REG(u3h(args));
        MEASURE_REG(u3t(args));
      } break;
      
      case c3__cel: {
        MEASURE_REG(args);
      } break;
      
      case c3__his:
      case c3__hos: {
        MEASURE_LIT(u3h(args));
        MEASURE_LIT(u3t(args));
      } break;
      
      case c3__hid:
      case c3__hod: {
        MEASURE_LIT(u3h(args));
        MEASURE_REG(u3h(u3t(args)));
        MEASURE_LIT(u3t(u3t(args)));
      } break;
      
      case c3__mem: {
        c3_stub;
      } break;
      
      case c3__spy:
      case c3__lnk:
      case c3__con: {
        MEASURE_REG(u3h(args));
        MEASURE_REG(u3h(u3t(args)));
        MEASURE_REG(u3t(u3t(args)));
      } break;
    }
  }
  #undef MEASURE_REG
  #undef MEASURE_LIT
  return sip;
}


//  retains
static void
_nc_write_dire(u3nc_dire* dir_u, c3_w** arg_w, u3_noun bell, u3_noun regs, u3_noun ring)
{
  dir_u->arg_w = *arg_w;
  dir_u->bell  = u3k(bell);
  dir_u->len_w = u3r_word(0, u3qb_lent(regs));
  dir_u->ring  = u3k(ring);
  dir_u->pog_p = 0;
  dir_u->ham_u = NULL;  //  XX jet matching
  u3_noun r;
  while ( u3_nul != regs ) {
    u3_assert(c3y == u3r_cell(regs, &r, &regs));
    *(*arg_w)++ = u3r_word(0, r);
  }
}

static void
_nc_nouncode_write(u3_noun ops,
  u3_noun* sip,
  c3_y**      ops_y,
  u3_post     lit_p,
  u3nc_memo** mem_u,
  c3_w**      arg_w,
  u3nc_dire* dir_u,
  c3_w*      dir_w)
{
  #define WRITE_LIT(SOM)  (_vle_write(ops_y, _nc_table_get(lit_p, SOM)))
  #define WRITE_REG(SOM)  (_vle_write(ops_y, u3r_word(0, _r_atom(SOM))))
  u3_noun op, tag, args, z, o, s;
  c3_y ax_z, ax_o;
  while (u3_nul != ops) {
    u3_assert(c3y == u3r_cell(ops, &op, &ops));
    u3_assert(c3y == u3r_cell(op, &tag, &args));
    *(*ops_y)++ = _nc_map_tag_cod(tag);
    switch ( tag ) {
      default: break;
      case c3__mim: {
        c3_stub;
        goto _branch;
      }
      case c3__clq: {
        ax_z = 6;
        ax_o = 7;
        WRITE_REG(u3h(args));
        goto _branch;
      }
      case c3__eqq: {
        ax_z = 14;
        ax_o = 15;
        WRITE_REG(u3h(args));
        WRITE_REG(u3h(u3t(args)));
        goto _branch;
      }
      case c3__brn: {
        ax_z = 6;
        ax_o = 7;
        WRITE_REG(u3h(args));
        goto _branch;
      }
      _branch: {
        u3_assert(c3y == u3r_mean(args, {ax_z, &z}, {ax_o, &o}));
        u3_assert(c3y == u3r_cell(*sip, &s, sip));
        _vle_write(ops_y, u3r_word(0, s));
        _nc_nouncode_write(z, sip, ops_y, lit_p, mem_u, arg_w, dir_u, dir_w);
        *(*ops_y)++ = ADV;
        u3_assert(c3y == u3r_cell(*sip, &s, sip));
        _vle_write(ops_y, u3r_word(0, s));
        _nc_nouncode_write(o, sip, ops_y, lit_p, mem_u, arg_w, dir_u, dir_w);
      } break;
     
      case c3__dom: {
        WRITE_LIT(args);
      } break;

      case c3__imm: {
        WRITE_LIT(u3h(args));
        WRITE_REG(u3t(args));
      } break;

      case c3__his:
      case c3__hos: {
        WRITE_LIT(u3h(args));
        WRITE_LIT(u3t(args));
      } break;

      case c3__hid:
      case c3__hod: {
        WRITE_LIT(u3h(args));
        WRITE_REG(u3h(u3t(args)));
        WRITE_LIT(u3t(u3t(args)));
      } break;

      case c3__mem: {
        c3_stub;
      } break;

      case c3__jmp: {
        _vle_write(ops_y, *dir_w);
        u3_noun bell, regs;
        u3_assert(c3y == u3r_mean(args, {2, &bell}, {3, &regs}));
        _nc_write_dire(dir_u + *dir_w, arg_w, bell, regs, u3_nul);
        (*dir_w)++;
      } break;

      case c3__jmf: {
        _vle_write(ops_y, *dir_w);
        u3_noun bell, regs, ring;
        u3_assert(c3y == u3r_mean(args, {2, &bell}, {6, &regs}, {7, &ring}));
        _nc_write_dire(dir_u + *dir_w, arg_w, bell, regs, ring);
        (*dir_w)++;
      } break;

      case c3__caf: {
        _vle_write(ops_y, *dir_w);
        u3_noun bell, regs, ring, r;
        u3_assert(c3y == u3r_mean(args,
                                  {2, &bell},
                                  {6, &regs},
                                  {14, &r},
                                  {15, &ring})
        );
        WRITE_REG(r);
        _nc_write_dire(dir_u + *dir_w, arg_w, bell, regs, ring);
        (*dir_w)++;
      } break;

      case c3__cal: {
        _vle_write(ops_y, *dir_w);
        u3_noun bell, regs, r;
        u3_assert(c3y == u3r_mean(args,
                                  {2, &bell},
                                  {6, &regs},
                                  {7, &r})
        );
        WRITE_REG(r);
        _nc_write_dire(dir_u + *dir_w, arg_w, bell, regs, u3_nul);
        (*dir_w)++;
      } break;

      case c3__lnt: {
        WRITE_REG(u3h(args));
        WRITE_REG(u3t(args));
      } break;

      case c3__don: {
        WRITE_REG(args);
      } break;

      case c3__bom: {

      } break;

      case c3__mov:
      case c3__inc:
      case c3__hed:
      case c3__tal: {
        WRITE_REG(u3h(args));
        WRITE_REG(u3t(args));
      } break;

      case c3__cel: {
        WRITE_REG(args);
      } break;

      case c3__spy:
      case c3__lnk:
      case c3__con: {
        WRITE_REG(u3h(args));
        WRITE_REG(u3h(u3t(args)));
        WRITE_REG(u3t(u3t(args)));
      } break;
    }
  }
  #undef WRITE_REG
  #undef WRITE_LIT
}

static void
_nc_cb_copy(u3_noun kev, void* arr_u)
{
  u3_noun* non_u = arr_u;
  u3_noun non = u3h(kev), idx = u3t(kev);
  u3_assert(idx < 256);
  u3_assert(non_u[idx] == u3_none);
  non_u[idx] = u3k(non);
}

//  retains
static u3nc_prog*
_nc_nouncode_build(u3_noun ops)
{
  u3_post lit_p = u3h_new();
  c3_w ops_w = 0, mem_w = 0, arg_w = 0, dir_w = 0;
  u3_noun sip = _nc_nouncode_measure(ops, &ops_w, lit_p, &mem_w, &arg_w, &dir_w);
  c3_w lit_w = u3h_wyt(lit_p);

  //  {u3nc_prog}[ops][args][literals][memo][dire]

  c3_w siz_w = sizeof(u3nc_prog);
  //  byte offsets of various buffers:
  //
  c3_w pos_w = siz_w;  //  ops
  c3_w rog_w = siz_w = c3_align(siz_w + ops_w, sizeof(c3_w), C3_ALGHI);  // args
  c3_w non_w = siz_w = c3_align((siz_w + arg_w * sizeof(c3_w)), sizeof(u3_noun), C3_ALGHI);  //  literals
  c3_w mom_w = siz_w = c3_align((siz_w + sizeof(u3_noun) * lit_w), sizeof(u3nc_memo), C3_ALGHI);  //  memo slots
  c3_w dor_w = siz_w = c3_align((siz_w + sizeof(u3nc_memo) * mem_w), sizeof(u3nc_dire), C3_ALGHI);  // callsite slots
  siz_w += sizeof(u3nc_dire) * dir_w;

  u3nc_prog* pog_u = u3a_malloc(siz_w);
  pog_u->byc_u.len_w = ops_w;
  c3_y* ops_y = pog_u->byc_u.ops_y = (c3_y*)pog_u + pos_w;
  pog_u->lit_u.len_w = lit_w;
  pog_u->lit_u.non = (u3_noun*)((c3_y*)pog_u + non_w);
  pog_u->mem_u.len_w = mem_w;
  u3nc_memo* mem_u = pog_u->mem_u.sot_u = (u3nc_memo*)((c3_y*)pog_u + mom_w);
  pog_u->dir_u.len_w = dir_w;
  u3nc_dire* dir_u = pog_u->dir_u.dat_u = (u3nc_dire*)((c3_y*)pog_u + dor_w);

  c3_w* rag_w = (c3_w*)((c3_y*)pog_u + rog_w);

  for (c3_w i_w = 0; i_w < lit_w; i_w++) {
    pog_u->lit_u.non[i_w] = u3_none;
  }
  u3h_walk_with(lit_p, _nc_cb_copy, pog_u->lit_u.non);
  for (c3_w i_w = 0; i_w < lit_w; i_w++) {
    u3_assert(u3_none != pog_u->lit_u.non[i_w]);
  }

  dir_w = 0;
  _nc_nouncode_write(ops, &sip, &ops_y, lit_p, &mem_u, &rag_w, dir_u, &dir_w);
  u3z(sip);
  u3h_free(lit_p);
  return pog_u;
}

u3nc_prog*
_n_bite_direct(u3_noun sock, u3_noun fol, c3_t entry_t)
{
  u3_noun ops = u3d_bell_ops(u3nc(u3k(sock), u3k(fol)), entry_t);
  u3nc_prog* out_u = _nc_nouncode_build(ops);
  u3z(ops);
  return out_u;
}

static u3_noun
_cb_jib_cons(u3_weak list, void* ptr_v)
{
  return u3nc(*(u3_noun*)ptr_v, ( u3_none == list ) ? u3_nul : list);
}

u3nc_prog*
u3nc_build_entry_direct(u3_noun sock, u3_noun fol)
{
  u3nc_prog* out_u = _n_bite_direct(sock, fol, true);
  u3_noun i_larp = u3nc(u3k(sock), _nc_of_prog(out_u));
  u3h_jib(u3R->byc_entry_p, fol, _cb_jib_cons, &i_larp);
  return out_u;
}

u3nc_prog*
u3nc_look_entry_direct(u3_noun sub, u3_noun fol)
{
  u3_weak list, sock_pog;
  u3a_road* rod_u = u3R;
  while ( 1 ) {
    if ( u3_none != (list = u3h_git(rod_u->byc_entry_p, fol))
      && u3_none != (sock_pog = u3d_match_sock(c3y, sub, list))) {
      return _nc_to_prog(u3t(sock_pog));
    }
    if ( !rod_u->par_p ) return NULL;
    rod_u = u3to(u3a_road, rod_u->par_p);
  }
}

u3_noun
u3nc_nock_on(u3_noun bus, u3_noun fol)
{
  return _nc_burn_out(u3d_search(bus, fol), &bus, 1);
}