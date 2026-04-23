/// @file

#include "nock-compile.h"
#include "nock.h"

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

// Several opcodes "overflow" (from byte to short index) to their successor, so
// order can matter here.
// Note that we use an X macro (https://en.wikipedia.org/wiki/X_Macro) to unify
// the opcode's enum name, string representation, and computed goto into a
// single structure.
#define OPCODES                                                                 \
  /* instructions in a block */                                                 \
  X(IMM, "imm", &&do_imm), /* c3_s, c3_y: index to literal array -> reg */      \
  X(MOV, "mov", &&do_mov), /* c3_y[2], from -> to */                            \
  X(INC, "inc", &&do_inc), /* c3_y[2], arg -> prod */                           \
  X(CON, "con", &&do_con), /* c3_y[3], (hed, tel) -> prod */                    \
  X(HED, "hed", &&do_hed), /* c3_y[2], arg -> prod */                           \
  X(TAL, "tal", &&do_tal), /* c3_y[2], arg -> prod */                           \
  X(CEL, "cel", &&do_cel), /* c3_y */                                           \
  X(HIS, "his", &&do_his), /* c3_s[2], hint, formula */                         \
  /*X(HYS, "hys", &&do_hys), */                                                 \
  X(HOS, "hos", &&do_hos), /* c3_s[2], hint, formula */                         \
  X(HID, "hid", &&do_hid), /* c3_s, c3_y, c3_s: hint, clue, formula */          \
  /*X(HYD, "hyd", &&do_hyd), */                                                 \
  X(HOD, "hod", &&do_hod), /* c3_s, c3_y, c3_s: hint, clue, formula */          \
  X(SPY, "spy", &&do_spy), /* c3_y[3], (ref, pax) -> out */                     \
  X(MEM, "mem", &&do_mem), /* c3_y, c3_s, c3_y: [sub sot(fol and cid) res] -> memo */\
  X(CAL, "cal", &&do_cal), /* c3_s, c3_y:  dir -> d */                          \
  X(LNK, "lnk", &&do_lnk), /* c3_y[3], Nock(u, f) -> d */                       \
  /*  X(CAF, "caf", &&do_caf), same as cal? */                                  \
  /* control-flow instructions */                                               \
  X(CLQ, "clq", &&do_clq), /* c3_y, c3_w: ?^ */                                 \
  X(EQQ, "eqq", &&do_eqq), /* c3_y[2], c3_w: .= */                              \
  X(BRN, "brn", &&do_brn), /* c3_y, c3_w: ?: */                                 \
  X(ADV, "adv", &&do_adv), /* c3_w: unconditional jmp */                        \
  X(LNT, "lnt", &&do_lnt), /* c3_y[2], Nock(u, f) */                            \
  X(JMP, "jmp", &&do_jmp), /* c3_s: dir */                                      \
  /* X(JMF, "jmf", &&do_jmf), same as jmp? */                                   \
  X(DON, "don", &&do_don), /* c3_y: return */                                   \
  X(DOM, "dom", &&do_dom), /* c3_s: lit */                                      \
  X(BOM, "bom", &&do_bom),                                                      \
  X(MIM, "mim", &&do_mim), /* c3_s, c3_y, c3_y, c3_w: check [sot sub], write to reg if available, else branch */\
  X(LAST, NULL, NULL),

// Opcodes. Define X to select the enum name from OPCODES.
#define X(opcode, name, indirect_jump) opcode
enum { OPCODES };
#undef X

static_assert(LAST < 256);

/* _n_arg(): return the size (in bytes) of an opcode's argument
 */
static inline c3_y
_n_arg(c3_y cod_y)
{
  switch ( cod_y ) {
    case IMM: return sizeof(c3_s) + sizeof(c3_y);

    case MOV: return sizeof(c3_y[2]);

    case INC: return sizeof(c3_y[2]);

    case CON: return sizeof(c3_y[3]);

    case HED:
    case TAL: return sizeof(c3_y[2]);

    case CEL: return sizeof(c3_y);

    case HIS: return sizeof(c3_s[2]);

    case HOS: return sizeof(c3_s[2]);

    case HID: 
    case HOD: return sizeof(c3_s[2]) + sizeof(c3_y);

    case SPY: return sizeof(c3_y[3]);

    case MEM: return sizeof(c3_s) + sizeof(c3_y[2]);

    case CLQ: return sizeof(c3_y) + sizeof(c3_w);

    case EQQ: return sizeof(c3_y[2]) + sizeof(c3_w);

    case BRN: return sizeof(c3_y) + sizeof(c3_w);

    case ADV: return sizeof(c3_w);

    case LNK: return sizeof(c3_y[3]);

    case CAL: return sizeof(c3_s) + sizeof(c3_y);

    case LNT: return sizeof(c3_y[2]);

    case JMP: return sizeof(c3_s);
    case DON: return sizeof(c3_y);
    case DOM: return sizeof(c3_s);
    case BOM: return 0;
    case MIM: return sizeof(c3_s) + sizeof(c3_y[2]) + sizeof(c3_w);

    default:
      u3_assert( 0 );
  }
}

typedef struct __attribute__((__packed__)) {
  u3nc_prog*  pog_u;
  c3_w        ip_w;
  c3_y        tar_y;
  c3_y        tot_y;
} nc_burnframe;

/* _n_peek(): pointer to noun in the stack slot
 *            off: 0 north, -1 south
 */
static inline u3_noun*
_nc_peek(c3_ys mov, c3_ys off, c3_y sot_y)
{
  return u3to(u3_noun, (u3R->cap_p - mov * sot_y) + off);
}

static inline void
_nc_put(u3_noun* sot_u, u3_noun som)
{
  u3_noun old = *sot_u;
  if ( u3_none != old ) u3z(old);
  *sot_u = som;
}

static inline c3_s
_nc_resh(c3_y* buf, c3_w* ip_w)
{
  c3_y les = buf[(*ip_w)++];
  c3_y mos = buf[(*ip_w)++];
  return les | (mos << 8);
}

static inline c3_w
_nc_rewo(c3_y* buf, c3_w* ip_w)
{
  c3_y one = buf[(*ip_w)++],
       two = buf[(*ip_w)++],
       tre = buf[(*ip_w)++],
       qua = buf[(*ip_w)++];
  return one | (two << 8) | (tre << 16) | (qua << 24);
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

static c3_t
_nc_is_last_frame(c3_ys mov, c3_ys off, u3p(void) empty, c3_y tot_y)
{
  return empty == (u3R->cap_p - (mov * tot_y));
}

static u3_noun
// len_y - number of input args, tot_y - total number of regs
_nc_burn(u3nc_prog* pog_u, u3_noun* args, c3_y len_y, c3_y tot_y, c3_ys mov, c3_ys off)
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
  _nc_push_args(mov, off, tot_y, len_y, args);

#ifdef VERBOSE_BYTECODE
  #define BURN() fprintf(stderr, "%s ", opcode_names[pog[ip_w]]); goto *lab[pog[ip_w++]]
#else
  #define BURN() goto *lab[pog[ip_w++]]
#endif

#define BYTE()  ( pog[ip_w++] )
#define SHOT()  ( _nc_resh(pog, &ip_w) )
#define WORD()  ( _nc_rewo(pog, &ip_w) )
#define PEEK(R) (_nc_peek(mov, off, R))

  BURN();
  {
    do_imm: {
      c3_s i_s = SHOT();
      _nc_put(_nc_peek(mov, off, BYTE()), u3k(pog_u->lit_u.non[i_s]));
      BURN();
    }

    do_mov: {
      c3_y s_y = BYTE(), d_y = BYTE();
      _nc_put(PEEK(d_y), u3k(*PEEK(s_y)));
      BURN();
    }

    do_inc: {
      c3_y s_y = BYTE(), d_y = BYTE();
      _nc_put(PEEK(d_y), u3i_vint(u3k(*PEEK(s_y))));
      BURN();
    }

    do_con: {
      c3_y h_y = BYTE(),
           t_y = BYTE(),
           d_y = BYTE();
      _nc_put(PEEK(d_y), u3nc(u3k(*PEEK(h_y)), u3k(*PEEK(h_y))));
      BURN();
    }

    do_hed: {
      c3_y s_y = BYTE(), d_y = BYTE();
      _nc_put(PEEK(d_y), u3k(u3h(*PEEK(s_y))));
      BURN();
    }

    do_tal: {
      c3_y s_y = BYTE(), d_y = BYTE();
      _nc_put(PEEK(d_y), u3k(u3t(*PEEK(s_y))));
      BURN();
    }

    do_cel: {
      if ( c3n == u3a_is_cell(*PEEK(BYTE())) ) {
        u3m_bail(c3__exit);
      }
      BURN();
    }

    do_his: {
      c3_s hin_s = SHOT(), fol_s = SHOT();
      static_prologue(pog_u->lit_u.non[hin_s], pog_u->lit_u.non[fol_s]);
      BURN();
    }

    do_hos: {
      c3_s hin_s = SHOT(), fol_s = SHOT();
      static_epilogue(pog_u->lit_u.non[hin_s], pog_u->lit_u.non[fol_s]);
      BURN();
    }

    do_hid: {
      c3_s hin_s = SHOT();
      c3_y clu_y = BYTE();
      c3_s fol_s = SHOT();
      dynamic_prologue(pog_u->lit_u.non[hin_s], pog_u->lit_u.non[fol_s], *PEEK(clu_y));
      BURN();
    }

    do_hod: {
      c3_s hin_s = SHOT();
      c3_y clu_y = BYTE();
      c3_s fol_s = SHOT();
      dynamic_epilogue(pog_u->lit_u.non[hin_s], pog_u->lit_u.non[fol_s], *PEEK(clu_y));
      BURN();
    }

    do_spy: {
      c3_y ref_y = BYTE(),
           pax_y = BYTE(),
           des_y = BYTE();
      u3_noun x = u3m_soft_esc(u3k(*PEEK(ref_y)), u3k(*PEEK(pax_y)));
      if ( c3n == u3du(x) ) {
        u3m_bail(u3nc(1, *PEEK(pax_y)));
      }
      else if ( c3n == u3du(u3t(x)) ) {
        u3t_push(u3nt(c3__hunk, *PEEK(ref_y), *PEEK(pax_y)));
        u3m_bail(c3__exit);
      }
      else {
        _nc_put(PEEK(des_y), u3k(u3t(u3t(x))));
        u3z(x);
        BURN();
      }
    }

    do_mem: {
      c3_y sub_y  = BYTE();
      c3_s sot_s  = SHOT();
      c3_y res_y  = BYTE();
      u3nc_memo* mem_u = &pog_u->mem_u.sot_u[sot_s];
      u3_noun key = u3nc(u3k(*PEEK(sub_y)), u3k(mem_u->key));
      if ( u3z_memo_ford == mem_u->cid ) {
        u3z_save_m(mem_u->cid, 136 + c3__ford, key, *PEEK(res_y));
      }
      else if ( ( u3z_memo_toss == mem_u->cid )
          ? ( &(u3H->rod_u) != u3R )
          : ( 0 == u3R->ski.gul ) ) {
        u3z_save_m(mem_u->cid, 144 + c3__nock, key, *PEEK(res_y));
      }
      u3z(key);
      BURN();
    }

    do_cal: {
      c3_s dir_s = SHOT();
      c3_y des_y = BYTE();
      u3nc_dire* dir_u = &pog_u->dir_u.dat_u[dir_s];
      u3_noun args[dir_u->len_y];
      for (c3_s i_s = 0; i_s < dir_u->len_y; i_s++) {
        args[i_s] = u3k(*PEEK(i_s));
      }
      if ( dir_u->ham_u ) {
        u3_weak res = dir_u->ham_u(args, dir_u->len_y);
        if ( u3_none != res ) {
          _nc_put(PEEK(des_y), res);
          for (c3_y i_y = 0; i_y < dir_u->len_y; i_y++) {
            u3z(args[i_y]);
          }
          BURN();
        }
      }
      fam         = u3to(nc_burnframe, u3R->cap_p) + off + mov;
      u3R->cap_p  = u3of(nc_burnframe, fam - off);

      fam->ip_w   = ip_w;
      fam->pog_u  = pog_u;
      fam->tar_y  = des_y;
      fam->tot_y  = tot_y;

      pog_u = u3to(u3nc_prog, dir_u->pog_p);
      pog   = pog_u->byc_u.ops_y;
      ip_w  = 0;
      tot_y = dir_u->tot_y;

      _nc_push_args(mov, off, dir_u->tot_y, dir_u->len_y, args);
      BURN();
    }

    do_lnk: {
      c3_y sub_y = BYTE(),
           fol_y = BYTE(),
           des_y = BYTE();
      _nc_put(PEEK(des_y), u3n_nock_on(*PEEK(sub_y), *PEEK(fol_y)));
      BURN();
    }

    do_clq: {
      c3_y som_y = BYTE();
      c3_w sip_w = WORD();
      if ( c3n == u3a_is_cell(*PEEK(som_y)) ) {
        ip_w += sip_w;
      }
      BURN();
    }

    do_eqq: {
      c3_y one_y = BYTE(), two_y = BYTE();
      c3_w sip_w = WORD();
      if ( c3n == u3r_sing(*PEEK(one_y), *PEEK(two_y)) ) {
        ip_w += sip_w;
      }
      BURN();
    }

    do_brn: {
      c3_y som_y = BYTE();
      c3_w sip_w = WORD();
      if ( c3n == u3x_loob(*PEEK(som_y)) ) {
        ip_w += sip_w;
      }
      BURN();
    }

    do_adv: {
      ip_w += WORD();
      BURN();
    }

    do_lnt: {
      c3_y sub_y = BYTE(),
           fol_y = BYTE();
      pro = u3n_nock_on(*PEEK(sub_y), *PEEK(fol_y));
      goto done_out;
    }

    do_jmp: {
      c3_s dir_s = SHOT();
      u3nc_dire* dir_u = &pog_u->dir_u.dat_u[dir_s];
      u3_noun args[dir_u->len_y];
      for (c3_s i_s = 0; i_s < dir_u->len_y; i_s++) {
        args[i_s] = u3k(*PEEK(i_s));
      }
      
      if ( dir_u->ham_u ) {
        pro = dir_u->ham_u(args, dir_u->len_y);
        if ( u3_none != pro ) {
          goto done_out;
        }
      }

      for ( c3_y i_y = 0; i_y < tot_y; i_y++ ) {
        if ( u3_none != *PEEK(i_y) ) u3z(*PEEK(i_y));
      }
      u3R->cap_p -= (mov * tot_y);
      
      pog_u = u3to(u3nc_prog, dir_u->pog_p);
      pog   = pog_u->byc_u.ops_y;
      ip_w  = 0;
      tot_y = dir_u->tot_y;

      _nc_push_args(mov, off, dir_u->tot_y, dir_u->len_y, args);
      BURN();
    }

    do_don: {
      pro = u3k(*PEEK(BYTE()));
      goto done_out;
    }

    do_dom: {
      pro = u3k(pog_u->lit_u.non[SHOT()]);
      goto done_out;
    }
    
    done_out: {
      u3_assert(u3_none != pro);
      for ( c3_y i_y = 0; i_y < tot_y; i_y++ ) {
        if ( u3_none != *PEEK(i_y) ) u3z(*PEEK(i_y));
      }
      u3R->cap_p -= (mov * tot_y);
      if ( empty == u3R->cap_p ) {
        return pro;
      }
      fam        = u3to(nc_burnframe, u3R->cap_p) + off;
      u3R->cap_p = u3of(nc_burnframe, fam - (mov+off));

      pog_u = fam->pog_u;
      pog   = pog_u->byc_u.ops_y;
      ip_w  = fam->ip_w;
      tot_y = fam->tot_y;
      _nc_put(PEEK(fam->tar_y), pro);
      BURN();
    }

    do_bom: {
      u3m_bail(c3__exit);
    }

    do_mim: {
      c3_s sot_s = SHOT();
      c3_y sub_y = BYTE();
      c3_y reg_y = BYTE();
      c3_w sip_w = WORD();

      u3nc_memo* mem_u = &pog_u->mem_u.sot_u[sot_s];
      u3_noun key = u3nc(u3k(*PEEK(sub_y)), u3k(mem_u->key));
      u3_weak res = u3_none;
      switch ( mem_u->cid ) {
        case u3z_memo_ford: {
          res = u3z_find_m(mem_u->cid, 136 + c3__ford, key);
        } break;
        default: {
          res = u3z_find_m(mem_u->cid, 144 + c3__nock, key);
        }
      }
      if ( u3_none != res ) {
        _nc_put(PEEK(reg_y), res);
      }
      else {
        ip_w += sip_w;
      }
      BURN();
    }
  }
}