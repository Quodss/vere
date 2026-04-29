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

static inline void
_nc_riby(c3_y** buf, c3_y a_y)
{
  **buf = a_y;
  *buf += 1;
}

static inline void
_nc_rish(c3_y** buf, c3_s a_s)
{
  _nc_riby(buf, a_s & 0xff);
  _nc_riby(buf, a_s >> 8);
}

static inline void
_nc_riwo(c3_y** buf, c3_w a_w)
{
  _nc_rish(buf, a_w & 0xffff);
  _nc_rish(buf, a_w >> 16);
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

#define BYTE()  ( pog[ip_w++] )
#define SHOT()  ( _nc_resh(pog, &ip_w) )
#define WORD()  ( _nc_rewo(pog, &ip_w) )
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
      c3_s i_s = SHOT();
      c3_y d_y = BYTE();
      _nc_put(_nc_peek(mov, off, d_y), u3k(pog_u->lit_u.non[i_s]));
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
      if ( c3n == u3du(*PEEK(s_y)) )
      _nc_put(PEEK(d_y), u3k(HEAD(*PEEK(s_y))));
      BURN();
    }

    do_tal: {
      c3_y s_y = BYTE(), d_y = BYTE();
      _nc_put(PEEK(d_y), u3k(TAIL(*PEEK(s_y))));
      BURN();
    }

    do_cel: {
      if ( c3n == u3du(*PEEK(BYTE())) ) {
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
      dynamic_prologue(pog_u->lit_u.non[hin_s], pog_u->lit_u.non[fol_s],
        *PEEK(clu_y));
      BURN();
    }

    do_hod: {
      c3_s hin_s = SHOT();
      c3_y clu_y = BYTE();
      c3_s fol_s = SHOT();
      dynamic_epilogue(pog_u->lit_u.non[hin_s], pog_u->lit_u.non[fol_s],
        *PEEK(clu_y));
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
      c3_stub;
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

      pog_u = u3to(u3nc_prog, dir_u->pog_p);
      pog   = pog_u->byc_u.ops_y;
      ip_w  = 0;

      _nc_push_args(mov, off, pog_u->tot_y, dir_u->len_y, args);
      BURN();
    }

    do_lnk: {
      c3_y sub_y = BYTE(),
           fol_y = BYTE(),
           des_y = BYTE();
      _nc_put(PEEK(des_y), u3n_nock_on(u3k(*PEEK(sub_y)), u3k(*PEEK(fol_y))));
      BURN();
    }

    do_clq: {
      c3_y som_y = BYTE();
      c3_w sip_w = WORD();
      ip_w += ( c3y == u3a_is_cell(*PEEK(som_y)) ) ? 0 : sip_w;
      BURN();
    }

    do_eqq: {
      c3_y one_y = BYTE(), two_y = BYTE();
      c3_w sip_w = WORD();
      ip_w += ( c3y == u3r_sing(*PEEK(one_y), *PEEK(two_y)) ) ? 0 : sip_w;
      BURN();
    }

    do_brn: {
      c3_y som_y = BYTE();
      c3_w sip_w = WORD();
      ip_w += ( c3y == u3x_loob(*PEEK(som_y)) ) ? 0 : sip_w;
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
          for (c3_y i_y = 0; i_y < dir_u->len_y; i_y++) {
            u3z(args[i_y]);
          }
          goto done_out;
        }
      }

      POP_REGS();
      
      pog_u = u3to(u3nc_prog, dir_u->pog_p);
      pog   = pog_u->byc_u.ops_y;
      ip_w  = 0;

      _nc_push_args(mov, off, pog_u->tot_y, dir_u->len_y, args);
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

#define c3__clq  c3_s3('c', 'l', 'q')
#define c3__eqq  c3_s3('e', 'q', 'q')
#define c3__brn  c3_s3('b', 'r', 'n')
#define c3__mim  c3_s3('m', 'i', 'm')
#define c3__jmp  c3_s3('j', 'm', 'p')
#define c3__jmf  c3_s3('j', 'm', 'f')
#define c3__lnt  c3_s3('l', 'n', 't')
#define c3__don  c3_s3('d', 'o', 'n')
#define c3__dom  c3_s3('d', 'o', 'm')
#define c3__bom  c3_s3('b', 'o', 'm')
#define c3__imm  c3_s3('i', 'm', 'm')
#define c3__mov  c3_s3('m', 'o', 'v')
#define c3__hed  c3_s3('h', 'e', 'd')
#define c3__tal  c3_s3('t', 'a', 'l')
#define c3__cel  c3_s3('c', 'e', 'l')
#define c3__his  c3_s3('h', 'i', 's')
#define c3__hos  c3_s3('h', 'o', 's')
#define c3__hid  c3_s3('h', 'i', 'd')
#define c3__hod  c3_s3('h', 'o', 'd')
#define c3__spy  c3_s3('s', 'p', 'y')
#define c3__mem  c3_s3('m', 'e', 'm')
#define c3__lnk  c3_s3('l', 'n', 'k')
#define c3__cal  c3_s3('c', 'a', 'l')
#define c3__caf  c3_s3('c', 'a', 'f')

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
static void
_nc_table_add(u3_post har_p, u3_noun som)
{
  if ( u3_none == u3h_git(har_p, som) ) {
    u3h_put(har_p, som, u3i_word(u3h_wyt(har_p)));
  }
}

//  retains
static c3_w
_nc_table_get(u3_post har_p, u3_noun som)
{
  return u3r_word(0, u3x_good(u3h_git(har_p, som)));
}

// RETAINS
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
  while (u3_nul != ops) {
    u3_assert(c3y == u3r_cell(ops, &op, &ops));
    u3_assert(c3y == u3r_cell(op, &tag, &args));
    *ops_w += 1 + _n_arg(_nc_map_tag_cod(tag));
    switch ( tag ) {
      default: break;
      case c3__mim: {
        c3_stub;
        goto _branch;
      }
      case c3__clq: {
        ax_z = 6;
        ax_o = 7;
        goto _branch;
      }
      case c3__eqq: {
        ax_z = 14;
        ax_o = 15;
        goto _branch;
      }
      case c3__brn: {
        ax_z = 6;
        ax_o = 7;
        goto _branch;
      }
      _branch: {
        u3_assert(c3y == u3r_mean(args, {ax_z, &z}, {ax_o, &o}));
        c3_w off_1 = *ops_w;
        u3_noun sip_z = _nc_nouncode_measure(z, ops_w, lit_p, mem_w, arg_w, dir_w);
        *ops_w += 1 + _n_arg(ADV);
        c3_w off_2 = *ops_w;
        u3_noun sip_o = _nc_nouncode_measure(o, ops_w, lit_p, mem_w, arg_w, dir_w);
        c3_w off_3 = *ops_w;
        sip = u3kb_zing(u3nl(
          sip_o,
          u3nc(u3i_word(off_3 - off_2), u3_nul),
          sip_z,
          u3nc(u3i_word(off_2 - off_1), u3_nul),
          sip
        ));
      } break;

      case c3__dom: {
        _nc_table_add(lit_p, args);
      } break;

      case c3__imm: {
        _nc_table_add(lit_p, u3h(args));
      } break;

      case c3__his:
      case c3__hos: {
        _nc_table_add(lit_p, u3h(args));
        _nc_table_add(lit_p, u3t(args));
      } break;

      case c3__hid:
      case c3__hod: {
        _nc_table_add(lit_p, u3h(args));
        _nc_table_add(lit_p, u3t(u3t(args)));
      } break;

      case c3__mem: {
        c3_stub;
      } break;

      case c3__jmp: {
        dir_w += 1;
        *arg_w += u3r_word(0, u3qb_lent(u3t(args)));
      } break;

      case c3__jmf: {
        dir_w += 1;
        *arg_w += u3r_word(0, u3qb_lent(u3h(u3t(args))));
      } break;

      case c3__caf: {
        dir_w += 1;
        *arg_w += u3r_word(0, u3qb_lent(u3h(u3t(args))));
      } break;

      case c3__cal: {
        dir_w += 1;
        *arg_w += u3r_word(0, u3qb_lent(u3h(u3t(args))));
      } break;
    }
  }
  return sip;
}


//  retains
static void
_nc_write_dire(u3nc_dire* dir_u, c3_y** arg_y, u3_noun bell, u3_noun regs, u3_noun ring, u3_noun* queu)
{
  *queu = u3nc(u3k(bell), *queu);
  dir_u->arg_y = *arg_y;
  dir_u->bell  = u3k(bell);
  dir_u->len_y = u3r_word(0, u3qb_lent(regs));
  dir_u->ring  = u3k(ring);
  //  pog_p, is not filled yet, need to return the bell to the
  //  caller to add the bell to the worklist
  //  XX ham_u
  u3_noun r;
  while ( u3_nul != regs ) {
    u3_assert(c3y == u3r_cell(regs, &r, &regs));
    _nc_riby(arg_y, u3r_byte(0, r));
  }
}

static void
_nc_nouncode_write(u3_noun ops,
  u3_noun* sip,
  c3_y**      ops_y,
  u3_post     lit_p,
  u3nc_memo** mem_u,
  c3_y**      arg_y,
  u3nc_dire* dir_u,
  c3_s*      dir_s,
  u3_noun*   queu)
{
  #define WRITE_LIT(SOM) (_nc_rish(ops_y, _nc_table_get(lit_p, SOM)))
  #define WRITE_REG(SOM)  (_nc_riby(ops_y, u3r_byte(0, SOM)))
  u3_noun op, tag, args, z, o, s;
  c3_y ax_z, ax_o;
  while (u3_nul != ops) {
    u3_assert(c3y == u3r_cell(ops, &op, &ops));
    u3_assert(c3y == u3r_cell(op, &tag, &args));
    _nc_riby(ops_y, _nc_map_tag_cod(tag));
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
        _nc_riwo(ops_y, u3r_word(0, s));
        _nc_nouncode_write(z, sip, ops_y, lit_p, mem_u, arg_y, dir_u, dir_s, queu);
        _nc_riby(ops_y, ADV);
        u3_assert(c3y == u3r_cell(*sip, &s, sip));
        _nc_riwo(ops_y, u3r_word(0, s));
        _nc_nouncode_write(o, sip, ops_y, lit_p, mem_u, arg_y, dir_u, dir_s, queu);
      } break;
     
      case c3__dom: {
        WRITE_LIT(args);
      } break;

      case c3__imm: {
        _nc_rish(ops_y, _nc_table_get(lit_p, u3h(args)));
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
        _nc_rish(ops_y, *dir_s);
        u3_noun bell, regs;
        u3_assert(c3y == u3r_mean(args, {2, &bell}, {3, &regs}));
        _nc_write_dire(dir_u + *dir_s, arg_y, bell, regs, u3_nul, queu);
        (*dir_s)++;
      } break;

      case c3__jmf: {
        _nc_rish(ops_y, *dir_s);
        u3_noun bell, regs, ring;
        u3_assert(c3y == u3r_mean(args, {2, &bell}, {6, &regs}, {7, &ring}));
        _nc_write_dire(dir_u + *dir_s, arg_y, bell, regs, ring, queu);
        (*dir_s)++;
      } break;

      case c3__caf: {
        _nc_rish(ops_y, *dir_s);
        u3_noun bell, regs, ring, r;
        u3_assert(c3y == u3r_mean(args,
                                  {2, &bell},
                                  {6, &regs},
                                  {14, &r},
                                  {15, &ring})
        );
        WRITE_REG(r);
        _nc_write_dire(dir_u + *dir_s, arg_y, bell, regs, ring, queu);
        (*dir_s)++;
      } break;

      case c3__cal: {
        _nc_rish(ops_y, *dir_s);
        u3_noun bell, regs, r;
        u3_assert(c3y == u3r_mean(args,
                                  {2, &bell},
                                  {6, &regs},
                                  {7, &r})
        );
        WRITE_REG(r);
        _nc_write_dire(dir_u + *dir_s, arg_y, bell, regs, u3_nul, queu);
        (*dir_s)++;
      } break;
    }
  }
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
_nc_nouncode_build(u3_noun ops, u3_noun* queu)
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
  c3_w rog_w = siz_w = siz_w + ops_w;  // args
  c3_w non_w = siz_w = c3_align((siz_w + arg_w), sizeof(u3_noun), C3_ALGHI);  //  literals
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

  c3_y* arg_y = (c3_y*)pog_u + rog_w;

  for (c3_w i_w = 0; i_w < lit_w; i_w++) {
    pog_u->lit_u.non[i_w] = u3_none;
  }
  u3h_walk_with(lit_p, _nc_cb_copy, pog_u->lit_u.non);
  for (c3_w i_w = 0; i_w < lit_w; i_w++) {
    u3_assert(u3_none != pog_u->lit_u.non[i_w]);
  }
  c3_s dir_s = 0;
  _nc_nouncode_write(ops, &sip, &ops_y, lit_p, &mem_u, &arg_y, dir_u, &dir_s, queu);
  u3z(sip);
  u3h_free(lit_p);
  return pog_u;
}

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

u3nc_prog*
_n_bite_direct(u3_noun sock, u3_noun fol, u3_noun* queu, c3_t entry_t)
{
  u3_noun ops = u3d_bell_ops(u3nc(u3k(sock), u3k(fol)), entry_t);
  u3nc_prog* out_u = _nc_nouncode_build(ops, queu);
  u3z(ops);
  return out_u;
}

static c3_o
_n_find_direct(u3_noun sock_fol, u3_noun* queu, u3nc_prog** out_u)
{
  u3a_road* rod_u = u3R;
  u3_weak pog;
  while ( 1 ) {
    if ( u3_none != (pog = u3h_git(rod_u->byc_direct_p, sock_fol)) ) {
      *out_u = _nc_to_prog(pog);
      return c3n;
    }
    if ( !rod_u->par_p ) break;
    rod_u = u3to(u3a_road, rod_u->par_p);
  }
  *out_u = _n_bite_direct(u3h(sock_fol), u3t(sock_fol), queu, false);
  pog = _nc_of_prog(*out_u);
  u3h_put(u3R->byc_direct_p, sock_fol, pog);
  return c3y;
}

static u3_noun
_cb_jib_cons(u3_weak list, void* ptr_v)
{
  return u3nc(*(u3_noun*)ptr_v, ( u3_none == list ) ? u3_nul : list);
}

static void
_cb_fresh_rewrite(u3_noun kev)
{
  u3nc_prog* pog_u = _nc_to_prog(u3t(kev));
  u3nc_dire*    dir_u = pog_u->dir_u.dat_u;
  c3_w          len_w = pog_u->dir_u.len_w;
  u3_weak       gop = u3_none;
  u3a_road*     rod_u;

  for (c3_w i_w = 0; i_w < len_w; i_w++) {
    rod_u = u3R;
    while ( 1 ) {
      if ( u3_none != (gop = u3h_git(rod_u->byc_direct_p, dir_u[i_w].bell)) ) {
        //  uncompress loom offset
        //
        dir_u[i_w].pog_p = gop << u3a_vits;
        return;
      }
      u3_assert(rod_u->par_p);
      rod_u = u3to(u3a_road, rod_u->par_p);
    }
  }
}

u3nc_prog*
u3nc_build_entry_direct(u3_noun sock, u3_noun fol)
{
  u3_noun sock_fol = u3nc(u3k(sock), u3k(fol));
  u3_post fresh_p = u3h_new();
  u3_noun queu = u3_nul;
  u3nc_prog* out_u = _n_bite_direct(sock, fol, &queu, true);
  u3_noun pog = _nc_of_prog(out_u);
  u3_noun i_larp = u3nc(u3k(sock), pog);
  u3h_jib(u3R->byc_entry_p, fol, _cb_jib_cons, &i_larp);
  u3h_put(fresh_p, sock_fol, pog);
  u3z(sock_fol);

  u3nc_prog* pog_u;
  u3_noun t;
  while ( u3_nul != queu ) {
    u3_assert(c3y == u3r_cell(queu, &sock_fol, &t));
    u3k(sock_fol); u3k(t); u3z(queu); queu = t;

    if ( u3_none == u3h_git(fresh_p, sock_fol)
          && c3y == _n_find_direct(sock_fol, &queu, &pog_u) ) {
      u3h_put(fresh_p, sock_fol, _nc_of_prog(pog_u));
    }
    u3z(sock_fol);
  }

  u3h_walk(fresh_p, _cb_fresh_rewrite);
  u3h_free(fresh_p);

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