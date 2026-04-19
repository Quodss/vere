/// @file

#include "nock-compile.h"

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
  X(IMM, "imm", &&do_imm), /* c3_s, c3_y: index to literal array -> reg */                    \
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
  X(CLQ, "clq", &&do_clq), /* c3_y, c3_s: ?^ */                                       \
  X(EQQ, "eqq", &&do_eqq), /* c3_y[2], c3_s: .= */                                    \
  X(BRN, "brn", &&do_brn), /* c3_y, c3_s: ?: */                                       \
  X(LNT, "lnt", &&do_lnt), /* c3_y[2], Nock(u, f) */                            \
  X(JMP, "jmp", &&do_jmp), /* c3_s: dir */                                      \
  /* X(JMF, "jmf", &&do_jmf), same as jmp? */                                   \
  X(DON, "don", &&do_don), /* c3_y: return */                                   \
  X(DOM, "dom", &&do_dom), /* c3_s: lit */                                      \
  X(BOM, "bom", &&do_bom),                                                      \
  X(MIM, "mim", &&do_mim), /* c3_s, c3_y, c3_y, c3_s: check [sot sub], write to reg if available, else branch */\
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

    case CLQ: return sizeof(c3_y) + sizeof(c3_s);

    case EQQ: return sizeof(c3_y[2]) + sizeof(c3_s);

    case BRN: return sizeof(c3_y) + sizeof(c3_s);

    case LNK: return sizeof(c3_y[3]);

    case CAL: return sizeof(c3_s) + sizeof(c3_y);

    case LNT: return sizeof(c3_y[2]);

    case JMP: return sizeof(c3_s);
    case DON: return sizeof(c3_y);
    case DOM: return sizeof(c3_s);
    case BOM: return 0;
    case MIM: return sizeof(c3_s) + sizeof(c3_y[2]) + sizeof(c3_s);

    default:
      u3_assert( 0 );
  }
}

typedef struct __attribute__((__packed__)) {
  u3nc_prog* pog_u;
  c3_w     ip_w;
} burnframe;

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

static u3_noun
// len_y - number of input args, tot_y - total number of regs
_nc_burn(u3nc_prog* pog_u, u3_noun* args, c3_y len_y, c3_y tot_y, c3_ys mov, c3_ys off)
{
# define X(opcode, name, indirect_jump) indirect_jump
  static void* lab[] = { OPCODES };
# undef X

  u3nc_memo* mem_u;
  u3nc_dire* dir_u;
  c3_y *pog = pog_u->byc_u.ops_y;
  c3_w sip_w, ip_w = 0;
  u3_noun* top;
  u3_noun x, o;
  u3p(void) empty;
  burnframe* fam;

  (void)empty;

  empty = u3R->cap_p;
  for ( c3_y i_y = 0; i_y < tot_y; i_y++) {
    *_nc_peek(mov, off, i_y) = ( i_y < len_y ) ? args[i_y] : u3_none;
  }

#ifdef VERBOSE_BYTECODE
  #define BURN() fprintf(stderr, "%s ", opcode_names[pog[ip_w]]); goto *lab[pog[ip_w++]]
#else
  #define BURN() goto *lab[pog[ip_w++]]
#endif

  BURN();
  {
    do_imm: {
      c3_s i_s = _nc_resh(pog, &ip_w);
      _nc_put(_nc_peek(mov, off, pog[ip_w++]), pog_u->lit_u.non[i_s]);
      BURN();
    }

    do_mov:
      c3_stub;

    do_inc:
      c3_stub;

    do_con:
      c3_stub;

    do_hed:
      c3_stub;

    do_tal:
      c3_stub;

    do_cel:
      c3_stub;

    do_his:
      c3_stub;

    do_hos:
      c3_stub;

    do_hid:
      c3_stub;

    do_hod:
      c3_stub;

    do_spy:
      c3_stub;

    do_mem:
      c3_stub;

    do_cal:
      c3_stub;

    do_lnk:
      c3_stub;

    do_clq:
      c3_stub;

    do_eqq:
      c3_stub;

    do_brn:
      c3_stub;

    do_lnt:
      c3_stub;

    do_jmp:
      c3_stub;

    do_don:
      c3_stub;

    do_dom:
      c3_stub;

    do_bom:
      c3_stub;

    do_mim:
      c3_stub;
  }


}