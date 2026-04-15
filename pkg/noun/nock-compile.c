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
  X(IMM, "imm", &&do_imm), /* c3_s index to literal array */                                     \
  X(MOV, "mov", &&do_mov), /* c3_y[2], from -> to */                            \
  X(INC, "inc", &&do_inc), /* c3_y[2], arg -> prod */                                                      \
  X(CON, "con", &&do_con), /* c3_y[3], (hed, tel) -> prod */                                                     \
  X(HED, "hed", &&do_hed), /* c3_y[2], arg -> prod */                                                      \
  X(TAL, "tal", &&do_tal), /* c3_y[2], arg -> prod */                                                     \
  X(CEL, "cel", &&do_cel), /* c3_y */                                                     \
  X(HIS, "his", &&do_his), /* c3_s[2], hint, formula */                                                     \
  /*X(HYS, "hys", &&do_hys), */                                                     \
  X(HOS, "hos", &&do_hos), /* c3_s[2], hint, formula */                                                     \
  X(HID, "hid", &&do_hid), /* c3_s, c3_y, c3_s: hint, clue, formula */                                                      \
  /*X(HYD, "hyd", &&do_hyd), */                                                     \
  X(HOD, "hod", &&do_hod), /* c3_s, c3_y, c3_s: hint, clue, formula */                                                      \
  X(SPY, "spy", &&do_spy), /* c3_y[3], (ref, pax) -> out */                                                     \
  X(MEM, "mem", &&do_mem), /* c3_y, c3_s, c3_y: [sub sot(fol and cid) res] -> memo */                                                      \
  /* control-flow instructions */                                               \
  X(CLQ, "clq", &&do_clq), /* c3_y, ?^ */                                                     \
  X(EQQ, "eqq", &&do_eqq), /* c3_y[2], .= */                                                      \
  X(BRN, "brn", &&do_brn), /* c3_y, ?: */                                                     \
  X(LNK, "lnk", &&do_lnk), /* c3_y[3], Nock(u, f) -> d */                                                     \
  X(CAL, "cal", &&do_cal), /* c3_s, c3_y:  dir -> d */                                                     \
  /*  X(CAF, "caf", &&do_caf), same as cal? */                                                      \
  X(LNT, "lnt", &&do_lnt), /* c3_y[2], Nock(u, f) */                                                     \
  X(JMP, "jmp", &&do_jmp), /* c3_s: dir */                                                      \
  /* X(JMF, "jmf", &&do_jmf), same as jmp? */                                                      \
  X(DON, "don", &&do_don), /* c3_y: return */                                                     \
  X(DOM, "dom", &&do_dom), /* c3_s: lit */                                                      \
  X(BOM, "bom", &&do_bom),                                                      \
  X(MIM, "mim", &&do_mim), /* c3_s, c3_y, c3_y: check [sot sub], write to reg if available, else branch */                                                      \
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
    case IMM: return sizeof(c3_s);

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

    case CLQ: return sizeof(c3_y);

    case EQQ: return sizeof(c3_y[2]);

    case BRN: return sizeof(c3_y);

    case LNK: return sizeof(c3_y[3]);

    case CAL: return sizeof(c3_s) + sizeof(c3_y);

    case LNT: return sizeof(c3_y[2]);

    case JMP: return sizeof(c3_s);
    case DON: return sizeof(c3_y);
    case DOM: return sizeof(c3_s);
    case BOM: return 0;
    case MIM: return sizeof(c3_s) + sizeof(c3_y[2]);

    default:
      u3_assert( 0 );
  }
}


