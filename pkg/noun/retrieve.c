/// @file

#include "retrieve.h"

#include "allocate.h"
#include "hashtable.h"
#include "imprison.h"
#include "murmur3.h"
#include "trace.h"
#include "xtract.h"


//  declarations of inline functions
//
c3_o
u3r_cell(u3_noun a, u3_noun* b, u3_noun* c);
c3_o
u3r_trel(u3_noun a, u3_noun* b, u3_noun* c, u3_noun* d);
c3_o
u3r_qual(u3_noun  a,
         u3_noun* b,
         u3_noun* c,
         u3_noun* d,
         u3_noun* e);
c3_o
u3r_quil(u3_noun  a,
         u3_noun* b,
         u3_noun* c,
         u3_noun* d,
         u3_noun* e,
         u3_noun* f);
c3_o
u3r_hext(u3_noun  a,
         u3_noun* b,
         u3_noun* c,
         u3_noun* d,
         u3_noun* e,
         u3_noun* f,
         u3_noun* g);

/* _frag_word(): fast fragment/branch prediction for top word.
*/
static u3_weak
_frag_word(c3_w_tmp a_w, u3_noun b)
{
  u3_assert(0 != a_w);

  {
    c3_w_tmp dep_w = u3x_dep(a_w);

    while ( dep_w ) {
      if ( c3n == u3a_is_cell(b) ) {
        return u3_none;
      }
      else {
        u3a_cell* b_u = u3a_to_ptr(b);

        b = *(((u3_noun*)&(b_u->hed)) + (1 & (a_w >> (dep_w - 1))));
        dep_w--;
      }
    }
    return b;
  }
}

/* _frag_deep(): fast fragment/branch for deep words.
*/
static u3_weak
_frag_deep(c3_w_tmp a_w, u3_noun b)
{
  c3_w_tmp dep_w = 32;

  while ( dep_w ) {
    if ( c3n == u3a_is_cell(b) ) {
      return u3_none;
    }
    else {
      u3a_cell* b_u = u3a_to_ptr(b);

      b = *(((u3_noun*)&(b_u->hed)) + (1 & (a_w >> (dep_w - 1))));
      dep_w--;
    }
  }
  return b;
}

/* u3r_at():
**
**   Return fragment (a) of (b), or u3_none if not applicable.
*/
u3_weak
u3r_at(u3_atom a, u3_noun b)
{
  u3_assert(u3_none != a);
  u3_assert(u3_none != b);

  u3t_on(far_o);

  if ( 0 == a ) {
    u3t_off(far_o);
    return u3_none;
  }

  if ( _(u3a_is_cat(a)) ) {
#ifndef VERE_64
    u3t_off(far_o);
    return _frag_word(a, b);
#else
    b = _frag_word((a >> 32), b);
    u3t_off(far_o);
    if ( u3_none == b ) {
      return b;
    }
    return _frag_deep((a & 0xffffffff), b);
#endif
  }
  else {
    if ( !_(u3a_is_pug(a)) ) {
      u3t_off(far_o);
      return u3_none;
    }
    else {
      u3a_atom* a_u = u3a_to_ptr(a);
      c3_n len_n      = a_u->len_n;

      b = _frag_word(a_u->buf_w[len_n - 1], b);
      len_n -= 1;

      if ( u3_none == b ) {
        u3t_off(far_o);
        return b;
      }

      while ( len_n ) {
        b = _frag_deep(a_u->buf_w[len_n - 1], b);

        if ( u3_none == b ) {
          u3t_off(far_o);

          return b;
        } else {
          len_n--;
        }
      }
      u3t_off(far_o);

      return b;
    }
  }
}

/* u3r_mean():
**
**   Attempt to deconstruct `a` by axis, noun pairs; 0 terminates.
**   Axes must be sorted in tree order.
*/
  struct _mean_pair {
    c3_n    axe_n;
    u3_noun* som;
  };

  static c3_n
  _mean_cut(c3_n               len_n,
            struct _mean_pair* prs_m)
  {
    c3_n i_n, cut_n;
    c3_t cut_t;

    cut_t = 0;
    cut_n = 0;
    for ( i_n = 0; i_n < len_n; i_n++ ) {
      c3_n axe_n = prs_m[i_n].axe_n;

      if ( (cut_t == 0) && (3 == u3x_cap(axe_n)) ) {
        cut_t = 1;
        cut_n = i_n;
      }
      prs_m[i_n].axe_n = u3x_mas(axe_n);
    }
    return cut_t ? cut_n : i_n;
  }

  static c3_o
  _mean_extract(u3_noun            som,
                c3_n               len_n,
                struct _mean_pair* prs_m)
  {
    if ( len_n == 0 ) {
      return c3y;
    }
    else if ( (len_n == 1) && (1 == prs_m[0].axe_n) ) {
      *prs_m->som = som;
      return c3y;
    }
    else {
      if ( c3n == u3a_is_cell(som) ) {
        return c3n;
      } else {
        c3_n cut_n = _mean_cut(len_n, prs_m);

        return c3a
          (_mean_extract(u3a_h(som), cut_n, prs_m),
           _mean_extract(u3a_t(som), (len_n - cut_n), (prs_m + cut_n)));
      }
    }
  }

c3_o
u3r_vmean(u3_noun som, va_list ap)
{
  va_list            aq;
  c3_n               len_n;
  struct _mean_pair* prs_m;

  u3_assert(u3_none != som);

  //  traverse copy of va_list for alloca
  //
  va_copy(aq, ap);
  len_n = 0;

  while ( 1 ) {
    if ( 0 == va_arg(aq, c3_n) ) {
      break;
    }
    va_arg(aq, u3_noun*);
    len_n++;
  }

  va_end(aq);

  u3_assert( 0 != len_n );
  prs_m = alloca(len_n * sizeof(struct _mean_pair));

  //  traverse va_list and extract args
  //
  {
    c3_n i_n;

    for ( i_n = 0; i_n < len_n; i_n++ ) {
      prs_m[i_n].axe_n = va_arg(ap, c3_n);
      prs_m[i_n].som = va_arg(ap, u3_noun*);
    }

    va_end(ap);
  }

  //  extract axis from som
  //
  return _mean_extract(som, len_n, prs_m);
}

c3_o
u3r_mean(u3_noun som, ...)
{
  c3_o    ret_o;
  va_list ap;

  va_start(ap, som);
  ret_o = u3r_vmean(som, ap);
  va_end(ap);

  return ret_o;
}

//  stack frame for tracking noun comparison and unification
//
//    we always compare arbitrary nouns in a none-frame.
//    when we compare two cells, we change the none-frame to a head-frame
//    and push a new none-frame for their heads. if the heads are equal,
//    we get the cells from the head-frame and unify their head pointers.
//    then, we convert the head-frame to a tail-frame and repeat with
//    the tails, mutatis mutandis.
//
//    in Hoon, this structure would be:
//
//    $%  [%none a=* b=*]
//        [%head a=^ b=^]
//        [%tail a=^ b=^]
//    ==
//
#define SING_NONE 0
#define SING_HEAD 1
#define SING_TAIL 2

typedef struct {
  c3_y     sat_y;
  u3_noun  a;
  u3_noun  b;
} eqframe;

/* _cr_sing_push(): push a new stack frame, initialized as SING_NONE.
*/
static inline eqframe*
_cr_sing_push(u3a_pile* pil_u, u3_noun a, u3_noun b)
{
  eqframe* fam_u = u3a_push(pil_u);
  fam_u->sat_y   = SING_NONE;
  fam_u->a       = a;
  fam_u->b       = b;
  return fam_u;
}

/* _cr_sing_mug(): short-circuit comparison if mugs are present and not equal.
*/
static inline c3_o
_cr_sing_mug(u3a_noun* a_u, u3a_noun* b_u)
{
  c3_dessert((a_u->mug_n >> 31) == 0 && (b_u->mug_n >> 31) == 0);

  if ( a_u->mug_n && b_u->mug_n && (a_u->mug_n != b_u->mug_n) ) {
    return c3n;
  }

  return c3y;
}

/* _cr_sing_atom(): check if atom [a] is indirect and equal to noun [b]
*/
static inline c3_o
_cr_sing_atom(u3_atom a, u3_noun b)
{
  //  [a] is an atom, not pointer-equal to noun [b].
  //  if they're not both indirect atoms, they can't be equal.
  //
  if (  (c3n == u3a_is_pug(a))
     || (c3n == u3a_is_pug(b)) )
  {
    return c3n;
  }
  else {
    u3a_atom* a_u = u3a_to_ptr(a);
    u3a_atom* b_u = u3a_to_ptr(b);

    //  [a] and [b] are not equal if their mugs are present and not equal.
    //
    if ( c3n == _cr_sing_mug((u3a_noun*)a_u, (u3a_noun*)b_u) ) {
      return c3n;
    }
    else {
      c3_n a_n = a_u->len_n;
      c3_n b_n = b_u->len_n;

      //  [a] and [b] are not equal if their lengths are not equal
      //
      if ( a_n != b_n ) {
        return c3n;
      }
      else {
        c3_n i_n;

        //  XX memcmp
        //
        for ( i_n = 0; i_n < a_n; i_n++ ) {
          if ( a_u->buf_w[i_n] != b_u->buf_w[i_n] ) {
            return c3n;
          }
        }
      }
    }
  }

  return c3y;
}

/* _cr_sing_cape_test(): check for previous comparison of [a] and [b].
*/
static inline c3_o
_cr_sing_cape_test(u3p(u3h_root) har_p, u3_noun a, u3_noun b)
{
  u3_noun key = u3nc(u3a_to_off(a), u3a_to_off(b));
  u3_noun val;

  u3t_off(euq_o);
  val = u3h_git(har_p, key);
  u3t_on(euq_o);

  u3z(key);
  return ( u3_none != val ) ? c3y : c3n;
}

/* _cr_sing_cape_keep(): store [a] and [b] to short-circuit subsequent tests.
**                   NB: [a] and [b] (which MUST be equal nouns)
**                       are cons'd as offsets (direct atoms) to avoid refcount churn.
*/
static inline void
_cr_sing_cape_keep(u3p(u3h_root) har_p, u3_noun a, u3_noun b)
{
  //  only store if [a] and [b] are copies of each other
  //
  if ( a != b ) {
    u3_noun key = u3nc(u3a_to_off(a), u3a_to_off(b));
    u3t_off(euq_o);
    u3h_put(har_p, key, c3y);
    u3t_on(euq_o);
    u3z(key);
  }
}

/* _cr_sing_cape(): unifying equality with comparison deduplication
 *                  (tightly coupled to _cr_sing)
 */
static c3_o
_cr_sing_cape(u3a_pile* pil_u, u3p(u3h_root) har_p)
{
  eqframe* fam_u = u3a_peek(pil_u);
  u3_noun   a, b;
  u3a_cell* a_u;
  u3a_cell* b_u;

  //  loop while arguments remain on the stack
  //
  do {
    a = fam_u->a;
    b = fam_u->b;

    switch ( fam_u->sat_y ) {

      //  [a] and [b] are arbitrary nouns
      //
      case SING_NONE: {
        if ( a == b ) {
          break;
        }
        else if ( c3y == u3a_is_atom(a) ) {
          if ( c3n == _cr_sing_atom(a, b) ) {
            return c3n;
          }
          else {
            break;
          }
        }
        else if ( c3y == u3a_is_atom(b) ) {
          return c3n;
        }
        //  [a] and [b] are cells
        //
        else {
          a_u = u3a_to_ptr(a);
          b_u = u3a_to_ptr(b);

          //  short-circuiting mug check
          //
          if ( c3n == _cr_sing_mug((u3a_noun*)a_u, (u3a_noun*)b_u) ) {
            return c3n;
          }
          //  short-circuiting re-comparison check
          //
          else if ( c3y == _cr_sing_cape_test(har_p, a, b) ) {
            fam_u = u3a_pop(pil_u);
            continue;
          }
          //  upgrade none-frame to head-frame, check heads
          //
          else {
            fam_u->sat_y = SING_HEAD;
            fam_u = _cr_sing_push(pil_u, a_u->hed, b_u->hed);
            continue;
          }
        }
      } break;

      //  cells [a] and [b] have equal heads
      //
      case SING_HEAD: {
        a_u = u3a_to_ptr(a);
        b_u = u3a_to_ptr(b);
        u3a_wed(&(a_u->hed), &(b_u->hed));

        //  upgrade head-frame to tail-frame, check tails
        //
        fam_u->sat_y = SING_TAIL;
        fam_u = _cr_sing_push(pil_u, a_u->tel, b_u->tel);
        continue;
      }

      //  cells [a] and [b] are equal
      //
      case SING_TAIL: {
        a_u = u3a_to_ptr(a);
        b_u = u3a_to_ptr(b);
        u3a_wed(&(a_u->tel), &(b_u->tel));
      } break;

      default: {
        u3_assert(0);
      } break;
    }

    //  track equal pairs to short-circuit possible (re-)comparison
    //
    _cr_sing_cape_keep(har_p, a, b);

    fam_u = u3a_pop(pil_u);
  }
  while ( c3n == u3a_pile_done(pil_u) );

  return c3y;
}

/* _cr_sing(): unifying equality.
*/
static c3_o
_cr_sing(u3_noun a, u3_noun b)
{
  c3_s     ovr_s = 0;
  u3a_cell*  a_u;
  u3a_cell*  b_u;
  eqframe* fam_u;
  u3a_pile pil_u;

  //  initialize stack control, push arguments onto the stack (none-frame)
  //
  u3a_pile_prep(&pil_u, sizeof(eqframe));
  fam_u = _cr_sing_push(&pil_u, a, b);

  //  loop while arguments are on the stack
  //
  while ( c3n == u3a_pile_done(&pil_u) ) {
    a = fam_u->a;
    b = fam_u->b;

    switch ( fam_u->sat_y ) {

      //  [a] and [b] are arbitrary nouns
      //
      case SING_NONE: {
        if ( a == b ) {
          break;
        }
        else if ( c3y == u3a_is_atom(a) ) {
          if ( c3n == _cr_sing_atom(a, b) ) {
            u3R->cap_p = pil_u.top_p;
            return c3n;
          }
          else {
            break;
          }
        }
        else if ( c3y == u3a_is_atom(b) ) {
          u3R->cap_p = pil_u.top_p;
          return c3n;
        }
        //  [a] and [b] are cells
        //
        else {
          a_u = u3a_to_ptr(a);
          b_u = u3a_to_ptr(b);

          //  short-circuiting mug check
          //
          if ( c3n == _cr_sing_mug((u3a_noun*)a_u, (u3a_noun*)b_u) ) {
            u3R->cap_p = pil_u.top_p;
            return c3n;
          }
          //  upgrade none-frame to head-frame, check heads
          //
          else {
            fam_u->sat_y = SING_HEAD;
            fam_u = _cr_sing_push(&pil_u, a_u->hed, b_u->hed);
            continue;
          }
        }
      } break;

      //  cells [a] and [b] have equal heads
      //
      case SING_HEAD: {
        a_u = u3a_to_ptr(a);
        b_u = u3a_to_ptr(b);
        u3a_wed(&(a_u->hed), &(b_u->hed));

        //  upgrade head-frame to tail-frame, check tails
        //
        fam_u->sat_y = SING_TAIL;
        fam_u = _cr_sing_push(&pil_u, a_u->tel, b_u->tel);
        continue;
      }

      //  cells [a] and [b] are equal
      //
      case SING_TAIL: {
        a_u = u3a_to_ptr(a);
        b_u = u3a_to_ptr(b);
        u3a_wed(&(a_u->tel), &(b_u->tel));
      } break;

      default: {
        u3_assert(0);
      } break;
    }

    //  [ovr_s] counts comparisons, if it overflows, we've likely hit
    //  a pathological case (highly duplicated tree), so we de-duplicate
    //  subsequent comparisons by maintaining a set of equal pairs.
    //
    if ( 0 == ++ovr_s ) {
      u3p(u3h_root) har_p = u3h_new();
      c3_o ret_o = _cr_sing_cape(&pil_u, har_p);
      u3h_free(har_p);
      u3R->cap_p = pil_u.top_p;
      return ret_o;
    }

    fam_u = u3a_pop(&pil_u);
  }

  return c3y;
}

/* u3r_sing(): Yes iff [a] and [b] are the same noun.
*/
c3_o
u3r_sing(u3_noun a, u3_noun b)
{
  c3_o ret_o;
  u3t_on(euq_o);
  ret_o = _cr_sing(a, b);
  u3t_off(euq_o);
  return ret_o;
}

c3_o
u3r_fing(u3_noun a,
           u3_noun b)
{
  return (a == b) ? c3y : c3n;
}

/* u3r_sing_cell():
**
**   Yes iff `[p q]` and `b` are the same noun.
*/
c3_o
u3r_sing_cell(u3_noun p,
                u3_noun q,
                u3_noun b)
{
  return c3a(_(u3a_is_cell(b)),
                c3a(u3r_sing(p, u3a_h(b)),
                       u3r_sing(q, u3a_t(b))));
}
c3_o
u3r_fing_cell(u3_noun p,
                u3_noun q,
                u3_noun b)
{
  return c3a(_(u3a_is_cell(b)),
                c3a(u3r_fing(p, u3a_h(b)),
                       u3r_fing(q, u3a_t(b))));
}

/* u3r_sing_mixt():
**
**   Yes iff `[p q]` and `b` are the same noun.
*/
c3_o
u3r_sing_mixt(const c3_c* p_c,
                u3_noun     q,
                u3_noun     b)
{
  return c3a(_(u3a_is_cell(b)),
                c3a(u3r_sing_c(p_c, u3a_h(b)),
                       u3r_sing(q, u3a_t(b))));
}
c3_o
u3r_fing_mixt(const c3_c* p_c,
                u3_noun     q,
                u3_noun     b)
{
  return c3a(_(u3a_is_cell(b)),
                c3a(u3r_sing_c(p_c, u3a_h(b)),
                       u3r_fing(q, u3a_t(b))));
}

/* u3r_sing_trel():
**
**   Yes iff `[p q r]` and `b` are the same noun.
*/
c3_o
u3r_sing_trel(u3_noun p,
                u3_noun q,
                u3_noun r,
                u3_noun b)
{
  return c3a(_(u3a_is_cell(b)),
                c3a(u3r_sing(p, u3a_h(b)),
                       u3r_sing_cell(q, r, u3a_t(b))));
}
c3_o
u3r_fing_trel(u3_noun p,
                u3_noun q,
                u3_noun r,
                u3_noun b)
{
  return c3a(_(u3a_is_cell(b)),
                c3a(u3r_fing(p, u3a_h(b)),
                       u3r_fing_cell(q, r, u3a_t(b))));
}

/* u3r_sing_qual():
**
**   Yes iff `[p q r]` and `b` are the same noun.
*/
c3_o
u3r_sing_qual(u3_noun p,
                u3_noun q,
                u3_noun r,
                u3_noun s,
                u3_noun b)
{
  return c3a(_(u3a_is_cell(b)),
                c3a(u3r_sing(p, u3a_h(b)),
                       u3r_sing_trel(q, r, s, u3a_t(b))));
}
c3_o
u3r_fing_qual(u3_noun p,
                u3_noun q,
                u3_noun r,
                u3_noun s,
                u3_noun b)
{
  return c3a(_(u3a_is_cell(b)),
                c3a(u3r_fing(p, u3a_h(b)),
                       u3r_fing_trel(q, r, s, u3a_t(b))));
}

/* u3r_nord():
**
**   Return 0, 1 or 2 if `a` is below, equal to, or above `b`.
*/
u3_atom
u3r_nord(u3_noun a,
        u3_noun b)
{
  u3_assert(u3_none != a);
  u3_assert(u3_none != b);

  if ( a == b ) {
    return 1;
  }
  else {
    if ( _(u3a_is_atom(a)) ) {
      if ( !_(u3a_is_atom(b)) ) {
        return 0;
      } else {
        if ( _(u3a_is_cat(a)) ) {
          if ( _(u3a_is_cat(b)) ) {
            return (a < b) ? 0 : 2;
          }
          else return 0;
        }
        else if ( _(u3a_is_cat(b)) ) {
          return 2;
        }
        else {
          u3a_atom* a_u = u3a_to_ptr(a);
          u3a_atom* b_u = u3a_to_ptr(b);

          c3_n n_rez = a_u->len_n;
          c3_n n_mox = b_u->len_n;

          if ( n_rez != n_mox ) {
            return (n_rez < n_mox) ? 0 : 2;
          }
          else {
            c3_n i_n;

            for ( i_n = 0; i_n < n_rez; i_n++ ) {
              c3_w_tmp ai_w = a_u->buf_w[i_n];
              c3_w_tmp bi_w = b_u->buf_w[i_n];

              if ( ai_w != bi_w ) {
                return (ai_w < bi_w) ? 0 : 2;
              }
            }
            return 1;
          }
        }
      }
    } else {
      if ( _(u3a_is_atom(b)) ) {
        return 2;
      } else {
        u3_atom c = u3r_nord(u3a_h(a), u3a_h(b));

        if ( 1 == c ) {
          return u3r_nord(u3a_t(a), u3a_t(b));
        } else {
          return c;
        }
      }
    }
  }
}

/* u3r_sing_c(): cord/C-string value equivalence.
*/
c3_o
u3r_sing_c(const c3_c* a_c,
           u3_noun     b)
{
  u3_assert(u3_none != b);

  if ( !_(u3a_is_atom(b)) ) {
    return c3n;
  }
  else {
    c3_n n_sof = strlen(a_c);
    c3_n i_n;

    if ( n_sof != u3r_met(3, b) ) {
      return c3n;
    }
    for ( i_n = 0; i_n < n_sof; i_n++ ) {
      if ( u3r_byte(i_n, b) != a_c[i_n] ) {
        return c3n;
      }
    }
    return c3y;
  }
}

/* u3r_bush():
**
**   Factor [a] as a bush [b.[p q] c].
*/
c3_o
u3r_bush(u3_noun  a,
           u3_noun* b,
           u3_noun* c)
{
  u3_assert(u3_none != a);

  if ( _(u3a_is_atom(a)) ) {
    return c3n;
  }
  else {
    *b = u3a_h(a);

    if ( _(u3a_is_atom(*b)) ) {
      return c3n;
    } else {
      *c = u3a_t(a);
      return c3y;
    }
  }
}

/* u3r_bite(): retrieve/default $bloq and $step from $bite.
*/
c3_o
u3r_bite(u3_noun bite, u3_atom* bloq, u3_atom *step)
{
  u3_noun hed, tal;

  if ( c3n == u3r_cell(bite, &hed, &tal) ) {
    *bloq = bite;
    *step = 1;
    return c3y;
  }
  else if (  (c3n == u3a_is_atom(hed))
          || (c3n == u3a_is_atom(tal)) )
  {
    return c3n;
  }
  else {
    *bloq = hed;
    *step = tal;
    return c3y;
  }
}

/* u3r_p():
**
**   & [0] if [a] is of the form [b *c].
*/
c3_o
u3r_p(u3_noun  a,
        u3_noun  b,
        u3_noun* c)
{
  u3_noun feg, nux;

  if ( (c3y == u3r_cell(a, &feg, &nux)) &&
       (c3y == u3r_sing(feg, b)) )
  {
    if ( c ) *c = nux;
    return c3y;
  }
  else return c3n;
}

/* u3r_pq():
**
**   & [0] if [a] is of the form [b *c d].
*/
c3_o
u3r_pq(u3_noun  a,
         u3_noun  b,
         u3_noun* c,
         u3_noun* d)
{
  u3_noun nux;

  if ( (c3y == u3r_p(a, b, &nux)) &&
       (c3y == u3r_cell(nux, c, d)) )
  {
    return c3y;
  }
  else return c3n;
}

/* u3r_pqr():
**
**   & [0] if [a] is of the form [b *c *d *e].
*/
c3_o
u3r_pqr(u3_noun  a,
          u3_noun  b,
          u3_noun* c,
          u3_noun* d,
          u3_noun* e)
{
  u3_noun nux;

  if ( (c3y == u3r_p(a, b, &nux)) &&
       (c3y == u3r_trel(nux, c, d, e)) )
  {
    return c3y;
  }
  else return c3n;
}

/* u3r_pqrs():
**
**   & [0] if [a] is of the form [b *c *d *e *f].
*/
c3_o
u3r_pqrs(u3_noun  a,
           u3_noun  b,
           u3_noun* c,
           u3_noun* d,
           u3_noun* e,
           u3_noun* f)
{
  u3_noun nux;

  if ( (c3y == u3r_p(a, b, &nux)) &&
       (c3y == u3r_qual(nux, c, d, e, f)) )
  {
    return c3y;
  }
  else return c3n;
}

/* u3r_met():
**
**   Return the size of (b) in bits, rounded up to
**   (1 << a_y).
**
**   For example, (a_y == 3) returns the size in bytes.
**   NB: (a_y) must be < 37.  // note dozreg: still true with VERE_64?
*/
c3_n
u3r_met(c3_y  a_y,
        u3_atom b)
{
  c3_dessert(u3_none != b);
  c3_dessert(_(u3a_is_atom(b)));

  if ( b == 0 ) {
    return 0;
  }
  /* gal_n: number of words besides (daz_w) in (b).
  ** daz_w: top word in (b).
  */
  c3_n gal_n;
  c3_w_tmp daz_w;

  if ( _(u3a_is_cat(b)) ) {
    gal_n = 0;
    daz_w = b;
  }
  else {
    u3a_atom* b_u = u3a_to_ptr(b);

    gal_n = (b_u->len_n) - 1;
    daz_w = b_u->buf_w[gal_n];
  }

  /* 5 because 1<<2 bytes in c3_w, 1<<3 bits in byte.
     aka log2(CHAR_BIT * sizeof daz_w)
     a_y < 5 informs whether we shift return left or right
     */
  if (a_y < 5) {
    c3_y max_y = (1 << a_y) - 1;
    c3_y gow_y = 5 - a_y;

    if (gal_n > ((u3r_note_max - (32 + max_y)) >> gow_y))
      return u3m_bail(c3__fail);

    return (gal_n << gow_y)
      + ((c3_bits_word(daz_w) + max_y)
         >> a_y);
  }
  c3_y gow_y = (a_y - 5);
  return ((gal_n + 1) + ((1 << gow_y) - 1)) >> gow_y;
}

/* u3r_bit():
**
**   Return bit (a_n) of (b).
*/
c3_b
u3r_bit(c3_n    a_n,
          u3_atom b)
{
  u3_assert(u3_none != b);
  u3_assert(_(u3a_is_atom(b)));

  if ( _(u3a_is_cat(b)) ) {

# ifndef VERE_64
    if ( a_n >= 31 ) {
      return 0;
    }
# else
    if ( a_n >= 63 ) {
      return 0;
    }
# endif

    else return (1 & (b >> a_n));
  }
  else {
    u3a_atom* b_u   = u3a_to_ptr(b);
    c3_y        vut_y = (a_n & 31);
    c3_n        pix_n = (a_n >> 5);

    if ( pix_n >= b_u->len_n ) {
      return 0;
    }
    else {
      c3_w_tmp nys_w = b_u->buf_w[pix_n];

      return (1 & (nys_w >> vut_y));
    }
  }
}

/* u3r_byte():
**
**   Return byte (a_n) of (b).
*/
c3_y
u3r_byte(c3_n    a_n,
           u3_atom b)
{
  u3_assert(u3_none != b);
  u3_assert(_(u3a_is_atom(b)));

  if ( _(u3a_is_cat(b)) ) {
#ifndef VERE_64
    if ( a_n > 3 ) {
      return 0;
    }
#else
    if ( a_n > 7 ) {
      return 0;
    }
#endif
    else return (255 & (b >> (a_n << 3)));
  }
  else {
    u3a_atom* b_u   = u3a_to_ptr(b);
    c3_y      vut_y = (a_n & 3);
    c3_n      pix_n = (a_n >> 2);

    if ( pix_n >= b_u->len_n ) {
      return 0;
    }
    else {
      c3_w_tmp nys_w = b_u->buf_w[pix_n];

      return (255 & (nys_w >> (vut_y << 3)));
    }
  }
}

/* u3r_bytes():
**
**  Copy bytes (a_n) through (a_n + b_n - 1) from (d) to (c).
*/
void
u3r_bytes(c3_n    a_n,
            c3_n    b_n,
            c3_y*   c_y,
            u3_atom d)
{
  u3_assert(u3_none != d);
  u3_assert(_(u3a_is_atom(d)));

  if ( _(u3a_is_cat(d)) ) {
#ifndef VERE_64
    c3_w_tmp e_w = d >> (c3_min(a_n, 4) << 3);
    c3_w_tmp m_w = c3_min(b_n, 4);
    memcpy(c_y, (c3_y*)&e_w, m_w);
    if ( b_n > 4 ) {
      memset(c_y + 4, 0, b_n - 4);
    }
#else
    c3_d e_d = d >> (c3_min(a_n, 8) << 3);
    c3_w_tmp m_w = c3_min(b_n, 8);
    memcpy(c_y, (c3_y*)&e_d, m_w);
    if ( b_n > 8 ) {
       memset(c_y + 8, 0, b_n - 8);
    }
#endif
  }
  else {
    u3a_atom* d_u   = u3a_to_ptr(d);
    c3_n n_n = d_u->len_n << 2;
    c3_y* x_y = (c3_y*)d_u->buf_w + a_n;

    if ( a_n >= n_n ) {
      memset(c_y, 0, b_n);
    }
    else {
      c3_n z_n = c3_min(b_n, n_n - a_n);
      memcpy(c_y, x_y, z_n);
      if ( b_n > n_n - a_n ) {
        memset(c_y + z_n, 0, b_n + a_n - n_n);
      }
    }
  }
}

/* u3r_bytes_fit():
**
**  Copy (len_n) bytes of (a) into (buf_y) if it fits, returning overage
*/
c3_n
u3r_bytes_fit(c3_n len_n, c3_y *buf_y, u3_atom a)
{
  c3_n met_n = u3r_met(3, a);
  if ( met_n <= len_n ) {
    u3r_bytes(0, len_n, buf_y, a);
    return 0;
  }
  else {
    return len_n - met_n;
  }
}

/* u3r_bytes_alloc():
**
**  Copy (len_n) bytes starting at (a_n) from (b) into a fresh allocation.
*/
c3_y*
u3r_bytes_alloc(c3_n    a_n,
                c3_n    len_n,
                u3_atom b)
{
  c3_y* b_y = u3a_malloc(len_n);
  u3r_bytes(a_n, a_n + len_n, b_y, b);
  return b_y;
}

/* u3r_bytes_all():
**
**  Allocate and return a new byte array with all the bytes of (a),
**  storing the length in (len_n).
*/
c3_y*
u3r_bytes_all(c3_n* len_n, u3_atom a)
{
  c3_n met_n = *len_n = u3r_met(3, a);
  return u3r_bytes_alloc(0, met_n, a);
}

/* u3r_mp():
**
**   Copy (b) into (a_mp).
*/
void
u3r_mp(mpz_t   a_mp,
       u3_atom b)
{
  u3_assert(u3_none != b);
  u3_assert(_(u3a_is_atom(b)));

  if ( _(u3a_is_cat(b)) ) {
    mpz_init_set_ui(a_mp, b);
  }
  else {
    u3a_atom* b_u = u3a_to_ptr(b);
    c3_n    len_n = b_u->len_n;
    c3_d    bit_d = (c3_d)len_n << 5;

    //  avoid reallocation on import, if possible
    //
    mpz_init2(a_mp, (c3_w_tmp)c3_min(bit_d, UINT32_MAX));
    mpz_import(a_mp, len_n, -1, sizeof(c3_w_tmp), 0, 0, b_u->buf_w);
  }
}

/* u3r_short():
**
**   Return short (a_n) of (b).
*/
c3_s
u3r_short(c3_n  a_n,
          u3_atom b)
{
  u3_assert( u3_none != b );
  u3_assert( c3y == u3a_is_atom(b) );

  if ( c3y == u3a_is_cat(b) ) {
#ifndef VERE_64
    switch ( a_n ) {
      case 0:  return b & 0xffff;
      case 1:  return b >> 16;
      default: return 0;
    }
#else
    switch ( a_n ) {
      case 0:  return b & 0xffff;
      case 1:  return (b >> 16) & 0xffff;
      case 2:  return (b >> 32) & 0xffff;
      case 3:  return b >> 48;
      default: return 0;
    }
#endif
  }
  else {
    u3a_atom* b_u = u3a_to_ptr(b);
    c3_n    nix_n = a_n >> 1;

    if ( nix_n >= b_u->len_n ) {
      return 0;
    }
    else {
      c3_w_tmp wor_w = b_u->buf_w[nix_n];

      return ( a_n & 1 ) ? (wor_w >> 16) : (wor_w & 0xffff);
    }
  }
}

/* u3r_word():
**
**   Return word (a_n) of (b).
*/
c3_w_tmp
u3r_word(c3_n    a_n,
           u3_atom b)
{
  u3_assert(u3_none != b);
  u3_assert(_(u3a_is_atom(b)));

  if ( _(u3a_is_cat(b)) ) {
#ifndef VERE_64
    if ( a_n > 0 ) {
      return 0;
    }
    else return b;
#else
    switch ( a_n ) {
      case 0:  return b & 0xffffffff;
      case 1:  return b >> 32;
      default: return 0
    }
#endif
  }
  else {
    u3a_atom* b_u = u3a_to_ptr(b);

    if ( a_n >= b_u->len_n ) {
      return 0;
    }
    else return b_u->buf_w[a_n];
  }
}

/* u3r_word_fit():
**
**   Fill (out_w) with (a) if it fits, returning success.
*/
c3_t
u3r_word_fit(c3_w_tmp *out_w, u3_atom a)
{
  if ( u3r_met(5, a) > 1 ) {
    return 0;
  }
  else {
    *out_w = u3r_word(0, a);
    return 1;
  }
}

/* u3r_chub():
**
**   Return double-word (a_n) of (b).
*/
c3_d
u3r_chub(c3_n  a_n,
           u3_atom b)
{
#ifndef VERE_64
  c3_w_tmp wlo_w = u3r_word(a_n * 2, b);
  c3_w_tmp whi_w = u3r_word(1 + (a_n * 2), b);

  return (((c3_d)whi_w) << 32ULL) | ((c3_d)wlo_w);
#else
  if ( _(u3a_is_cat(b)) ) {
    if ( a_n > 0 ) {
      return 0;
    }
    else return b;
  }
  else {
    c3_w_tmp wlo_w = u3r_word(a_n * 2, b);
    c3_w_tmp whi_w = u3r_word(1 + (a_n * 2), b);

    return (((c3_d)whi_w) << 32ULL) | ((c3_d)wlo_w);
  }
#endif
}

/* u3r_words():
**
**  Copy words (a_n) through (a_n + b_n - 1) from (d) to (c).
*/
void
u3r_words(c3_n    a_n,
          c3_n    b_n,
          c3_w_tmp*   c_w,
          u3_atom d)
{
  u3_assert(u3_none != d);
  u3_assert(_(u3a_is_atom(d)));

  if ( b_n == 0 ) {
    return;
  }
  if ( _(u3a_is_cat(d)) ) {
#ifndef VERE_64
    if ( a_n == 0 ) {
      *c_w = d;
      memset((c3_y*)(c_w + 1), 0, (b_n - 1) << 2);
    }
    else {
      memset((c3_y*)c_w, 0, b_n << 2);
    }
#else
    if ( a_n == 0 ) {
      *c_w = (c3_w_tmp)(d & 0xffffffff);
      if ( b_n > 1 ) {
        *(c_w + 1) = (c3_w_tmp)(d >> 32);
        memset((c3_y*)(c_w + 2), 0, (b_n - 2) << 2);
      }
    }
    else if ( a_n == 1 ) {
      *c_w = (c3_w_tmp)(d >> 32);
      memset((c3_y*)(c_w + 1), 0, (b_n - 1) << 2);
    }
    else {
      memset((c3_y*)c_w, 0, b_n << 2);
    }
#endif
  }
  else {
    u3a_atom* d_u = u3a_to_ptr(d);
    if ( a_n >= d_u->len_n ) {
      memset((c3_y*)c_w, 0, b_n << 2);
    }
    else {
      c3_n z_n = c3_min(b_n, d_u->len_n - a_n);
      c3_w_tmp* x_w = d_u->buf_w + a_n;
      memcpy((c3_y*)c_w, (c3_y*)x_w, z_n << 2);
      if ( b_n > d_u->len_n - a_n ) {
        memset((c3_y*)(c_w + z_n), 0, (b_n + a_n - d_u->len_n) << 2);
      }
    }
  }
}

/* u3r_chubs():
**
**  Copy double-words (a_n) through (a_n + b_n - 1) from (d) to (c).
*/
void
u3r_chubs(c3_n    a_n,
          c3_n    b_n,
          c3_d*   c_d,
          u3_atom d)
{
  /* XX: assumes little-endian
  */
  u3r_words(a_n * 2, b_n * 2, (c3_w_tmp *)c_d, d);
}

/* u3r_safe_byte(): validate and retrieve byte.
*/
c3_o
u3r_safe_byte(u3_noun dat, c3_y* out_y)
{
  if (  (c3n == u3a_is_atom(dat))
     || (1 < u3r_met(3, dat)) )
  {
    return c3n;
  }

  *out_y = u3r_byte(0, dat);
  return c3y;
}

/* u3r_safe_word(): validate and retrieve word.
*/
c3_o
u3r_safe_word(u3_noun dat, c3_w_tmp* out_w)
{
  if (  (c3n == u3a_is_atom(dat))
     || (1 < u3r_met(5, dat)) )
  {
    return c3n;
  }

  *out_w = u3r_word(0, dat);
  return c3y;
}

/* u3r_safe_chub(): validate and retrieve chub.
*/
c3_o
u3r_safe_chub(u3_noun dat, c3_d* out_d)
{
  if (  (c3n == u3a_is_atom(dat))
     || (1 < u3r_met(6, dat)) )
  {
    return c3n;
  }

  *out_d = u3r_chub(0, dat);
  return c3y;
}

/* u3r_chop_bits():
**
**   XOR `wid_d` bits from`src_w` at `bif_g` to `dst_w` at `bif_g`
**
**   NB: [dst_w] must have space for [bit_g + wid_d] bits
*/
void
u3r_chop_bits(c3_g  bif_g,
              c3_d  wid_d,
              c3_g  bit_g,
              c3_w_tmp* dst_w,
        const c3_w_tmp* src_w)
{
  c3_y fib_y = 32 - bif_g;
  c3_y tib_y = 32 - bit_g;

  //  we need to chop words
  //
  if ( wid_d >= tib_y ) {
    //  align *dst_w
    //
    if ( bit_g ) {
      c3_w_tmp low_w = src_w[0] >> bif_g;

      if ( bif_g > bit_g ) {
        low_w   ^= src_w[1] << fib_y;
      }

      *dst_w++  ^= low_w << bit_g;

      wid_d -= tib_y;
      bif_g += tib_y;
      src_w += !!(bif_g >> 5);
      bif_g &= 31;
      fib_y  = 32 - bif_g;
    }

    {
      size_t i_i, byt_i = wid_d >> 5;

      if ( !bif_g ) {
        for ( i_i = 0; i_i < byt_i; i_i++ ) {
          dst_w[i_i] ^= src_w[i_i];
        }
      }
      else {
        for ( i_i = 0; i_i < byt_i; i_i++ ) {
          dst_w[i_i] ^= (src_w[i_i] >> bif_g) ^ (src_w[i_i + 1] << fib_y);
        }
      }

      src_w += byt_i;
      dst_w += byt_i;
      wid_d &= 31;
      bit_g  = 0;
    }
  }

  //  we need to chop (more) bits
  //
  if ( wid_d ) {
    c3_w_tmp hig_w = src_w[0] >> bif_g;

    if ( wid_d > fib_y ) {
      hig_w   ^= src_w[1] << fib_y;
    }

    *dst_w    ^= (hig_w & (((c3_d)1 << wid_d) - 1)) << bit_g;
  }
}

/* u3r_chop_words():
**
**   Into the bloq space of `met`, from position `fum` for a
**   span of `wid`, to position `tou`, XOR from `src_w`
**   into `dst_w`.
**
**   NB: [dst_w] must have space for [tou_n + wid_n] bloqs
*/
void
u3r_chop_words(c3_g  met_g,
               c3_n  fum_n,
               c3_n  wid_n,
               c3_n  tou_n,
               c3_w_tmp* dst_w,
               c3_n  len_n,
         const c3_w_tmp* src_w)
{
  //  operate on words
  //
  if ( met_g >= 5 ) {
    size_t i_i, wid_i;

    {
      c3_g   hut_g = met_g - 5;
      size_t fum_i = (size_t)fum_n << hut_g;
      size_t tou_i = (size_t)tou_n << hut_g;
      size_t tot_i;

      wid_i = (size_t)wid_n << hut_g;
      tot_i = fum_i + wid_i;

      //  since [dst_w] must have space for (tou_n + wid_n) bloqs,
      //  neither conversion can overflow
      //
      if ( (fum_i >> hut_g != fum_n) || (tot_i  - wid_i != fum_i) ) {
        u3m_bail(c3__fail);
        return;
      }
      else if ( fum_i >= len_n ) {
        return;
      }

      if ( tot_i > len_n ) {
        wid_i -= tot_i - len_n;
      }

      src_w += fum_i;
      dst_w += tou_i;
    }

    for ( i_i = 0; i_i < wid_i; i_i++ ) {
      dst_w[i_i] ^= src_w[i_i];
    }
  }
  //  operate on bits
  //
  else {
    c3_d wid_d = (c3_d)wid_n << met_g;
    c3_g bif_g, bit_g;

    {
      c3_d len_d = (c3_d)len_n << 5;
      c3_d fum_d = (c3_d)fum_n << met_g;
      c3_d tou_d = (c3_d)tou_n << met_g;
      c3_d tot_d = fum_d + wid_d;

      // see above
      //
      if ( (fum_d >> met_g != fum_n) || (tot_d  - wid_d != fum_d) ) {
        u3m_bail(c3__fail);
        return;
      }
      else if ( fum_d > len_d ) {
        return;
      }

      if ( tot_d > len_d ) {
        wid_d -= tot_d - len_d;
      }

      src_w += fum_d >> 5;
      dst_w += tou_d >> 5;
      bif_g  = fum_d & 31;
      bit_g  = tou_d & 31;
    }

    u3r_chop_bits(bif_g, wid_d, bit_g, dst_w, src_w);
  }
}

/* u3r_chop():
**
**   Into the bloq space of `met`, from position `fum` for a
**   span of `wid`, to position `tou`, XOR from atom `src`
**   into `dst_w`.
**
**   NB: [dst_w] must have space for [tou_n + wid_n] bloqs
*/
void
u3r_chop(c3_g  met_g,
         c3_n  fum_n,
         c3_n  wid_n,
         c3_n  tou_n,
         c3_w_tmp* dst_w,
         u3_atom src)
{
  c3_w_tmp* src_w;
  c3_n  len_n;

  if ( _(u3a_is_cat(src)) ) {
    len_n = src ? 1 : 0;
    src_w = &src;
  }
  else {
    u3a_atom* src_u = u3a_to_ptr(src);

    u3_assert(u3_none != src);
    u3_assert(_(u3a_is_atom(src)));

    len_n = src_u->len_n;
    src_w = src_u->buf_w;
  }

  u3r_chop_words(met_g, fum_n, wid_n, tou_n, dst_w, len_n, src_w);
}

/* u3r_string(): `a` as malloced C string.
*/
c3_c*
u3r_string(u3_atom a)
{
  c3_n  met_n = u3r_met(3, a);
  c3_c* str_c = c3_malloc(met_n + 1);

  u3r_bytes(0, met_n, (c3_y*)str_c, a);
  str_c[met_n] = 0;
  return str_c;
}

/* u3r_tape(): `a`, a list of bytes, as malloced C string.
*/
c3_y*
u3r_tape(u3_noun a)
{
  u3_noun b;
  c3_n    i_n;
  c3_y    *a_y;

  for ( i_n = 0, b=a; c3y == u3a_is_cell(b); i_n++, b=u3a_t(b) )
    ;
  a_y = c3_malloc(i_n + 1);

  for ( i_n = 0, b=a; c3y == u3a_is_cell(b); i_n++, b=u3a_t(b) ) {
    a_y[i_n] = u3a_h(b);
  }
  a_y[i_n] = 0;

  return a_y;
}

/* u3r_mug_both(): Join two mugs.
*/
c3_w_tmp
u3r_mug_both(c3_w_tmp lef_w, c3_w_tmp rit_w)
{
  c3_y len_y = 4 + ((c3_bits_word(rit_w) + 0x7) >> 3);
  c3_w_tmp syd_w = 0xdeadbeef;
  c3_w_tmp   i_w = 0;
  c3_y buf_y[8];

  buf_y[0] = lef_w         & 0xff;
  buf_y[1] = (lef_w >>  8) & 0xff;
  buf_y[2] = (lef_w >> 16) & 0xff;
  buf_y[3] = (lef_w >> 24) & 0xff;
  buf_y[4] = rit_w         & 0xff;
  buf_y[5] = (rit_w >>  8) & 0xff;
  buf_y[6] = (rit_w >> 16) & 0xff;
  buf_y[7] = (rit_w >> 24) & 0xff;

  while ( i_w < 8 ) {
    c3_w_tmp haz_w;
    c3_w_tmp ham_w;

    MurmurHash3_x86_32(buf_y, len_y, syd_w, &haz_w);
    ham_w = (haz_w >> 31) ^ (haz_w & 0x7fffffff);

    if ( 0 == ham_w ) {
      syd_w++; i_w++;
    }
    else {
      return ham_w;
    }
  }

  return 0xfffe;
}

/* u3r_mug_bytes(): Compute the mug of `buf`, `len`, LSW first.
*/
c3_w_tmp
u3r_mug_bytes(const c3_y *buf_y,
              c3_n        len_n)
{
  c3_w_tmp syd_w = 0xcafebabe;
  c3_w_tmp   i_w = 0;

  while ( i_w < 8 ) {
    c3_w_tmp haz_w;
    c3_w_tmp ham_w;

    MurmurHash3_x86_32(buf_y, len_n, syd_w, &haz_w);
    ham_w = (haz_w >> 31) ^ (haz_w & 0x7fffffff);

    if ( 0 == ham_w ) {
      syd_w++; i_w++;
    }
    else {
      return ham_w;
    }
  }

  return 0x7fff;
}

/* u3r_mug_c(): Compute the mug of `a`, LSB first.
*/
c3_w_tmp
u3r_mug_c(const c3_c* a_c)
{
  return u3r_mug_bytes((c3_y*)a_c, strlen(a_c));
}

/* u3r_mug_cell(): Compute the mug of the cell `[hed tel]`.
*/
c3_w_tmp
u3r_mug_cell(u3_noun hed,
             u3_noun tel)
{
  c3_w_tmp lus_w = u3r_mug(hed);
  c3_w_tmp biq_w = u3r_mug(tel);

  return u3r_mug_both(lus_w, biq_w);
}

/* u3r_mug_chub(): Compute the mug of `num`, LSW first.
*/
c3_w_tmp
u3r_mug_chub(c3_d num_d)
{
  c3_w_tmp buf_w[2];

  buf_w[0] = (c3_w_tmp)(num_d & 0xffffffffULL);
  buf_w[1] = (c3_w_tmp)(num_d >> 32);

  return u3r_mug_words(buf_w, 2);
}

/* u3r_mug_words(): 31-bit nonzero MurmurHash3 on raw words.
*/
c3_w_tmp
u3r_mug_words(const c3_w_tmp* key_w, c3_n len_n)
{
  c3_n byt_n;

  //  ignore trailing zeros
  //
  while ( len_n && !key_w[len_n - 1] ) {
    len_n--;
  }

  //  calculate byte-width a la u3r_met(3, ...)
  //
  if ( !len_n ) {
    byt_n = 0;
  }
  else {
    c3_n gal_n = len_n - 1;
    c3_w_tmp daz_w = key_w[gal_n];

    byt_n = (gal_n << 2) + ((c3_bits_word(daz_w) + 7) >> 3);
  }

  //  XX: assumes little-endian
  //
  return u3r_mug_bytes((c3_y*)key_w, byt_n);
}

/* _cr_mug: stack frame for recording cell traversal
**          !mug == head-frame
*/
typedef struct {
  c3_w_tmp  mug_w;
  u3_cell cel;
} _cr_mugf;

/* _cr_mug_next(): advance mug calculation, pushing cells onto the stack.
*/
static inline c3_w_tmp
_cr_mug_next(u3a_pile* pil_u, u3_noun veb)
{
  while ( 1 ) {
    //  veb is a direct atom, mug is not memoized
    //
    if ( c3y == u3a_is_cat(veb) ) {
      return u3r_mug_words(&veb, 1);
    }
    //  veb is indirect, a pointer into the loom
    //
    else {
      u3a_noun* veb_u = u3a_to_ptr(veb);

      //  veb has already been mugged, return memoized value
      //
      if ( veb_u->mug_n ) {
        c3_dessert((veb_u->mug_n >> 31) == 0);
        return (c3_w_tmp)veb_u->mug_n;
      }
      //  veb is an indirect atom, mug its bytes and memoize
      //
      else if ( c3y == u3a_is_atom(veb) ) {
        u3a_atom* vat_u = (u3a_atom*)veb_u;
        c3_w_tmp      mug_w = u3r_mug_words(vat_u->buf_w, vat_u->len_n);
        vat_u->mug_n = mug_w;
        return mug_w;
      }
      //  veb is a cell, push a stack frame to mark head-recursion
      //  and read the head
      //
      else {
        u3a_cell* cel_u = (u3a_cell*)veb_u;
        _cr_mugf* fam_u = u3a_push(pil_u);

        fam_u->mug_w = 0;
        fam_u->cel   = veb;

        veb = cel_u->hed;
        continue;
      }
    }
  }
}

/* u3r_mug(): statefully mug a noun with 31-bit murmur3.
*/
c3_w_tmp
u3r_mug(u3_noun veb)
{
  u3a_pile  pil_u;
  _cr_mugf* fam_u;
  c3_w_tmp      mug_w;

  //  sanity check
  //
  u3_assert( u3_none != veb );

  u3a_pile_prep(&pil_u, sizeof(*fam_u));

  //  commence mugging
  //
  mug_w = _cr_mug_next(&pil_u, veb);

  //  process cell results
  //
  if ( c3n == u3a_pile_done(&pil_u) ) {
    fam_u = u3a_peek(&pil_u);

    do {
      //  head-frame: stash mug and continue into the tail
      //
      if ( !fam_u->mug_w ) {
        u3a_cell* cel_u = u3a_to_ptr(fam_u->cel);

        fam_u->mug_w = mug_w;
        mug_w        = _cr_mug_next(&pil_u, cel_u->tel);
        fam_u        = u3a_peek(&pil_u);
      }
      //  tail-frame: calculate/memoize cell mug and pop the stack
      //
      else {
        u3a_cell* cel_u = u3a_to_ptr(fam_u->cel);

        mug_w        = u3r_mug_both(fam_u->mug_w, mug_w);
        cel_u->mug_n = mug_w;
        fam_u        = u3a_pop(&pil_u);
      }
    }
    while ( c3n == u3a_pile_done(&pil_u) );
  }

  return mug_w;
}

/* u3r_skip():
**
**  Extract a constant from a formula, ignoring
**  safe/static hints, doing no computation.
*/
u3_weak
u3r_skip(u3_noun fol)
{
  while ( c3y == u3du(fol) ) {
    switch ( u3h(fol) ) {
      default: return u3_none;
      case 1:  return u3t(fol);
      case 11: {
        u3_noun arg = u3t(fol),
                hod = u3h(arg);

        if ( (c3y == u3du(hod)) && (u3_none == u3r_skip(u3t(hod))) ) {
          return u3_none;
        }
        fol = u3t(arg);
      }
    }
  }
  return u3_none;
}
