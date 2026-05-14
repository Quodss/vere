/// @file

#include "noun.h"
#include "vere.h"
#include "direct.h"
#include "ivory.h"
#include "nock-compile.h"
#include "ur/ur.h"


static u3_noun
_d_shape_mut(c3_l* loc_l, c3_w arg_w)
{
  if ( 0 == arg_w )                return c3n;
  if ( 1 == arg_w && 1 == *loc_l ) return c3y;

  c3_w piv_w = 0;
  while ( piv_w < arg_w && 2 == u3x_cap(loc_l[piv_w]) ) {
    loc_l[piv_w] = u3x_mas(loc_l[piv_w]);
    piv_w++;
  }
  for (c3_w i_w = piv_w; i_w < arg_w; i_w++) {
    loc_l[i_w] = u3x_mas(loc_l[i_w]);
  }

  return u3nc(_d_shape_mut(loc_l, piv_w),
  _d_shape_mut(loc_l + piv_w, arg_w - piv_w));
}

static u3_noun
_d_shape(const c3_l* loc_l, c3_w arg_w)
{
  c3_l* mut_l = u3a_malloc(arg_w * sizeof(c3_l));
  memcpy(mut_l, loc_l, arg_w * sizeof(c3_l));
  u3_noun pro = _d_shape_mut(mut_l, arg_w);
  u3a_free(mut_l);
  return pro;
}

static c3_t
_test_shape1(void)
{
  const c3_l loc_l[2] = {12, 13};
  u3_noun shape = _d_shape(loc_l, 2);
  u3_noun target = u3nt(c3n, u3nc(c3y, c3y), c3n);
  c3_t out_t = c3y == u3r_sing(shape, target);
  u3z(shape); u3z(target);
  return out_t;
}

static c3_t
_test_shape2(void)
{
  const c3_l loc_l[1] = {6};
  u3_noun shape = _d_shape(loc_l, 1);
  u3_noun target = u3nt(c3n, c3y, c3n);
  c3_t out_t = c3y == u3r_sing(shape, target);
  u3z(shape); u3z(target);
  return out_t;
}

/* _setup(): prepare for tests.
*/
static void
_setup(void)
{
  c3_d          len_d = u3_Ivory_pill_len;
  c3_y*         byt_y = u3_Ivory_pill;
  u3_weak       pil;
  u3C.wag_w |= u3o_hashless;
  u3m_boot_lite(1 << 30);
  if ( u3_none == (pil = u3s_cue_bytes(len_d, byt_y)) ) {
    printf("*** fail _setup 1\n");
    exit(1);
  }
  if ( c3n == u3v_boot_lite(pil) ) {
    printf("*** fail _setup 2\n");
    exit(1);
  }
}

static u3_noun
_nc_nock_on(u3_noun sub_fol)
{
  u3_noun sub = u3k(u3h(sub_fol));
  u3_noun fol = u3k(u3t(sub_fol));
  u3z(sub_fol);
  return u3nc_nock_on(sub, fol);
}

static c3_t
_do_or_error(u3_funk fun_f, u3_noun arg, c3_c* where, u3_noun* out)
{
  u3_noun res = u3m_soft(0, fun_f, arg);
  u3_assert(c3y == u3du(res));
  if (0 == u3h(res)) {
    *out = u3k(u3t(res));
    u3z(res);
    return 1;
  }
  u3_pier_punt_goof(where, res);
  return 0;
}


static c3_t
_test_eq(u3_noun sub, u3_noun fol, u3_noun target)
{
  u3_noun pro;
  if ( !_do_or_error(_nc_nock_on, u3nc(sub, fol), "test 1", &pro) ) {
    return 0;
  }
  c3_t out = _(u3r_sing(pro, target));
  u3z(pro), u3z(target);
  return out;
}

/* main(): run all test cases.
*/
int
main(int argc, char* argv[])
{
  _setup();

  if ( !_test_shape1() ) {
    fprintf(stderr, "test failed: %s:%d\r\n", __FILE__, __LINE__);
    exit(1);
  }

  if ( !_test_shape2() ) {
    fprintf(stderr, "test failed: %s:%d\r\n", __FILE__, __LINE__);
    exit(1);
  }

  if ( !_test_eq(42, u3nt(4, 0, 1), 43) ) {
    fprintf(stderr, "test failed: %s:%d\r\n", __FILE__, __LINE__);
    exit(1);
  }

  {
    u3_noun dec = u3nq(8, u3nc(1, 0), 8, u3nq(u3nq(1, 6, u3nq(5, u3nc(0, 7), 4, u3nc(0, 6)), u3nq(u3nc(0, 6), 9, 2, u3nq(u3nc(0, 2), u3nt(4, 0, 6), 0, 7))), 9, 2, u3nc(0, 1)));
    
    if ( !_test_eq(42, dec, 41) ) {
      fprintf(stderr, "test failed: %s:%d\r\n", __FILE__, __LINE__);
      exit(1);
    }
  }
  
  //  GC
  //
  u3m_grab(u3_none);

  fprintf(stderr, "test nock compile: ok\r\n");
  return 0;
}
