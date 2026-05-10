/// @file

#include "noun.h"
#include "vere.h"
#include "direct.h"
#include "ivory.h"
#include "nock-compile.h"
#include "ur/ur.h"


/* _setup(): prepare for tests.
*/
static void
_setup(void)
{
  c3_d          len_d = u3_Ivory_pill_len;
  c3_y*         byt_y = u3_Ivory_pill;
  u3_weak       pil;
  u3C.wag_w |= u3o_hashless;
  u3m_boot_lite(1 << 26);
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
_test_1()
{
  u3_noun sub = 42, fol = u3nt(4, 0, 1);
  u3_noun pro;
  if ( !_do_or_error(_nc_nock_on, u3nc(sub, fol), "test 1", &pro) ) {
    return 0;
  }
  c3_t out = _(u3r_sing(pro, 43));
  u3z(pro);
  return out;
}

/* main(): run all test cases.
*/
int
main(int argc, char* argv[])
{
  _setup();

  if ( !_test_1() ) {
    fprintf(stderr, "test 1: failed\r\n");
    exit(1);
  }
  
  //  GC
  //
  u3m_grab(u3_none);

  fprintf(stderr, "test nock compile: ok\r\n");
  return 0;
}
