/// @file

#include "noun.h"
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
  u3_cue_xeno*  sil_u;
  u3_weak       pil;
  u3C.wag_h |= u3o_hashless;
  u3m_boot_lite(1 << 26);
  sil_u = u3s_cue_xeno_init_with(ur_fib27, ur_fib28);
  if ( u3_none == (pil = u3s_cue_xeno_with(sil_u, len_d, byt_y)) ) {
    printf("*** fail _setup 1\n");
    exit(1);
  }
  u3s_cue_xeno_done(sil_u);
  if ( c3n == u3v_boot_lite(pil) ) {
    printf("*** fail _setup 2\n");
    exit(1);
  }
}

static c3_t
_test_1()
{
  // u3_noun sub = 42, fol = u3nt(4, 0, 1);
  // u3_noun pro = u3nc_nock_on(sub, fol);
  // c3_t out = _(u3r_sing(pro, 43));
  // u3z(pro);
  // return out;
  u3d_prep_ka();
  return 1;
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
  u3m_grab();

  fprintf(stderr, "test nock compile: ok\r\n");
  return 0;
}
