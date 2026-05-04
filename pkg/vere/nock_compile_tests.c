/// @file

#include "noun.h"
#include "ivory.h"
#include "vere.h"
#include "nock-compile.h"


/* _setup(): prepare for tests.
*/
static void
_setup(void)
{
  u3m_init(1 << 20);
  u3m_pave(c3y);
}

static c3_t
_test_1()
{
  u3_noun sub = 42, fol = u3nt(4, 0, 1);
  u3_noun pro = u3nc_nock_on(sub, fol);
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
  u3m_grab();

  fprintf(stderr, "test nock compile: ok\r\n");
  return 0;
}
