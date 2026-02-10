/// @file

#include "noun.h"
#include <time.h>

/* _setup(): prepare for tests.
*/
static void
_setup(void)
{
  u3m_boot_lite(1 << 24);
}

#define CEL(som)  if ( c3n == u3du(som) ) u3m_bail(c3__exit);
#define HED(som)  ( c3y == u3du(som) ) ? ((u3a_cell*)u3a_to_ptr(som))->hed \
                                       : 0

#define TAL(som)  ( c3y == u3du(som) ) ? ((u3a_cell*)u3a_to_ptr(som))->tel \
                                       : 0

#define INC(som)  u3qa_inc(som)

#define CON(hed, tel) u3nc(u3k(hed), u3k(tel))

static u3_noun _function_0x2(u3_noun reg_0v0, u3_noun reg_0v1);

static u3_noun _function_0x1(u3_noun reg_0v0);

static u3_noun _function_0x0(u3_noun reg_0v0);

static u3_noun
_function_0x2(u3_noun reg_0v0, u3_noun reg_0v1)
{
  u3_noun rs[6];

  rs[0] = reg_0v0;
  rs[1] = reg_0v1;
_0w1:
  CEL(rs[1]);
  rs[3] = TAL(rs[1]);
  CEL(rs[3]);
  rs[4] = HED(rs[3]);
  rs[5] = INC(rs[0]);
  if ( c3y == u3r_sing(rs[4], rs[5]) ) {
    goto _0w7;
  }
  else {
    goto _0w8;
  }
//
_0w7:
  return rs[0];

_0w8:
  rs[2] = INC(rs[0]);
  return _function_0x2(rs[2], rs[1]);


}
static u3_noun
_function_0x1(u3_noun reg_0v0)
{
  u3_noun rs[2];

  rs[0] = reg_0v0;
_0w1:
  rs[1] = 0;
  return _function_0x2(rs[1], rs[0]);
//

}
static u3_noun
_function_0x0(u3_noun reg_0v0)
{
  u3_noun rs[5];

  rs[0] = reg_0v0;
_0w1:
  rs[1] = u3nq(8, u3nc(1, 0), 8, u3nq(u3nq(1, 6, u3nq(5, u3nc(0, 30), 4, u3nc(0, 6)), u3nq(u3nc(0, 6), 9, 2, u3nq(10, u3nq(6, 4, 0, 6), 0, 1))), 9, 2, u3nc(0, 1)));
  rs[2] = 10000000;
  rs[3] = CON(rs[2], rs[0]);
  rs[4] = CON(rs[1], rs[3]);
  return _function_0x1(rs[4]);
//

}

static double diff_in_seconds(struct timespec start, struct timespec end) {
    return (end.tv_sec - start.tv_sec) +
           (end.tv_nsec - start.tv_nsec) / 1e9;
}

static c3_t
_test_call_transpiled(void)
{
  struct timespec start, end;

  clock_gettime(CLOCK_MONOTONIC, &start);
  u3_noun pro = _function_0x0(u3_nul);
  clock_gettime(CLOCK_MONOTONIC, &end);

  printf("Elapsed: %.6f seconds\n", diff_in_seconds(start, end));
  return 9999999 == pro;
}


int
main(int argc, char* argv[])
{
  _setup();

  if ( !_test_call_transpiled() ) {
    fprintf(stderr, "test transpile: failed\r\n");
    exit(1);
  }

  //  GC
  //  (we leak for now)
  // u3m_grab(u3_none);

  fprintf(stderr, "test transpile: ok\r\n");
  return 0;
}