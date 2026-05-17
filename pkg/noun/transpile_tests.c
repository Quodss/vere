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

// #define INC(som)  u3qa_inc(som)
#define INC(som) ({                                             \
  u3_noun __som = som;                                          \
  ( __som < (0x7fffffff - 1) ) ? (__som + 1) : u3qa_inc(__som); \
})

#define CON(hed, tel) u3nc(u3k(hed), u3k(tel))

//  XX way faster, what means?
// inline static c3_o
// EQ(u3_noun a, u3_noun b)
// {
//   if ( a == b ) return c3y;
//   if ( c3y == u3a_is_cat(a) || c3y == u3a_is_cat(b) ) return c3n;
//   return u3r_sing(a, b);
// }

#define EQ u3r_sing

/// transpiler output

static u3_noun _function_0x2(u3_noun reg_0v0, u3_noun reg_0v1);

static u3_noun _function_0x1(u3_noun reg_0v0);

static u3_noun _function_0x0();

//  |- body. XX could recursive calls like this be turned into loops?
static u3_noun
_function_0x2(u3_noun reg_0v0, u3_noun reg_0v1)
{
  u3_noun rs[4];
  rs[0] = reg_0v0;
  rs[1] = reg_0v1;
  rs[3] = INC(rs[0]);
  if ( c3y == EQ(rs[1], rs[3]) ) {   //  ?:  =(a +(b))
    return rs[0];                          //    b
  }
  else {
    // rs[2] = INC(rs[0]);
    return _function_0x2(rs[3], rs[1]);   //  $(b +(b))
  }
}

//  +dec body
static u3_noun
_function_0x1(u3_noun reg_0v0)
{
  u3_noun rs[3];
  rs[0] = reg_0v0;
  rs[2] = 0;
  if ( c3y == EQ(rs[2], rs[0]) ) {      //  ?<  =(0 a)
    u3m_bail(c3__exit);
  }
  else {
    rs[1] = 0;
    return _function_0x2(rs[1], rs[0]);       //  |-  ...
  }
}

//  (dec 10000000)  :: top level entry
static u3_noun
_function_0x0()
{
  u3_noun rs[1];
  rs[0] = 10000000;
  return _function_0x1(rs[0]);
}



/// end of transpiler output

static double diff_in_seconds(struct timespec start, struct timespec end) {
    return (end.tv_sec - start.tv_sec) +
           (end.tv_nsec - start.tv_nsec) / 1e9;
}

static c3_t
_test_call_transpiled(void)
{
  struct timespec start, end;

  clock_gettime(CLOCK_MONOTONIC, &start);

  u3_noun pro;
  if ( 1 ) {
    pro = _function_0x0();
  }
  else {
    int inc, i = 0;
    for (; (inc = INC(i)) != 10000000; i = inc) ;

    asm volatile("" :: "r"(i));
    pro = (u3_noun)i;
  }

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
  u3m_grab(u3_none);

  fprintf(stderr, "test transpile: ok\r\n");
  return 0;
}