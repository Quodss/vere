/// @file

#ifndef U3_NOCK_COMPILE_H
#define U3_NOCK_COMPILE_H

#include <stdio.h>

#include "c3/c3.h"
#include "jets.h"
#include "types.h"
#include "zave.h"

/*
  |%
  +$  cape  $~(| $@(? (pair cape cape)))  ::  noun mask
  +$  sock  $~(|+~ (pair cape *))         ::  mask + data
  --
*/

  typedef struct {
    c3_l    sip_l;
    u3_noun key;
    u3z_cid cid;
  } u3nc_memo;

  struct _u3nc_prog;
  typedef struct {
    u3_noun          bell;    //  [sock formula]
    u3p(_u3nc_prog)  pog_p;   //  called program post or [less formula] during compilation
    c3_s             len_s;   //  number of arguments
    c3_y*            arg_y;   //  register indices
    u3_noun          ring;    //  ~ or [path axis]
    u3j_harm*        ham_u;   //  jet arm, nullable
    c3_l             axe_l;   //  jet arm axis
  } u3nc_dire;

  typedef struct _u3nc_prog  {
    struct {
      c3_o      own_o;                // program owns ops_y?
      c3_w      len_w;                // length of bytecode (bytes)
      c3_y*     ops_y;                // actual array of bytes
    } byc_u;                          // bytecode
    struct {
      c3_w      len_w;                // number of literals
      u3_noun*  non;                  // array of literals
    } lit_u;                          // literals
    struct {
      c3_w       len_w;               // number of memo slots
      u3nc_memo* sot_u;               // array of memo slots
    } mem_u;                          // memo slot data
    struct {
      c3_w       len_w;               // number of direct calls
      u3nc_dire* dat_u;               // array of call info
    } dir_u;                          // direct call data
  } u3nc_prog;

      u3_noun
      u3nc_nock_on(u3_noun bus, u3_noun fol);

      u3p(u3n_prog)
      u3nc_find(u3_noun key, u3_noun fol);

      u3_noun
      u3nc_burn(u3p(u3n_prog) pog_p, u3_noun bus);

      u3_noun
      u3nc_slam_on(u3_noun gat, u3_noun sam);

      u3_noun
      u3nc_kick_on(u3_noun gat);

      u3_noun
      u3nc_nock_et(u3_noun gul, u3_noun bus, u3_noun fol);

      u3_noun
      u3nc_slam_et(u3_noun gul, u3_noun gat, u3_noun sam);

      u3_noun
      u3nc_nock_an(u3_noun bus, u3_noun fol);

    /* u3nc_reap(): promote bytecode state.
     */
      void
      u3nc_reap(u3p(u3h_root) har_p);

    /* u3nc_take(): copy junior bytecode state.
     */
      u3p(u3h_root)
      u3nc_take(u3p(u3h_root) har_p);

    /* u3nc_mark(): mark bytecode cache.
     */
      u3m_quac*
      u3nc_mark();

    /* u3nc_reclaim(): clear ad-hoc persistent caches to reclaim memory.
    */
      void
      u3nc_reclaim(void);

    /* u3nc_rewrite_compact(): rewrite bytecode cache for compaction.
     */
      void
      u3nc_rewrite_compact(void);

    /* u3nc_free(): free bytecode cache.
     */
      void
      u3nc_free(void);

    /* u3nc_ream(): refresh after restoring from checkpoint.
    */
      void
      u3nc_ream(void);

#endif /* ifndef U3_NOCK_COMPILE_H */
