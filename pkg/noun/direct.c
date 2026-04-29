/// @file

#include "direct.h"

static inline c3_o
_assert_loob(u3_noun som)
{
  u3_assert(som <= 1);
  return som;
}

// RETAINS
//
static void
_ca_rip(u3_noun cape, u3_noun* l, u3_noun* r)
{
  if ( c3y == u3ud(cape) ) {
    *l = *r = _assert_loob(cape);
  }
  else {
    u3r_cell(cape, l, r);
  }
}

// RETAINS arguments
// (here it is ok since deduplication will always happen on each iteration, so
// inductive argument of validity of uncounted refs applies)
//
static c3_o
_so_huge(u3_noun cape_one,
         u3_noun data_one,
         u3_noun cape_two,
         u3_noun data_two)
{
  if ( c3y == u3r_sing(cape_one, cape_two)
    && c3y == u3r_sing(data_one, data_two) ) {
    return c3y;
  }

  if ( c3y == u3ud(data_one) ) {
    if ( c3n == _assert_loob(cape_one) ) return c3y;
    return c3a(u3ud(cape_two),
            c3a(_assert_loob(cape_two),
                u3r_sing(data_one, data_two)));
  }
  
  u3_assert(c3n != cape_one);

  if ( c3y == u3ud(data_two) ) {
    _assert_loob(cape_two);
    return c3n;
  }

  u3_noun lope, rope, loop, roop;
  u3_noun l_data_one, r_data_one;
  u3_noun l_data_two, r_data_two;

  u3r_cell(data_one, &l_data_one, &r_data_one);
  u3r_cell(data_two, &l_data_two, &r_data_two);

  _ca_rip(cape_one, &lope, &rope);
  _ca_rip(cape_two, &loop, &roop);

  return c3a(_so_huge(lope, l_data_one, loop, l_data_two),
             _so_huge(rope, r_data_one, roop, r_data_two));
}

#define nth_arg(n)  ((1 << (n + 1)) - 2)

void
u3d_prep_ka()
{
  if ( u3R->dir_ka ) {
    return;
  }
  u3_noun hoons = u3s_cue_bytes((c3_d)U3_Ska_Verb_len, U3_Ska_Verb);
  u3_noun fol, sock, soak, noir, skan, gene, line, vere;
  if ( c3n == u3r_mean(hoons,
      {nth_arg(1),     &fol },
      {nth_arg(2),     &sock},
      {nth_arg(3),     &soak},
      {nth_arg(4),     &noir},
      {nth_arg(5),     &skan},
      {nth_arg(6),     &gene},
      {nth_arg(7),     &line},
      {nth_arg(7) + 1, &vere}) ) {
        u3m_bail(c3__fail);
  }

  u3_noun subject = u3nq(
    u3k(sock),
    u3k(soak),
    u3k(noir), u3nq(
    u3k(skan),
    u3k(gene),
    u3k(line), u3nc(
    u3k(vere),
    u3v_wish("..zuse")
  )));

  u3_noun interface = u3n_nock_on(subject, u3k(fol));

  u3R->dir_ka = interface;

  u3z(hoons);
}

// RETAINS
// `list` is (list pro=[sock *])
//
u3_weak
u3d_match_sock(u3_noun cape, u3_noun data, u3_noun list)
{
  u3_weak pro = u3_none;
  u3_noun cape_max, data_max;
  u3_noun i, cape_i, data_i;
  while ( u3_nul != list ) {
    u3x_cell(list, &i, &list);
    u3x_mean(i, {4, &cape_i}, {5, &data_i});
    if ( c3n == _so_huge(cape_i, data_i, cape, data) ) continue;
    //  first match or better match
    //
    if ( (u3_none == pro)
          || (c3y == _so_huge(cape_max, data_max, cape_i, data_i)) ) {
      pro = i;
      cape_max = cape_i;
      data_max = data_i;
    }
  }
  return pro;
}

//  RETAINS
static u3_noun
_d_compile(u3_noun sub, u3_noun fol)
{
  u3_noun limb = u3nc(c3__limb, u3i_string("compile")),
          comp = u3dc("slap", u3R->dir_ka, limb),
          samp = u3nt(u3nt(c3__cell, c3__noun, c3__noun), u3k(sub), u3k(fol)),
          slam = u3v_wish("slam"),
          gul  = u3nt(u3nc(1, 0), u3nc(0, 0), 0),  // |~(^ ~)
          pro  = u3n_slam_et(gul, slam, u3nc(comp, samp));
  
  u3_assert(_(u3du(pro)));
  if ( 0 != u3h(pro) )
  {
      u3m_bail(c3__fail);
  }
  u3R->dir_ka = u3k(u3t(u3t(pro)));
  u3_noun out = u3k(u3h(u3t(pro)));
  u3z(pro);
  return out;
}

//  RETAINS arguments
//  XX remove u3dc, use hard-coded axes
//
u3nc_prog*
u3d_search(u3_noun sub, u3_noun fol)
{
  u3d_prep_ka();

  u3nc_prog* pog_u = u3nc_look_entry_direct(sub, fol);
  if ( pog_u ) return pog_u;
  u3_noun sock = _d_compile(sub, fol);
  pog_u = u3nc_build_entry_direct(sock, fol);
  u3z(sock);
  return pog_u;
}

c3_y
u3d_bell_number_args(u3_noun bell)
{
  c3_stub;
}

u3_noun
u3d_bell_ops(u3_noun bell, c3_t entry_t)
{
  c3_stub;
}