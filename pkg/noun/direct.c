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

static u3_noun
_face(u3_noun vase, u3_noun face)
{
  return u3i_edit(vase, 2, u3nt(c3__face, face, u3k(u3h(vase))));
}

static u3_noun
_d_path(const c3_c** pax_c, c3_w len_w)
{
  u3_noun path = u3_nul;
  while ( len_w-- ) {
    path = u3nc(u3i_string(pax_c[len_w]), path);
  }
  return path;
}

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

void
u3d_prep_ka()
{
  if ( u3R->dir_ka ) {
    return;
  }
  fprintf(stderr, "prep_ka\r\n");
  u3R->dir_ka = u3n_nock_on(
    u3s_cue_bytes((c3_d)U3_Ska_Verb_len, U3_Ska_Verb),
    u3nt(2, u3nc(0, 3), u3nc(0, 2))
  );

  u3_noun list_ring_shape = u3_nul;
  for (c3_w i_w = 0; i_w < u3nc_Cod_len_w; i_w++) {
    const c3_c** pax_u = u3nc_Cod_u[i_w].rin.pax_u;
    c3_w len_w = u3nc_Cod_u[i_w].rin.len_w;
    c3_l axe_l = u3nc_Cod_u[i_w].rin.axe_l;
    u3_noun path = _d_path(pax_u, len_w);
    u3_noun shape = _d_shape(u3nc_Cod_u[i_w].loc_l, u3nc_Cod_u[i_w].arg_w);
    list_ring_shape = u3nc(u3nc(u3nc(path, axe_l), shape), list_ring_shape);
  }

  u3_noun limb = u3nc(c3__limb, u3i_string("add-jet-registerization")),
          gate = u3dc("slap", u3R->dir_ka, limb),
          samp = u3nc(c3__noun, list_ring_shape);
          // gul  = u3nt(u3nc(1, 0), u3nc(0, 0), 0),  // |~(^ ~)
          // pro  = u3n_slam_et(gul, u3v_wish("slam"), u3nc(gate, samp));

  // u3_assert(_(u3du(pro)));
  // if ( 0 != u3h(pro) ) {
  //   fprintf(stderr, "add-jet-registerization crash\r\n");
  //     u3m_bail(c3__fail);
  // }

  // u3R->dir_ka = u3k(u3t(pro));
  // u3z(pro);
  u3R->dir_ka = u3dc("slam", gate, samp);
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
    u3x_mean(i, 4, &cape_i, 5, &data_i, u3_nul);
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
          gul  = u3nt(u3nc(1, 0), u3nc(0, 0), 0),  // |~(^ ~)
          pro  = u3n_slam_et(gul, u3v_wish("slam"), u3nc(comp, samp));
  
  u3_assert(_(u3du(pro)));
  if ( 0 != u3h(pro) ) {
    fprintf(stderr, "%s\r\n", __FUNCTION__);
    u3m_bail(c3__fail);
  }
  u3_noun dir_ka_new = u3dc("slot", 3, u3k(u3t(pro)));
  u3_noun sock = u3k(u3h(u3t(u3t(pro))));
  u3R->dir_ka = dir_ka_new;
  u3z(pro);
  return sock;
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

//  RETAINS
u3_noun
u3d_bell_ops_tot(u3_noun bell, c3_t entry_t)
{
  u3_noun limb = u3nc(c3__limb, u3i_string("vere-straighten")),
          gate = u3dc("slap", u3k(u3R->dir_ka), limb),
          samp = u3nc(u3k(bell), __(entry_t));
          // gul  = u3nt(u3nc(1, 0), u3nc(0, 0), 0),  // |~(^ ~)
          // pro  = u3n_slam_et(gul, u3v_wish("slum"), u3nc(u3k(u3t(gate)), samp));
  u3_noun pro = u3n_slam_on(u3k(u3t(gate)), samp);
  u3z(gate);
  return pro;
  
  // u3_assert(_(u3du(pro)));
  // if ( 0 != u3h(pro) ) {
  //   fprintf(stderr, "%s\r\n", __FUNCTION__);
  //   u3m_bail(c3__fail);
  // }
  // u3_noun out = u3k(u3t(pro));
  // u3z(pro);
  // return out;
}
