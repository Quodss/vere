/// @file

#include "direct.h"

// RETAINS
//
static void
_ca_rip(u3_noun cape, u3_noun* l, u3_noun* r)
{
    if ( c3y == u3ud(cape) )
    {
        *l = *r = u3x_loob(cape);  // debug assert
    }
    else
    {
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
      && c3y == u3r_sing(data_one, data_two) )
    {
        return c3y;
    }

    if ( c3y == u3ud(data_one) )
    {
        if ( c3n == u3x_loob(cape_one) ) return c3y;
        return c3a(u3ud(cape_two),
               c3a(u3x_loob(cape_two),
                   u3r_sing(data_one, data_two)));
    }

    if ( c3y == u3ud(data_two) )
    {
        u3x_loob(cape_two);
        if ( c3n == cape_one ) return u3m_bail(c3__exit);  // normalization assert
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

void
u3d_prep_ka()
{
    if ( u3R->dir.ka ) return;
    // XX commit a trap and kick it here
    //
    u3R->dir.ka = u3s_cue_bytes((c3_d)u3_Ka_core_len, u3_Ka_core);
}

//  XX: reentrance?
//
void
u3d_rout(u3_noun sub, u3_noun fol)
{
    u3d_prep_ka();
    // ( [%wing p=~[%rout]] )
    //
    u3_noun gen = u3nt(c3__wing, c3_s4('r','o','u','t'), u3_nul);
    u3_noun vax = u3dc("slap", u3R->dir.ka, gen);
    u3_noun gat = u3k(u3t(vax));
    u3z(vax);
    u3R->dir.ka = u3n_slam_on(gat, u3nc(sub, fol));
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
    while ( u3_nul != list )
    {
        u3x_cell(list, &i, &list);
        u3x_mean(i, 4, &cape_i,
                    5, &data_i,
                    0);
        if ( c3n == _so_huge(cape_i, data_i, cape, data) ) continue;
        //  first match or better match
        //
        if ( (u3_none == pro)
              || (c3y == _so_huge(cape_max, data_max, cape_i, data_i)) )
        {
            pro = i;
            cape_max = cape_i;
            data_max = data_i;
        }
    }
    return pro;
}

//  RETAINS arguments
//
u3n_prog*
u3d_search(u3_noun sub, u3_noun fol)
{
    u3n_prog* pog_u = NULL;
    u3_weak lit = u3h_git(u3R->byc.lar_p, fol);
    if ( u3_none != lit )
    {
        u3_weak less_pog = u3d_match_sock(c3y, sub, lit);
        pog_u = ( u3_none != less_pog )
              ? u3to(u3n_prog, u3t(less_pog))
              : pog_u;
    }
    if ( pog_u ) return pog_u;

    u3d_rout(u3k(sub), u3k(fol));
    // ( [%wing p=~[%lon]] )
    //
    u3_noun gen = u3nt(c3__wing, c3_s3('l','o','n'), u3_nul);
    u3_noun vax = u3dc("slap", u3k(u3R->dir.ka), gen);
    u3_noun lon = u3k(u3t(vax));
    u3z(vax);

    // ( [%wing p=~[%cook]] )
    //
    gen = u3nt(c3__wing, c3__cook, u3_nul);
    vax = u3dc("slap", u3k(u3R->dir.ka), gen);
    u3_noun gat = u3k(u3t(vax));
    u3z(vax);

    u3_noun boil = u3n_slam_on(gat, lon);
    u3_noun cole, code, fols;
    u3r_mean(boil, 2, &cole, 6, &code, 7, &fols, 0);

    pog_u = u3n_build_direct(sub, fol, cole, code, fols);
    u3z(boil);
    return pog_u;
}