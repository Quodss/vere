/// @file

#include "jets/q.h"
#include "jets/w.h"

#include "noun.h"


  typedef struct {
    u3_noun write_fun;
    u3_noun read_fun;
    u3_noun pure_fun;
  } omon_dash;
  
  //  forward-declare mutually-recursive function
  //
  static u3_weak  // RETAIN
  _bast_bind_fun(u3_noun a,
                 u3_noun b,
                 c3_w len_w,
                 c3_y* buf_y,
                 omon_dash dash,
                 u3_noun cor
                 );

  static u3_weak  //  RETAIN
  _omon_reduce(u3_noun omon, c3_w len_w, c3_y *buf_y, omon_dash dash, u3_noun cor)
  {
    u3_noun res_hed;  // must be gained in "subjets" and shimmering

    if ( (c3y == u3r_sing(u3x_at(u3x_bat, omon), u3x_at(u3x_bat, dash.write_fun))) &&
         (c3y == u3r_sing(u3x_at(63, omon), u3x_at(63, dash.write_fun)))  //  ..write-bytes
       ) {
      u3_noun src, off, len;
      if ( (c3n == u3r_mean(omon, 124, &src, 250, &off, 251, &len, 0)) ||
           (c3n == u3a_is_cat(src))  ||
           (c3n == u3a_is_cat(off))  ||
           (c3n == u3a_is_cat(len)) ) {
        fprintf(stderr, "\r\ntype fail write\r\n");
        return u3_none;
      }
      if (off + len > len_w) return u3m_bail(c3__exit);
      u3r_bytes(0, len, buf_y+off, src);
      res_hed = u3_nul;

    } else if ( (c3y == u3r_sing(u3x_at(u3x_bat, omon), u3x_at(u3x_bat, dash.read_fun))) &&
                (c3y == u3r_sing(u3x_at(63, omon), u3x_at(63, dash.read_fun)))  // ..read-bytes
              ) {
        u3_noun off, len;
        if ( (c3n == u3r_mean(omon, 124, &off, 125, &len, 0)) ||
             (c3n == u3a_is_cat(off))  ||
             (c3n == u3a_is_cat(len)) ) {
          fprintf(stderr, "\r\ntype fail read\r\n");
          return u3_none;
        }
        if (off + len > len_w) return u3m_bail(c3__exit);
        res_hed = u3i_bytes(len, buf_y+off);

    } else if ( c3y == u3r_sing(u3x_at(u3x_bat, omon), u3x_at(u3x_bat, dash.pure_fun)) ) {
        if ( c3n == u3r_mean(omon, u3x_con_sam, &res_hed, 0) ) {
          fprintf(stderr, "\r\ntype fail pure\r\n");
          return u3_none;
        }
        u3k(res_hed);

    } else if ( c3y == u3r_sing(u3x_at(u3x_bat, omon), u3x_at(u3x_bat, cor)) ) {
        u3_noun a_a, b_a;
        if ( c3n == u3r_mean(omon, u3x_con_sam_2, &a_a, u3x_con_sam_3, &b_a, 0) ) {
          fprintf(stderr, "\r\ntype fail bind\r\n");
          return u3_none;
        }
        res_hed = u3k(_bast_bind_fun(a_a, b_a, len_w, buf_y, dash, cor));

    } else {
      fprintf(stderr, "\r\nshimmer\r\n");
      u3_noun octs_new = u3nc(len_w, u3i_bytes(len_w, buf_y));
      u3_noun res_tel, res = u3n_slam_on(u3k(omon), octs_new);
      u3x_cell(res, &res_hed, &res_tel);
      if (_(u3ud(res_tel)))      return u3m_bail(c3__fail);
      if (len_w != u3h(res_tel)) return u3m_bail(c3__fail);
      u3r_bytes(0, len_w, buf_y, u3t(res_tel));
      u3k(res_hed);
      u3z(res);
    }

    return res_hed;
  }

  static u3_weak  // RETAIN
  _bast_bind_fun(u3_noun a,
                 u3_noun b,
                 c3_w len_w,
                 c3_y* buf_y,
                 omon_dash dash,
                 u3_noun cor
                 )
  {
    for (;;) {
      u3_weak a_res_hed = _omon_reduce(a, len_w, buf_y, dash, cor);
      if ( u3_none == a_res_hed) return u3_none;
      u3_noun cont = u3n_slam_on(u3k(b), a_res_hed);
      if ( (c3y == u3r_sing(u3x_at(u3x_bat, cont), u3x_at(u3x_bat, cor))) &&
           (c3y == u3r_mean(cont, u3x_con_sam_2, &a, u3x_con_sam_3, &b, 0)) )
        {
        continue;
      } else {
        return _omon_reduce(cont, len_w, buf_y, dash, cor);
      }
    }
  }

  u3_weak
  u3we_omon_bind_fun(u3_noun cor)
  {
    u3_noun a, b, p_octs, q_octs;

    if ( c3n == u3r_mean(cor, u3x_sam_2, &p_octs,
                              u3x_sam_3, &q_octs,
                              u3x_con_sam_2, &a,
                              u3x_con_sam_3, &b,
                               0) ) {
      return u3_none;
    } else {
      if ( (c3n == u3a_is_cat(p_octs)) ||
           (c3n == u3ud(q_octs))) {
        return u3_none;
      }
      omon_dash dash = {
        u3j_kink(u3j_kink(u3k(u3at(1023, cor)), 22), 2),
        u3j_kink(u3j_kink(u3k(u3at(1023, cor)), 47), 2),
        u3j_kink(u3j_kink(u3k(u3at(127,  cor)), 10), 2)
      };
      c3_w len_w = p_octs;
      fprintf(stderr, "\r\ninit alloc\r\n");
      c3_y *buf_y = u3r_bytes_alloc(0, len_w, q_octs);
      u3_weak res_hed = _bast_bind_fun(a, b, len_w, buf_y, dash, cor);
      u3_weak res = (u3_none == res_hed)
                  ? u3_none
                  : u3nt(u3k(res_hed), len_w, u3i_bytes(len_w, buf_y));
      if (u3_none != res) {
        fprintf(stderr, "\r\nfinal alloc\r\n");
      }
      u3z(dash.read_fun); u3z(dash.write_fun); u3z(dash.pure_fun);
      u3a_free(buf_y);
      return res;
    }
  }
