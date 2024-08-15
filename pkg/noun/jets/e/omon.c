/// @file

#include "jets/q.h"
#include "jets/w.h"

#include "noun.h"


  typedef struct {
    u3_noun write_fun;
    u3_noun read_fun;
  } omon_dash;

  static u3_weak  // RETAIN
  _bast_bind_fun(u3_noun a,
                 u3_noun b,
                 c3_w len_w,
                 c3_y* buf_y,
                 omon_dash dash,
                 u3_noun cor
                 ) {
    //  route on a
    //
    for (;;) {
      u3_noun a_res_hed;
      if ( (c3y == u3r_sing(u3x_at(u3x_bat, a), u3x_at(u3x_bat, dash.write_fun))) &&
           (c3y == u3r_sing(u3x_at(63, a), u3x_at(63, dash.write_fun)))  //  ..write-bytes
          ) {
        u3_noun src, off, len;
        if ( (c3n == u3r_mean(a, 124, &src, 250, &off, 251, &len, 0)) ||
            (c3n == u3a_is_cat(src)) ||
            (c3n == u3a_is_cat(off)) ||
            (c3n == u3a_is_cat(len)) ) {
          return u3_none;
        }
        if (off + len > len_w) return u3m_bail(c3__exit);
        u3r_bytes(0, len, buf_y+off, src);
        a_res_hed = u3_nul;
      } else if ( (c3y == u3r_sing(u3x_at(u3x_bat, a), u3x_at(u3x_bat, dash.read_fun))) &&
                  (c3y == u3r_sing(u3x_at(63, a), u3x_at(63, dash.read_fun)))  // ..read-bytes
                ) {
        u3_noun off, len;
        if ( (c3n == u3r_mean(a, 124, &off, 125, &len, 0)) ||
             (c3n == u3a_is_cat(off)) ||
             (c3n == u3a_is_cat(len)) ) {
          return u3_none;
        }
        if (off + len > len_w) return u3m_bail(c3__exit);
        a_res_hed = u3i_bytes(len, buf_y+off);
      } else {
        // fprintf(stderr, "\r\nshimmer a\r\n");
        u3_noun octs_new = u3nc(len_w, u3i_bytes(len_w, buf_y));
        u3_noun a_res_tel, a_res = u3n_slam_on(u3k(a), octs_new);
        u3x_cell(a_res, &a_res_hed, &a_res_tel);
        u3_noun cont = u3n_slam_on(u3k(b), u3k(a_res_hed));
        return u3n_slam_on(cont, u3k(a_res_tel));
      }
      //  route on (b c)
      //
      u3_noun cont = u3n_slam_on(u3k(b), a_res_hed);
      if ( (c3y == u3r_sing(u3x_at(u3x_bat, cont), u3x_at(u3x_bat, cor))) &&
           (c3y == u3r_mean(cont, u3x_con_sam_2, &a, u3x_con_sam_3, &b, 0))
      ) {
        continue;
      }
      else {
        // fprintf(stderr, "\r\nshimmer (b c)\r\n");
        return u3n_slam_on(cont, u3nc(len_w, u3i_bytes(len_w, buf_y)));
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
        u3j_kink(u3j_kink(u3k(u3at(1023, cor)), 47), 2)
      };
      c3_w len_w = p_octs;
      c3_y *buf_y = u3r_bytes_alloc(0, len_w, q_octs);
      u3_weak res = _bast_bind_fun(a, b, len_w, buf_y, dash, cor);
      u3z(dash.read_fun); u3z(dash.write_fun);
      u3a_free(buf_y);
      return res;
    }
  }
