/// @file

#include "jets/k.h"
#include "jets/q.h"
#include "jets/w.h"

#include "noun.h"

  static u3_atom
  _cqe_interpret(u3_atom bin,
                 u3_atom i_arg,
                 u3_atom args,
                 u3_atom i_ret)
  {
    if ( !_(u3a_is_cat(i_arg)) ) {
      return u3m_bail(c3__fail);
    }
    c3_w i_arg_w = i_arg;
    c3_w i_ret_w = i_ret;
    c3_w  len_bin, len_args;
    c3_y* bin_bytes = u3r_bytes_all(&len_w, bin);
    c3_y* args_bytes = u3r_bytes_all(&len_args, args);
    c3_y* out_y = u3a_malloc(i_ret_w * 8);
    u3_atom out;

    IM3Environment env = m3_NewEnvironment ();
    if (!env) {
      return u3m_bail(c3__fail);
    }
    
    IM3Runtime runtime = m3_NewRuntime (env, 8192, NULL);
    if (!runtime) {
      return u3m_bail(c3__fail);
    }

    IM3Module module;
    result = m3_ParseModule (env, &module, bin_bytes, (len_bin));
    if (result) {
      return u3m_bail(c3__fail);
    }

    result = m3_LoadModule (runtime, module);
    if (result) {
      return u3m_bail(c3__fail);
    }

    IM3Function f;
    result = m3_FindFunction (&f, runtime, "main");
    if (result) {
      return u3m_bail(c3__fail);
    }

    result = m3_CallArgv (f, i_arg_w, args_bytes);
    if (result) {
      return u3m_bail(c3__fail);
    }

    result = m3_GetResults (f, i_ret_w, &out_y);
    if (result) {
      return u3m_bail(c3__fail);
    }

    out = u3i_bytes(i_ret_w * 8, out_y);
    u3k(out);
    u3a_free(out_y);
    u3a_free(bin_bytes);
    u3a_free(args_bytes);
    
    return out;
  }

  u3_noun
  u3we_interpret(u3_noun cor)
  {
    u3_noun bin, i_arg, args, i_ret;
    if ( (u3_none == (bin = u3r_at(u3x_sam_2, cor)))    ||
         (u3_none == (i_arg = u3r_at(u3x_sam_6, cor)))  ||
         (u3_none == (args = u3r_at(u3x_sam_14, cor)))  ||
         (u3_none == (i_ret = u3r_at(u3x_sam_15, cor))) ||
         (c3n == u3ud(bin))   ||
         (c3n == u3ud(i_arg)) ||
         (c3n == u3ud(args))  ||
         (c3n == u3ud(i_ret)) )
    {
        return u3m_bail(c3__exit);
    } else {
        return _cqe_interpret(bin, i_arg, args, i_ret);
    }
  }