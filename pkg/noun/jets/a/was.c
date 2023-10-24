/// @file

#include "jets/k.h"
#include "jets/q.h"
#include "jets/w.h"

#include "noun.h"

#include "wasm3.h"

#include <stdio.h>

  u3_atom
  u3qa_was(u3_atom bin,
           u3_atom i_arg,
           u3_atom args,
           u3_atom i_ret)
  {
    fprintf(stderr, "entered into u3qa_was\r\n");
    // What if number of arguments is more than the maximum number possible
    // of a direct atom? For now, we ignore this, we can fix this in the future.
    if ( !_(u3a_is_cat(i_arg)) ) {
      fprintf(stderr, "i_arg is not direct atom\r\n");
      return u3m_bail(c3__fail);
    }
    if ( !_(u3a_is_cat(i_ret)) ) {
      fprintf(stderr, "i_ret is not direct atom\r\n");
      return u3m_bail(c3__fail);
    }

    c3_w i_arg_w = i_arg;
    c3_w i_ret_w = i_ret;

    c3_w  len_bin, len_args;
    c3_y* bin_bytes = u3r_bytes_all(&len_bin, bin);
    c3_y* args_bytes = u3r_bytes_all(&len_args, args);
    c3_y* out_y = u3a_malloc(i_ret_w * 8);
    u3_atom out;

    IM3Environment env = m3_NewEnvironment ();
    if (!env) {
      fprintf(stderr, "env is null\r\n");
      return u3m_bail(c3__fail);
    }
    
    IM3Runtime runtime = m3_NewRuntime (env, 8192, NULL);
    if (!runtime) {
      fprintf(stderr, "runtime is null\r\n");
      return u3m_bail(c3__fail);
    }

    IM3Module module;
    M3Result result = m3_ParseModule (env, &module, bin_bytes, len_bin);
    if (result) {
      for (int i = 0; i < len_bin; i++) {
        fprintf(stderr, "%d: %u\r\n", i, bin_bytes[i]);
      }
        fprintf(stderr, "parse module error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    result = m3_LoadModule (runtime, module);
    if (result) {
      fprintf(stderr, "load module error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    IM3Function f;
    result = m3_FindFunction (&f, runtime, "main");
    if (result) {
      fprintf(stderr, "find function error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    result = m3_CallArgv (f, i_arg_w, args_bytes);
    if (result) {
      fprintf(stderr, "call argv error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    result = m3_GetResults (f, i_ret_w, &out_y);
    if (result) {
      fprintf(stderr, "get result error: %s\r\n", result);
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
  u3wa_was(u3_noun cor)
  {
    fprintf(stderr, "u3wa_was entered\r\n");
    u3_noun bin, i_arg, args, i_ret;

    if ( (c3n == u3r_mean(cor, u3x_sam_2,  &bin,
                               u3x_sam_6,  &i_arg,
                               u3x_sam_14, &args,
                               u3x_sam_15, &i_ret, 0)) ||
         (c3n == u3ud(bin)) ||
         (c3n == u3ud(i_arg)) ||
         (c3n == u3ud(args)) ||
         (c3n == u3ud(i_ret)) )
    {
        fprintf(stderr, "u3wa_was bail\r\n");
        return u3m_bail(c3__exit);
    } else {
        fprintf(stderr, "about to enter u3qa_was\r\n");
        return u3qa_was(bin, i_arg, args, i_ret);
    }
  }