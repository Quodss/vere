/// @file

#include "jets/k.h"
#include "jets/q.h"
#include "jets/w.h"

#include "noun.h"

#include "wasm3.h"
#include "m3_env.h"

#include <stdio.h>
#include <math.h>

  char *
  int_to_string(uint64_t num)
  {
    char *str = u3a_malloc((ceil(log10(num)) + 1) * sizeof(char));
    sprintf(str, "%d", num);
    return str;
  }

  // The returned atom is an array of return values similar to args in its 
  // structure (8 bytes for each value, no type info).
  u3_atom
  u3qa_was(u3_atom bin,
           u3_atom bin_len,
           u3_atom fun_id,
           u3_atom arg_len,
           u3_atom args,     // little endian concatenation, 8 bytes each
           u3_atom ret_len)
  {
    // What if number of arguments is more than the maximum number possible
    // of a direct atom? For now, we ignore this, we can fix this in the future.
    if ( !_(u3a_is_cat(arg_len)) ) {
      fprintf(stderr, "arg_len is not direct atom\r\n");
      return u3m_bail(c3__fail);
    }
    if ( !_(u3a_is_cat(ret_len)) ) {
      fprintf(stderr, "ret_len is not direct atom\r\n");
      return u3m_bail(c3__fail);
    }

    // Does it matter if fun_id is more than 32 bits? Should check...
    c3_w  fun_id_w = fun_id;
    c3_w arg_len_w = arg_len;
    c3_w ret_len_w = ret_len;
    c3_w bin_len_w = bin_len;

    c3_y *bin_bytes = u3r_bytes_alloc(0, bin_len_w, bin);

    // Arguments must be serialized into string for function call.
    c3_y *args_bytes = u3r_bytes_alloc(0, arg_len_w * 8, args);

    const char *str_inputs[arg_len_w];
    for (int i = 0; i < arg_len_w; i++) {
      str_inputs[i] = int_to_string(args_bytes[i * 8]);
    }

    c3_y *out_y = u3a_malloc(ret_len_w * 8);
    u3_atom out;

    IM3Environment env = m3_NewEnvironment ();
    if (!env) {
      fprintf(stderr, "env is null\r\n");
      return u3m_bail(c3__fail);
    }
    
    IM3Runtime runtime = m3_NewRuntime (env, 2097152, NULL);
    if (!runtime) {
      fprintf(stderr, "runtime is null\r\n");
      return u3m_bail(c3__fail);
    }

    IM3Module module;
    M3Result result = m3_ParseModule (env, &module, bin_bytes, bin_len_w);
    if (result) {
      fprintf(stderr, "parse module error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    result = m3_LoadModule (runtime, module);
    if (result) {
      fprintf(stderr, "load module error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    IM3Function f = Module_GetFunction(module, fun_id_w);
    CompileFunction(f);

    result = m3_CallArgv (f, arg_len_w, str_inputs);
    if (result) {
      fprintf(stderr, "call argv error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    // output array strategy taken from:
    // https://github.com/wasm3/wasm3/blob/main/platforms/app/main.c
    c3_d **valptrs = (c3_d **) u3a_calloc(ret_len_w, sizeof(c3_d*));
    c3_d *valbuff = (c3_d *)u3a_calloc(ret_len_w, sizeof(c3_d));

    for (int i = 0; i < ret_len_w; i++) {
      valptrs[i] = &valbuff[i];
    }

    result = m3_GetResults(f, ret_len_w, valptrs);
    if (result) {
      fprintf(stderr, "get result error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    // Is it bad that we are passing in an 8-byte when it expects 1?
    out = u3i_chubs(ret_len_w, valbuff);
    u3k(out);
    u3a_free(out_y);
    u3a_free(bin_bytes);
    u3a_free(args_bytes);

    for (int i = 0; i < arg_len_w; i++) {
      u3a_free(str_inputs[i]);
    }

    u3a_free(valptrs);
    u3a_free(valbuff);

    return out;
  }

  u3_noun
  u3wa_was(u3_noun cor)
  {
    u3_noun bin, bin_len, fun_id, arg_len, args, ret_len;

    if ( (c3n == u3r_mean(cor, u3x_sam_2,  &bin,
                               u3x_sam_6,  &bin_len,
                               u3x_sam_14, &fun_id,
                               u3x_sam_30, &arg_len,
                               u3x_sam_62, &args,
                               u3x_sam_63, &ret_len, 0)) ||
         (c3n == u3ud(bin)) ||
         (c3n == u3ud(bin_len)) ||
         (c3n == u3ud(fun_id)) ||
         (c3n == u3ud(arg_len)) ||
         (c3n == u3ud(args)) ||
         (c3n == u3ud(ret_len)) )
    {
        fprintf(stderr, "u3wa_was bail\r\n");
        return u3m_bail(c3__exit);
    } else {
        return u3qa_was(bin, bin_len, fun_id, arg_len, args, ret_len);
    }
  }
