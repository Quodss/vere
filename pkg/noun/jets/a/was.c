/// @file

#include "jets/k.h"
#include "jets/q.h"
#include "jets/w.h"

#include "noun.h"

#include "wasm3.h"

#include <stdio.h>

  u3_atom
  u3qa_was(u3_atom bin,
           u3_atom bin_len,
           u3_atom arg_len,
           u3_atom args,
           u3_atom i_ret)
  {
    fprintf(stderr, "entered into u3qa_was\r\n");
    // What if number of arguments is more than the maximum number possible
    // of a direct atom? For now, we ignore this, we can fix this in the future.
    if ( !_(u3a_is_cat(arg_len)) ) {
      fprintf(stderr, "arg_len is not direct atom\r\n");
      return u3m_bail(c3__fail);
    }
    if ( !_(u3a_is_cat(i_ret)) ) {
      fprintf(stderr, "i_ret is not direct atom\r\n");
      return u3m_bail(c3__fail);
    }

    fprintf(stderr, "completed arguments validation\r\n");

    c3_w arg_len_w = arg_len;
    c3_w i_ret_w = i_ret;
    c3_w bin_len_w = bin_len;

    fprintf(stderr, "bin_len: %d\r\n", bin_len_w);

    c3_y *bin_bytes = u3r_bytes_alloc(0, bin_len_w, bin);
    fprintf(stderr, "u3r_bytes_fit complete\r\n");

    // reverse bin_bytes, maybe endianness?
    // int temp;
    // for (int i = 0; i < bin_len_w / 2; i++) {
    //   temp = bin_bytes[i];
    //   bin_bytes[i] = bin_bytes[bin_len_w-i-1];
    //   bin_bytes[bin_len_w-i-1] = temp;
    // }

    c3_y *args_bytes = u3r_bytes_alloc(0, arg_len, args);

    char **args_bytes_normalised = (char**) u3a_calloc(3, sizeof(char *));
    char *args_bytes_0 = (char *)u3a_calloc(2, sizeof(char));
    args_bytes_0[0] = 42;
    args_bytes_0[1] = '\0';
    char *args_bytes_1 = (char *)u3a_calloc(2, sizeof(char));
    args_bytes_1[0] = 42;
    args_bytes_1[1] = '\0';
    args_bytes_normalised[0] = args_bytes_0;
    args_bytes_normalised[1] = args_bytes_1;
    args_bytes_normalised[2] = NULL;

    c3_y *out_y = u3a_malloc(i_ret_w * 8);
    u3_atom out;

    IM3Environment env = m3_NewEnvironment ();
    if (!env) {
      fprintf(stderr, "env is null\r\n");
      return u3m_bail(c3__fail);
    }

    fprintf(stderr, "env computed\r\n");
    
    IM3Runtime runtime = m3_NewRuntime (env, 8192, NULL);
    if (!runtime) {
      fprintf(stderr, "runtime is null\r\n");
      return u3m_bail(c3__fail);
    }

    fprintf(stderr, "runtime computed\r\n");

    IM3Module module;
    M3Result result = m3_ParseModule (env, &module, bin_bytes, bin_len_w);
    if (result) {
      fprintf(stderr, "parse module error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    fprintf(stderr, "module parsed\r\n");

    result = m3_LoadModule (runtime, module);
    if (result) {
      fprintf(stderr, "load module error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    fprintf(stderr, "module loaded\r\n");

    IM3Function f;
    result = m3_FindFunction (&f, runtime, "main");
    if (result) {
      fprintf(stderr, "find function error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    fprintf(stderr, "main function found\r\n");

    result = m3_CallArgv (f, arg_len_w, args_bytes_normalised);
    if (result) {
      fprintf(stderr, "call argv error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    fprintf(stderr, "call argv successful\r\n");

    // uint64_t    valbuff[128];
    // const void* valptrs[128];
    // memset(valbuff, 0, sizeof(valbuff));
    // for (int i = 0; i < 1; i++) {
    //     valptrs[i] = &valbuff[i];
    // }

    c3_d **valptrs = (c3_d **) u3a_calloc(2, sizeof(c3_d*));
    c3_d *out_d = (c3_d *) u3a_calloc(1, sizeof(c3_d));
    valptrs[0] = out_d;
    valptrs[1] = NULL;

    result = m3_GetResults (f, 1, valptrs);
    if (result) {
      fprintf(stderr, "get result error: %s\r\n", result);
      return u3m_bail(c3__fail);
    }

    fprintf(stderr, "results got: %llu\r\n", valptrs[0][0]);

    out = u3i_bytes(i_ret_w * 8, valptrs[0]);
    u3k(out);
    u3a_free(out_y);
    u3a_free(bin_bytes);
    u3a_free(args_bytes);

    u3a_free(args_bytes_normalised);
    u3a_free(args_bytes_0);
    u3a_free(args_bytes_1);

    u3a_free(out_d);
    u3a_free(valptrs);

    return out;
  }

  u3_noun
  u3wa_was(u3_noun cor)
  {
    fprintf(stderr, "u3wa_was entered\r\n");
    u3_noun bin, bin_len, arg_len, args, i_ret;

    if ( (c3n == u3r_mean(cor, u3x_sam_2,  &bin,
                               u3x_sam_6,  &bin_len,
                               u3x_sam_14, &arg_len,
                               u3x_sam_30, &args,
                               u3x_sam_31, &i_ret, 0)) ||
         (c3n == u3ud(bin)) ||
         (c3n == u3ud(arg_len)) ||
         (c3n == u3ud(args)) ||
         (c3n == u3ud(i_ret)) )
    {
        fprintf(stderr, "u3wa_was bail\r\n");
        return u3m_bail(c3__exit);
    } else {
        fprintf(stderr, "about to enter u3qa_was\r\n");
        return u3qa_was(bin, bin_len, arg_len, args, i_ret);
    }
  }