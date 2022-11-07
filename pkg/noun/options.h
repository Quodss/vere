#ifndef U3_OPTIONS_H
#define U3_OPTIONS_H

  /** Data structures.
  **/
    /* u3o_role: process role.
    */
      typedef enum _u3o_role {
        u3o_sole = 0,                         //  default (util)
        u3o_mars = 1,                         //  child
        u3o_urth = 2                          //  parent
      } u3o_role;

    /* u3o_config: process / system configuration.
    */
      typedef struct _u3o_config {
        u3o_role rol_e;                       //  process role
        c3_c*    dir_c;                       //  execution directory (pier)
        c3_w     wag_w;                       //  flags (both ways)
        size_t   wor_i;                       //  loom words (<= u3a_words)
        void (*stderr_log_f)(c3_c*);          //  errors from c code
        void (*slog_f)(u3_noun);              //  function pointer for slog
        void (*sign_hold_f)(void);            //  suspend system signal regime
        void (*sign_move_f)(void);            //  restore system signal regime
      } u3o_config;

    /* u3o_flag: process/system flags.
    **
    **  _debug flags are set outside u3 and heard inside it.
    **  _check flags are set inside u3 and heard outside it.
    */
      enum u3o_flag {                         //  execution flags
        u3o_debug_ram =     1 <<  0,          //  debug: gc
        u3o_debug_cpu =     1 <<  1,          //  debug: profile
        u3o_check_corrupt = 1 <<  2,          //  check: gc memory
        u3o_check_fatal =   1 <<  3,          //  check: unrecoverable
        u3o_verbose =       1 <<  4,          //  be remarkably wordy
        u3o_dryrun =        1 <<  5,          //  don't touch checkpoint
        u3o_quiet =         1 <<  6,          //  disable ~&
        u3o_hashless =      1 <<  7,          //  disable hashboard
        u3o_trace =         1 <<  8,          //  enables trace dumping
        u3o_auto_meld =     1 <<  9,          //  enables meld under pressure
        u3o_no_demand =     1 << 10           //  disables demand paging
      };

  /** Globals.
  **/
    /* u3_Config / u3C: global memory control.
    */
      c3_global u3o_config u3o_Config;
#     define u3C u3o_Config


#endif /* ifndef U3_OPTIONS_H */
