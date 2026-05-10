#ifndef U3_DIRECT_H
#define U3_DIRECT_H

#include "error.h"
#include "hashtable.h"
#include "manage.h"
#include "nock-compile.h"
#include "nock.h"
#include "retrieve.h"
#include "serial.h"
#include "ska_verb.h"
#include "vortex.h"
#include "xtract.h"
#include "jets/k.h"

u3nc_prog*
u3d_search(u3_noun sub, u3_noun fol);

u3_weak
u3d_match_sock(u3_noun cape, u3_noun data, u3_noun list);

u3_noun
u3d_bell_ops_tot(u3_noun bell, c3_t entry_t);

void
u3d_prep_ka();

#endif /* ifndef U3_DIRECT_H */
