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

c3_y
u3d_bell_number_args(u3_noun bell);

#endif /* ifndef U3_DIRECT_H */