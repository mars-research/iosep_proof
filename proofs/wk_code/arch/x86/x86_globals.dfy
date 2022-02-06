include "../../utils/common/headers.dfy"
include "x86_mstate.dfy"

/*********************** Interface Realizations - Memory Address ********************/

// Interface realization: <wkm_get_globals>
function method wkm_get_globals(wkm:WK_MState) : globalsmap
{
    wkm.globals
}





