include "state_properties.s.dfy"
include "proof/state_map_OpsSaneState.i.dfy"

// Returns if an operation fulfills all transition constraints (TCs)
// The operation transits from <s1> to <s2>
predicate WSM_IsSecureOps(s1:state, s2:state)
    requires OpsSaneState(s1)
    requires OpsSaneState(s2)
{
    var dm1:DM_State := WSM_MapSecureState(s1);
    var dm2:DM_State := WSM_MapSecureState(s2);

    DM_IsSecureOps(dm1, dm2) && 

    WKOps_UnchangedStateVars(s1, s2)
}
