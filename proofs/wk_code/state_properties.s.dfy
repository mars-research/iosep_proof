include "state_properties_OpsSaneStateSubset.s.dfy"
include "proof/state_map_OpsSaneStateSubset.i.dfy"

// State invariants satisfied by each WK API
predicate OpsSaneState(s:state)
{
    OpsSaneStateSubset(s) &&
    WSM_OpsSaneState_Security_SI1(s)
}

predicate {:opaque} WSM_OpsSaneState_Security_SI1(s:state)
    requires OpsSaneStateSubset(s)
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_SubjsObjsPIDs(s, dm);
    assert DM_IsValidState_SubjsObjsPIDs(dm);

    // SI1: The mapped state in the WK design spec fulfill SI1 of the WK design spec
    // [NOTE] This SI is for hardware protection mechanisms
    P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(dm) &&
        
    (true)
}

