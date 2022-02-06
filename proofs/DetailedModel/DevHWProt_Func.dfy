include "Properties_DevHWProt.dfy"
include "Properties_SecureDMState.dfy"

function {:axiom} DevHWProt(orig_ws:DM_State, ws:DM_State) : (out_ws:DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(ws.objects)
        // Requirement: <ws.objects.active_*> must contain active objects only
    requires DM_IsValidState_DevsActivateCond(ws)
        // Requirement: Devices can be active or inactive, as long as they
        // fulfill DM_IsValidState_DevsActivateCond

    ensures P_DMObjectsHasUniqueIDs(out_ws.objects)
        // Properties needed by the following properties
    ensures P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_SubjsPIDsRedPID(ws, out_ws)
    ensures P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(ws, out_ws)
        // Property: <dev_hwprot> only modifies values of red TDs (excluding 
        // hardcoded TDs)
    ensures DevHWProt_ReturnGoodSnapshotOfRedTDs(ws, out_ws)
        // Property:
    ensures ws == orig_ws &&
            DM_IsValidState(orig_ws) && DM_IsSecureState(orig_ws)
                ==> out_ws == orig_ws
        // Propertry: If ws is unmodified from a secure state <orig_ws>, then out_ws == ws == orig_ws