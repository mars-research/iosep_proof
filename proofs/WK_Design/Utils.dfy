include "../DetailedModel/Model.dfy"
include "DM_AdditionalPropertiesLemmas.dfy"
include "Utils.dafny21.dfy"

lemma Lemma_SeqSameIndexYieldSameElem<T>(s:seq<T>, a:int, b:int)
    requires a == b
    requires 0<a<|s|
    
    ensures s[a] == s[b]
{
    // Dafny can automatically prove this lemma
}




//******** Activate Multiple Subjects/Objects ********//
function method WSD_HCodedTDsOwnedByDevs(ws:DM_State, dev_ids:set<Dev_ID>) : (result:set<TD_ID>)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && ws.subjects.devs[dev_id].hcoded_td_id == id)
    ensures forall dev_id :: dev_id in dev_ids 
                ==> ws.subjects.devs[dev_id].hcoded_td_id in result
{
    set dev_id | dev_id in dev_ids :: ws.subjects.devs[dev_id].hcoded_td_id
}

function method WSD_TDsOwnedByDevs(ws:DM_State, dev_ids:set<Dev_ID>) : (result:set<TD_ID>)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && id in ws.subjects.devs[dev_id].td_ids)
    ensures forall dev_id :: dev_id in dev_ids 
                ==> ws.subjects.devs[dev_id].td_ids <= result
{
    var s := set dev_id, td_id | dev_id in dev_ids &&
                        td_id in ws.subjects.devs[dev_id].td_ids 
                    :: td_id ;

    Lemma_WSD_TDsOwnedByDevs_Prove(ws, dev_ids, s);

    s
}

function method WSD_FDsOwnedByDevs(ws:DM_State, dev_ids:set<Dev_ID>) : (result:set<FD_ID>)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && id in ws.subjects.devs[dev_id].fd_ids)
    ensures forall dev_id :: dev_id in dev_ids 
                ==> ws.subjects.devs[dev_id].fd_ids <= result
{
    var s := set dev_id, fd_id | dev_id in dev_ids &&
                        fd_id in ws.subjects.devs[dev_id].fd_ids 
                    :: fd_id ;

    Lemma_WSD_FDsOwnedByDevs_Prove(ws, dev_ids, s);

    s
}

function method WSD_DOsOwnedByDevs(ws:DM_State, dev_ids:set<Dev_ID>) : (result:set<DO_ID>)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && id in ws.subjects.devs[dev_id].do_ids)
    ensures forall dev_id :: dev_id in dev_ids 
                ==> ws.subjects.devs[dev_id].do_ids <= result
{
    var s := set dev_id, do_id | dev_id in dev_ids &&
                        do_id in ws.subjects.devs[dev_id].do_ids 
                    :: do_id ;

    Lemma_WSD_DOsOwnedByDevs_Prove(ws, dev_ids, s);

    s
}




//******** Private Lemmas of Utility Functions ********//
lemma Lemma_WSD_TDsOwnedByDevs_Prove(ws:DM_State, dev_ids:set<Dev_ID>, s:set<TD_ID>)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    requires s == (set dev_id, td_id | dev_id in dev_ids &&
                        td_id in ws.subjects.devs[dev_id].td_ids 
                    :: td_id)

    ensures forall dev_id :: dev_id in dev_ids 
                ==> ws.subjects.devs[dev_id].td_ids <= s
{
    forall dev_id | dev_id in dev_ids 
        ensures ws.subjects.devs[dev_id].td_ids <= s
    {
        assert forall td_id :: td_id in ws.subjects.devs[dev_id].td_ids 
                ==> td_id in s;
    }
}

lemma Lemma_WSD_FDsOwnedByDevs_Prove(ws:DM_State, dev_ids:set<Dev_ID>, s:set<FD_ID>)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    requires s == (set dev_id, fd_id | dev_id in dev_ids &&
                        fd_id in ws.subjects.devs[dev_id].fd_ids 
                    :: fd_id)

    ensures forall dev_id :: dev_id in dev_ids 
                ==> ws.subjects.devs[dev_id].fd_ids <= s
{
    forall dev_id | dev_id in dev_ids 
        ensures ws.subjects.devs[dev_id].fd_ids <= s
    {
        assert forall fd_id :: fd_id in ws.subjects.devs[dev_id].fd_ids 
                ==> fd_id in s;
    }
}

lemma Lemma_WSD_DOsOwnedByDevs_Prove(ws:DM_State, dev_ids:set<Dev_ID>, s:set<DO_ID>)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    requires s == (set dev_id, do_id | dev_id in dev_ids &&
                        do_id in ws.subjects.devs[dev_id].do_ids 
                    :: do_id)

    ensures forall dev_id :: dev_id in dev_ids 
                ==> ws.subjects.devs[dev_id].do_ids <= s
{
    forall dev_id | dev_id in dev_ids 
        ensures ws.subjects.devs[dev_id].do_ids <= s
    {
        assert forall do_id :: do_id in ws.subjects.devs[dev_id].do_ids 
                ==> do_id in s;
    }
}




lemma Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_EquivilantEndOfSeq(
    t_detailed:DM_Trace_Detailed, t2_detailed:DM_Trace_Detailed, seq1:seq<DM_State>, seq2:seq<DM_State>
)
    requires |t_detailed.states| > 0
    requires |t2_detailed.states| > 0
    requires t_detailed.states[|t_detailed.states|-1] == t2_detailed.states[|t2_detailed.states|-1]
    requires seq1 == t_detailed.states
    requires seq2 == t2_detailed.states
    
    ensures seq1[|seq1|-1] == seq2[|seq2|-1]
{
    // Dafny can automatically prove this lemma
}



//******** Private Lemmas of Operations ********//
/*
lemma Lemma_WK_WimpDrvsDevs_Registration_ProveValidTrace_AfterActivateExternalObjsToGreenPartition(
    last_ws:DM_State, t:DM_Trace,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(last_ws) && DM_IsSecureState(last_ws)

    requires to_assign_external_td_ids <= DM_AllTDIDs(last_ws.objects)
    requires to_assign_external_fd_ids <= DM_AllFDIDs(last_ws.objects)
    requires to_assign_external_do_ids <= DM_AllDOIDs(last_ws.objects)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(last_ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DM_DoOwnObj(last_ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    requires t == DM_Trace(last_ws, [DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid)])
    
    requires green_pid != NULL
    requires green_pid != last_ws.red_pid
    requires green_pid in last_ws.pids
        // Requirement: We have already create a green partition

    ensures DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
    ensures DM_IsValidTrace(t)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WK_WimpDrvsDevs_Unregistration_ProveValidTrace_AfterDestroyPartition(
    last_ws:DM_State, t:DM_Trace,
    green_pid:Partition_ID
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(last_ws) && DM_IsSecureState(last_ws)


    requires t == DM_Trace(last_ws, [DM_EmptyPartitionDestroyOp(green_pid)])
    
    requires green_pid != NULL
    requires green_pid != last_ws.red_pid

    ensures DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
    ensures DM_IsValidTrace(t)
{
    // Dafny can automatically prove this lemma
}



// (needs 80s to verify)
lemma Lemma_WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProveSameTransitionContraintOverInputAndOutputState(
    ws:DM_State, ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State,
    to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
    requires DM_IsValidState(ws)

    requires to_deactivate_dev_id in ws.subjects.devs

    requires forall id :: id in to_assign_drv_ids ==> id in ws.subjects.drvs
    requires forall id :: id in to_assign_dev_ids ==> id in ws.subjects.devs

    requires to_assign_external_td_ids <= DM_AllTDIDs(ws.objects)
    requires to_assign_external_fd_ids <= DM_AllFDIDs(ws.objects)
    requires to_assign_external_do_ids <= DM_AllDOIDs(ws.objects)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: We have already create a green partition

    requires DM_IsSecureOps(ws, ws2)
    requires P_DevDeactivate_ModificationToState(DMStateToState(ws), to_deactivate_dev_id.sid, DMStateToState(ws2))
        // From device deactivation
    requires P_DMObjectsHasUniqueIDs(ws3.objects)
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws2, ws3, SeqToSet(to_assign_dev_ids), green_pid)
        // From devices activation
    requires P_DMObjectsHasUniqueIDs(ws4.objects)
    requires P_WSD_DrvActivate_Multi_ObjModifications(ws3, ws4, SeqToSet(to_assign_drv_ids), green_pid)
        // From drivers activation
    requires DM_IsValidState(ws4) //&& DM_IsSecureState(ws4)
    requires DM_IsSecureOps(ws4, ws5)
    requires IsValidState(DMStateToState(ws4))
    requires to_assign_external_td_ids <= AllTDIDs(DMStateToState(ws4).objects)
    requires to_assign_external_fd_ids <= AllFDIDs(DMStateToState(ws4).objects)
    requires to_assign_external_do_ids <= AllDOIDs(DMStateToState(ws4).objects)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(DMStateToState(ws4).subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DoOwnObj(DMStateToState(ws4), s_id, o_id)
        // Requirement: no subject owns these external objects
    requires P_ExternalObjsActivate_ModificationToState(DMStateToState(ws4), 
                    to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, DMStateToState(ws5))

    ensures DM_IsSecureOps(ws, ws5)
{
    assert DM_IsSecureOps(ws, ws2);
    assert DM_IsSecureOps(ws, ws3);
    assert DM_IsSecureOps(ws, ws4);
    assert DM_IsSecureOps(ws, ws5);
}




// (needs 60s to verify)
lemma Lemma_WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs_ProveSameTransitionContraintOverInputAndOutputState(
    ws:DM_State, ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State,
    to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
    requires DM_IsValidState(ws)

    requires forall id :: id in to_deactivate_drv_ids ==> id in ws.subjects.drvs
    requires forall id :: id in to_deactivate_dev_ids ==> id in ws.subjects.devs
    requires forall id :: id in devs_to_activate_in_red ==> id in ws.subjects.devs

    requires to_deactivate_external_td_ids <= DM_AllTDIDs(ws.objects)
    requires to_deactivate_external_fd_ids <= DM_AllFDIDs(ws.objects)
    requires to_deactivate_external_do_ids <= DM_AllDOIDs(ws.objects)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_deactivate_external_td_ids) + FDIDsToObjIDs(to_deactivate_external_fd_ids) + DOIDsToObjIDs(to_deactivate_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: We have already create a green partition

    requires DM_IsSecureOps(ws, ws2)
    requires P_ExternalObjsDeactivate_ModificationToState(DMStateToState(ws), DMStateToState(ws2),
                    to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids)
        // From external objects deactivation
    requires P_DMObjectsHasUniqueIDs(ws3.objects)
    requires P_WSD_DrvDevDeactivate_Multi_ObjModifications(ws2, ws3, DrvIDsToSubjIDs(SeqToSet(to_deactivate_drv_ids)))
        // From drivers deactivation
    requires P_DMObjectsHasUniqueIDs(ws4.objects)
    requires P_WSD_DrvDevDeactivate_Multi_ObjModifications(ws3, ws4, DevIDsToSubjIDs(SeqToSet(to_deactivate_dev_ids)))
        // From devices deactivation
    requires P_DMObjectsHasUniqueIDs(ws5.objects)
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws4, ws5, SeqToSet(devs_to_activate_in_red), ws.red_pid)
        // From devices activation

    ensures DM_IsSecureOps(ws, ws5)
{
    assert DM_IsSecureOps(ws, ws2);
    assert DM_IsSecureOps(ws, ws3);
    assert DM_IsSecureOps(ws, ws4);
    assert DM_IsSecureOps(ws, ws5);
}
*/

lemma Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_ProvePropertiesWhenT2HasMultipleElems(
    t_detailed:DM_Trace_Detailed, t1_detailed:DM_Trace_Detailed, t2_detailed:DM_Trace_Detailed, i:int
)
    requires var s_t := |t_detailed.states|;
             var s_t1 := |t1_detailed.states|;
             var s_t2 := |t2_detailed.states|;
             0 <= i < |t_detailed.states| &&
             0 <= i+1-s_t1 < |t2_detailed.states| &&
             s_t - s_t1 == s_t2 - 1 &&
             t_detailed.states[i] == t2_detailed.states[i+1-s_t1] &&
             i == s_t - 1

    ensures var s_t := |t_detailed.states|;
            var s_t1 := |t1_detailed.states|;
            var s_t2 := |t2_detailed.states|;
            t_detailed.states[s_t-1] == t2_detailed.states[s_t2-1]
{
    // Dafny can automatically prove this lemma
}