include "../Abstract/Properties.dfy"
include "../Abstract/Lemmas_Ops.dfy"
include "Utils.dfy"
include "./utils/Collections.dfy"
include "Properties_ValidDMState.dfy"
include "K_AdditionalPropertiesLemmas.dfy"

predicate P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws:DM_State, ws':DM_State)
{
    // Same subject IDs
    MapGetKeys(ws'.subjects.drvs) == MapGetKeys(ws.subjects.drvs) &&
    MapGetKeys(ws'.subjects.devs) == MapGetKeys(ws.subjects.devs) &&

    // Same object ownership
    (forall id :: id in ws'.subjects.drvs 
        ==> (ws'.subjects.drvs[id].td_ids == ws.subjects.drvs[id].td_ids) &&
            (ws'.subjects.drvs[id].fd_ids == ws.subjects.drvs[id].fd_ids) &&
            (ws'.subjects.drvs[id].do_ids == ws.subjects.drvs[id].do_ids)) &&
    (forall id :: id in ws'.subjects.devs 
        ==> (ws'.subjects.devs[id].hcoded_td_id == ws.subjects.devs[id].hcoded_td_id) &&
            (ws'.subjects.devs[id].td_ids == ws.subjects.devs[id].td_ids) &&
            (ws'.subjects.devs[id].fd_ids == ws.subjects.devs[id].fd_ids) &&
            (ws'.subjects.devs[id].do_ids == ws.subjects.devs[id].do_ids)) &&

    (true)
}

predicate P_AllHCodedTDsAreObjs(ws:DM_State)
{
    (forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id in ws.subjects.devs[dev_id].td_ids) &&
        // Requirement: Hardcoded TDs are in devices
    (forall dev_id, td_id :: 
                dev_id in ws.subjects.devs && td_id in ws.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(ws.objects)) &&
    (MapGetKeys(ws.objects.hcoded_tds) == DM_AllHCodedTDIDs(ws.subjects))
}

predicate P_DMAndNewDM_SameObjectID(ws:DM_State, ws':DM_State)
    requires P_AllHCodedTDsAreObjs(ws)
{
    // Same object IDs
    (AllTDIDs(ws'.objects) == AllTDIDs(ws.objects) &&
     AllFDIDs(ws'.objects) == AllFDIDs(ws.objects) &&
     AllDOIDs(ws'.objects) == AllDOIDs(ws.objects)) &&
     MapGetKeys(ws'.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds) &&

    // Same hardcoded TD Values
    (forall id :: id in DM_AllHCodedTDIDs(ws.subjects) ==> ws.objects.hcoded_tds[id].val == ws'.objects.hcoded_tds[id].val) &&

    // Same <tds_to_all_states>
    (ws'.tds_to_all_states == ws.tds_to_all_states) &&

    (true)
}

predicate P_DMAndNewDM_SameSubjObjPID(ws:DM_State, ws':DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
        // Requirement: Objects have different internal IDs

    requires P_AllHCodedTDsAreObjs(ws)
    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')
{
    // Same Subjects' PIDs
    (forall id :: id in ws'.subjects.drvs
        ==> ws'.subjects.drvs[id].pid == ws.subjects.drvs[id].pid) &&
    (forall id :: id in ws'.subjects.devs
        ==> ws'.subjects.devs[id].pid == ws.subjects.devs[id].pid) &&

    // Same Objects' PIDs
    (forall id :: id in AllTDIDs(ws'.objects)
        ==> ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid)) &&
    (forall id :: id in AllFDIDs(ws'.objects)
        ==> ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid)) &&
    (forall id :: id in AllDOIDs(ws'.objects)
        ==> ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid)) &&

    (true)
}

lemma Lemma_DM_ValidState_ProveP_DMSubjectsHasUniqueIDs(ws:DM_State)
    requires DM_IsValidState(ws)
    ensures P_DMSubjectsHasUniqueIDs(ws.subjects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws:DM_State)
    requires DM_IsValidState(ws)

    ensures var k := DMStateToState(ws);
            K_UniqueIDsAndOwnedObjs(k.subjects, AllTDIDs(k.objects), AllFDIDs(k.objects), AllDOIDs(k.objects))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_GreenTDsMustBeInActiveTDsState(ws:DM_State, k:State)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)

    requires k == DMStateToState(ws)

    ensures forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> td_id in ActiveTDsState(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws:DM_State, ws':DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
        // Requirement: Objects have different internal IDs
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(ws'.objects)

    requires DM_IsValidState_SubjsObjsPIDs(ws)

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    ensures DM_IsValidState_Subjects(ws')
    ensures DM_IsValidState_Objects(ws')

    ensures DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    ensures DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    ensures DM_AllHCodedTDIDs(ws'.subjects) == DM_AllHCodedTDIDs(ws.subjects)

    ensures DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects)
    ensures DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects)
    ensures DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects)
{
    var k := DMStateToState(ws);
    var k' := DMStateToState(ws');

    // Prove DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    Lemma_SameAllSubjsIDsBetweenStates(k, k'.subjects);
    assert DM_AllSubjsIDs(ws.subjects) == AllSubjsIDs(ws.subjects);
    assert DM_AllSubjsIDs(ws'.subjects) == AllSubjsIDs(ws'.subjects);

    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'.subjects, k'.objects);
    Lemma_NewK_FulfillIsValidStateObjects(k, k');
}

lemma Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws:DM_State, ws':DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
        // Requirement: Objects have different internal IDs
    requires DM_IsValidState_ObjIDs(ws)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_AllHCodedTDsAreObjs(ws)

    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')
    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjObjPID(ws, ws')

    ensures forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_SubjPID(ws'.subjects, s_id) == DM_SubjPID(ws.subjects, s_id)
    ensures forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id)

    ensures DM_AllActiveSubjs(ws'.subjects) == DM_AllActiveSubjs(ws.subjects)
    ensures DM_AllActiveDevs(ws'.subjects) == DM_AllActiveDevs(ws.subjects)
{
    reveal IsValidState_Objects_UniqueObjIDs();
    assert DM_BuildMap_ObjIDsToPIDs(ws'.objects) == DM_BuildMap_ObjIDsToPIDs(ws.objects);
}




//******** From NewK ********//
lemma Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws':DM_State, k':State)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_ObjIDs(ws')

    requires IsValidState_Subjects(k') && IsValidState_Objects(k') && 
            IsValidState_Partitions(k') && IsValidState_SubjsOwnObjsThenInSamePartition(k')
    requires k' == DMStateToState(ws')

    ensures DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
{
    Lemma_K_ProveIsValidState_SubjsOwnObjsThenInSamePartition(k');
    assert forall s_id, o_id :: s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
                ==> o_id in AllObjsIDs(k'.objects) &&
                    SubjPID(k', s_id) == ObjPID(k', o_id);
    
    // Prove the property
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws', k');
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws', k');

    Lemma_DM_ObjsInSubjsAreAlsoInState(ws');

    forall s_id, o_id | s_id in DM_AllSubjsIDs(ws'.subjects) && DM_DoOwnObj(ws'.subjects, s_id, o_id)
        ensures DM_SubjPID(ws'.subjects, s_id) == DM_ObjPID(ws'.objects, o_id)
    {
        assert s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id);
    }
}




//******** Important Sub-Lemmas ********//
lemma Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(
    ws:DM_State, ws':DM_State
)
    requires DM_IsValidState_DevsActivateCond(ws)

    requires ws'.devs_activatecond == ws.devs_activatecond
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid

    requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    requires forall id :: id in ws.subjects.devs
                ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)

    ensures DM_IsValidState_DevsActivateCond(ws')
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_FulFillIsValidState_SubjsOwnObjsThenInSamePartition_IfPIDsAreUnchanged(
    ws:DM_State, ws':DM_State
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_AllHCodedTDsAreObjs(ws)
    requires P_ObjsInSubjsAreInSetOfAllObjs(ws.subjects, ws.objects)

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')
    
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)

    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)

    requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    requires DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_DoOwnObj(ws'.subjects, s_id, o_id) == DM_DoOwnObj(ws.subjects, s_id, o_id)
    requires forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_SubjPID(ws'.subjects, s_id) == DM_SubjPID(ws.subjects, s_id)
    requires forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id) 

    ensures P_ObjsInSubjsAreInSetOfAllObjs(ws'.subjects, ws'.objects)
    ensures DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
{
    var k := DMStateToState(ws);

    Lemma_DM_ObjsInSubjsAreAlsoInState(ws);

    // Prove property 2
    forall s_id, o_id | s_id in DM_AllSubjsIDs(ws'.subjects) && DM_DoOwnObj(ws'.subjects, s_id, o_id)
        ensures DM_SubjPID(ws'.subjects, s_id) == DM_ObjPID(ws'.objects, o_id)
    {
        assert s_id in DM_AllSubjsIDs(ws.subjects);
        assert DM_DoOwnObj(ws.subjects, s_id, o_id);

        assert DoOwnObj(k, s_id, o_id);
        assert SubjPID(k, s_id) == ObjPID(k, o_id);

        assert DM_SubjPID(ws.subjects, s_id) == DM_ObjPID(ws.objects, o_id);
    }
}

// [NOTE] Needs 110s to verify
lemma Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(
    ws:DM_State, k:State, ws':DM_State, k':State
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_Objects(ws')
    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id)

    requires ws'.red_pid == ws.red_pid
    requires DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)

    requires forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> ObjStateUnchanged_TD(ws.objects, ws'.objects, td_id)
    requires forall fd_id :: fd_id in DM_FDIDsInGreen(ws)
                ==> ObjPID_KObjects(ws'.objects, fd_id.oid) == ObjPID_KObjects(ws.objects, fd_id.oid)
    requires forall do_id :: do_id in DM_DOIDsInGreen(ws)
                ==> ObjPID_KObjects(ws'.objects, do_id.oid) == ObjPID_KObjects(ws.objects, do_id.oid)
                     
    ensures forall td_id :: td_id in DM_TDIDsInGreen(ws')
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k'), ActiveTDsState(k'), td_id)
{
    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');

    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'.subjects, k'.objects);
    assert k'_params.hcoded_td_ids == k_params.hcoded_td_ids;
    assert k'_params.objs_td_ids == k_params.objs_td_ids;
    assert k'_params.objs_fd_ids == k_params.objs_fd_ids;
    assert k'_params.objs_do_ids == k_params.objs_do_ids;

    var k'_tds_state := ActiveTDsState(k');
    forall td_id | td_id in DM_TDIDsInGreen(ws')
        ensures DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, k'_tds_state, td_id)
    {
        assert ObjStateUnchanged_TD(ws.objects, ws'.objects, td_id);
        assert k'_tds_state[td_id] == ActiveTDsState(k)[td_id];

        assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, ActiveTDsState(k), td_id);

        // Prove DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, ActiveTDsState(k'), td_id)
        forall td_id2 | td_id2 in k'_tds_state[td_id].trans_params_tds
            ensures td_id2 in k'_params.objs_td_ids &&
                td_id2 !in k'_params.hcoded_td_ids &&
                (ObjPID_SlimState(k'_params.objs_pids, td_id2.oid) == 
                    ObjPID_SlimState(k'_params.objs_pids, td_id.oid) || 
                        // The TD (<td_id>) contains a transfer, the target TD 
                        // (<td_id2>) must be in the same partition with the TD
                 k'_tds_state[td_id].trans_params_tds[td_id2].amodes == {})
        {
            // Dafny can automatically prove this statement
        }

        forall fd_id2 | fd_id2 in k'_tds_state[td_id].trans_params_fds
            ensures fd_id2 in k'_params.objs_fd_ids &&
                ((ObjPID_SlimState(k'_params.objs_pids, fd_id2.oid) == 
                    ObjPID_SlimState(k'_params.objs_pids, td_id.oid)) ||
                        // The TD (<td_id>) contains a transfer, the target FD 
                        // (<fd_id2>) must be in the same partition with the TD
                 k'_tds_state[td_id].trans_params_fds[fd_id2].amodes == {})
        {
            // Dafny can automatically prove this statement
        }

        forall do_id2 | do_id2 in k'_tds_state[td_id].trans_params_dos
            ensures do_id2 in k'_params.objs_do_ids && 
                (ObjPID_SlimState(k'_params.objs_pids, do_id2.oid) ==
                    ObjPID_SlimState(k'_params.objs_pids, td_id.oid) ||
                        // The TD (<td_id>) contains a transfer, the target DO
                        // (<do_id2>) must be in the same partition with the TD
                 k'_tds_state[td_id].trans_params_dos[do_id2].amodes == {})
        {
            // Dafny can automatically prove this statement
        }

        Lemma_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Prove(k'_params, k'_tds_state, td_id);
        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k'_tds_state, td_id);
    }
}

lemma Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws:DM_State, ws':DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
        // Requirement: Objects have different internal IDs
    requires ws'.red_pid == ws.red_pid
        // Requirement: PID of red partition is unchanged

    requires AllTDIDs(ws'.objects) == AllTDIDs(ws.objects)
    requires forall id :: id in AllTDIDs(ws.objects)
                ==> ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid)

    ensures DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)
{
    // Dafny can automatically prove this lemma
}




//******** Important Util Lemmas ********//
lemma Lemma_NewDM_SameSubjObjIDs(ws:DM_State, ws':DM_State)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_ObjIDs(ws)
    requires P_AllHCodedTDsAreObjs(ws)

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    ensures DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    ensures DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_IsValidState_DevsActivateCond(ws:DM_State, ws':DM_State)
    requires DM_IsValidState_DevsActivateCond(ws)

    requires ws'.devs_activatecond == ws.devs_activatecond
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires (forall dev_id :: dev_id in ws'.devs_activatecond
                ==> DM_SubjPID(ws'.subjects, dev_id.sid) == NULL ||  DM_SubjPID(ws'.subjects, dev_id.sid) == ws'.red_pid)
        // Condition 5.2
    requires (forall dev_id, dev_id2 :: dev_id in ws'.devs_activatecond &&
                    dev_id2 in ws'.devs_activatecond[dev_id]
                ==> DM_SubjPID(ws'.subjects, dev_id2.sid) != ws'.red_pid)
        // Condition 5.3
    requires (forall dev_id :: dev_id in ws'.devs_activatecond &&
                    DM_SubjPID(ws'.subjects, dev_id.sid) != NULL
                ==> (forall dev_id2 :: dev_id2 in ws'.devs_activatecond[dev_id]
                        ==> DM_SubjPID(ws'.subjects, dev_id2.sid) == NULL))
        // Condition 5.6

    ensures DM_IsValidState_DevsActivateCond(ws')
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_SameSubjObjOwnership(ws:DM_State, ws':DM_State)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_ObjIDs(ws)
    requires P_AllHCodedTDsAreObjs(ws)

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')
    
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_ObjIDs(ws')

    ensures DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    ensures forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_DoOwnObj(ws'.subjects, s_id, o_id) == DM_DoOwnObj(ws.subjects, s_id, o_id)
{
    Lemma_NewDM_SameSubjObjIDs(ws, ws');

    forall s_id, o_id | s_id in DM_AllSubjsIDs(ws.subjects)
        ensures DM_DoOwnObj(ws'.subjects, s_id, o_id) == DM_DoOwnObj(ws.subjects, s_id, o_id)
    {
        // Dafny can automatically prove this statement
    }
}

lemma Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws:DM_State, k:State)
    requires DM_IsValidState_Subjects(ws)
    requires k == DMStateToState(ws)

    ensures (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
        // Property: Unique subject IDs
    ensures AllSubjsIDs(k.subjects) == DM_AllSubjsIDs(ws.subjects)
    ensures forall s_id :: DM_IsDevID(ws.subjects, Dev_ID(s_id))
                <==> IsDevID(k, Dev_ID(s_id))
    ensures forall s_id :: DM_IsDrvID(ws.subjects, Drv_ID(s_id))
                <==> IsDrvID(k, Drv_ID(s_id))

    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects)
                ==> DM_SubjPID(ws.subjects, s_id) == SubjPID(k, s_id)
{
    // Dafny can automatically prove this lemma
}

// Lemma: After mapping a valid WK state <ws> to the abstract state <k>,
// DM_ObjPID returns same PID of objects to objects as ObjPID.
lemma Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws:DM_State, k:State)
    requires DM_IsValidState_ObjIDs(ws)
    requires k == DMStateToState(ws)

    ensures forall td_id, fd_id :: TD_ID(td_id) in AllTDIDs(k.objects) && FD_ID(fd_id) in AllFDIDs(k.objects)
                ==> td_id != fd_id
    ensures forall td_id, do_id :: TD_ID(td_id) in AllTDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> td_id != do_id
    ensures forall fd_id, do_id :: FD_ID(fd_id) in AllFDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> fd_id != do_id
        // Properties needed by the ObjPID

    ensures AllObjsIDs(k.objects) == DM_AllObjsIDs(ws.objects)
    ensures forall o_id :: o_id in AllObjsIDs(k.objects)
                ==> o_id in DM_AllObjsIDs(ws.objects)
    ensures forall o_id :: o_id in AllObjsIDs(k.objects)
                ==> DM_ObjPID(ws.objects, o_id) == ObjPID(k, o_id)
{
    reveal IsValidState_Objects_UniqueObjIDs();
}

lemma Lemma_DM_TDIDsInGreen_ProveEqual(ws:DM_State, ws':DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
        // Requirement: Objects have different internal IDs
    requires AllTDIDs(ws.objects) == AllTDIDs(ws'.objects)
    
    requires DM_TDIDsInGreen(ws) <= AllTDIDs(ws.objects)
    requires DM_TDIDsInGreen(ws') <= AllTDIDs(ws'.objects)

    requires ws.red_pid == ws'.red_pid

    requires forall td_id :: td_id in DM_TDIDsInGreen(ws')
                ==> ObjStateUnchanged_TD(ws.objects, ws'.objects, td_id);
    requires forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> ObjStateUnchanged_TD(ws.objects, ws'.objects, td_id);

    ensures DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)
{
    assert DM_TDIDsInGreen(ws') <= DM_TDIDsInGreen(ws);
    assert DM_TDIDsInGreen(ws') >= DM_TDIDsInGreen(ws);
}

// Lemma: If a TD is unchanged between two TDs'states, and fulfills DoTDsIncludeSecureNoTDWriteTransfersOnly in the 1st
// state, then DoTDsIncludeSecureNoTDWriteTransfersOnly must hold in the 2nd state
lemma Lemma_TwoTDStatesUnchangedTD_ProveDoTDsIncludeSecureNoTDWriteTransfersOnly(
    k_params:ReachableTDsKParams, tds_state1:TDs_Vals, tds_state2:TDs_Vals, td_id:TD_ID
)
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
        // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state1) == k_params.all_active_tds
    requires TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state1
    requires td_id in tds_state2
        // Requirement: The TD (<td_id>) is active

    requires DoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, tds_state1, td_id)
    requires tds_state1[td_id] == tds_state2[td_id]

    ensures DoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, tds_state2, td_id)
{
    // Dafny can automatically prove this lemma
}




//******** For EmptyPartitionCreate/Destroy ********//
lemma Lemma_EmptyPartitionCreateDestroy_ProveTDsAreUnmodified(ws:DM_State, ws':DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires ws.objects == ws'.objects
    ensures forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> ObjStateUnchanged_TD(ws.objects, ws'.objects, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_EmptyPartitionDestroy_ProveCheckOfDevActivateInK(
    ws:DM_State, k:State, pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires k == DMStateToState(ws)

    requires (pid != NULL) &&
        (pid in ws.pids) &&
        (forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects) ==> DM_SubjPID(ws.subjects, s_id) != pid) &&
        (forall o_id :: o_id in DM_AllObjsIDs(ws.objects) ==> DM_ObjPID(ws.objects, o_id) != pid)
    
    ensures forall td_id, fd_id :: TD_ID(td_id) in AllTDIDs(k.objects) && FD_ID(fd_id) in AllFDIDs(k.objects)
                ==> td_id != fd_id
    ensures forall td_id, do_id :: TD_ID(td_id) in AllTDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> td_id != do_id
    ensures forall fd_id, do_id :: FD_ID(fd_id) in AllFDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> fd_id != do_id
    ensures (pid != NULL) &&
                (pid in k.pids) &&
                (forall s_id :: s_id in AllSubjsIDs(k.subjects) ==> SubjPID(k, s_id) != pid) &&
                (forall o_id :: o_id in AllObjsIDs(k.objects) ==> ObjPID(k, o_id) != pid)
{
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
}

lemma Lemma_EmptyPartitionDestroy_ProveRedPIDStillExists(
    ws:DM_State, ws':DM_State, pid:Partition_ID
)
    requires pid != ws.red_pid
    requires ws'.red_pid == ws.red_pid
    requires ws'.pids == ws.pids - {pid}
    
    requires ws.red_pid in ws.pids
    
    ensures ws'.red_pid in ws'.pids
{
    // Dafny can automatically prove this lemma
}

//******** For ExternalObjsActivate/Deactivate ********//
lemma Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(
    ws:DM_State, k:State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires DM_IsValidState_Subjects(ws) && DM_IsValidState_Objects(ws)
    requires k == DMStateToState(ws)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
{
    forall s_id, o_id | s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
        ensures !DoOwnObj(k, s_id, o_id)
    {
        assert !DM_DoOwnObj(ws.subjects, s_id, o_id);
    }
}

lemma Lemma_NewDMFromNewK_FulfillSI1_Private(k':State, tds_state2:TDs_Vals)
    requires IsValidState_Subjects(k') && IsValidState_Objects(k')

    requires forall td_id2:TD_ID :: td_id2 in AllActiveTDs_SlimState(k'.objects)
                ==> td_id2.oid in AllObjsIDs(k'.objects) &&
                    ObjPID(k', td_id2.oid) != NULL
    requires TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k'.objects)

    ensures forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> td_id2.oid in AllObjsIDs(k'.objects) &&
                    ObjPID(k', td_id2.oid) != NULL
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_ExternalObjsActivateToGreenPartition_InnerFunc_ProvePreCondition1(
    ws:DM_State, k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)

    requires td_ids <= AllTDIDs(ws.objects)
    requires fd_ids <= AllFDIDs(ws.objects)
    requires do_ids <= AllDOIDs(ws.objects)

    requires (forall td_id :: td_id in td_ids ==> DM_ObjPID(ws.objects, td_id.oid) == NULL) &&
           (forall fd_id :: fd_id in fd_ids ==> DM_ObjPID(ws.objects, fd_id.oid) == NULL) &&
           (forall do_id :: do_id in do_ids ==> DM_ObjPID(ws.objects, do_id.oid) == NULL)

    requires AllObjsIDs(k.objects) == DM_AllObjsIDs(ws.objects)
    requires forall o_id :: o_id in AllObjsIDs(k.objects)
                ==> DM_ObjPID(ws.objects, o_id) == ObjPID(k, o_id)

    ensures (forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) == NULL) &&
            (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) == NULL) &&
            (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) == NULL)
{
    // Dafny can automatically prove this lemma
}