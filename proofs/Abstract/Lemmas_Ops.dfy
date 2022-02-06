include "Syntax.dfy"
include "Properties.dfy"
include "Properties_Corollaries.dfy"
include "Utils.dfy"
include "CASOps.dfy"
include "Lemmas.dfy"

//******** Lemmas for All Operations  ********//
lemma Lemma_ValidK_HCodedTDsAreTDs(k:State)
    requires IsValidState(k)
    ensures forall dev_id :: dev_id in k.subjects.devs
        ==> k.subjects.devs[dev_id].hcoded_td_id in AllTDIDs(k.objects)
{
    // Dafny can automatically prove this lemma
}

// Note: Needs 300s to verify
lemma Lemma_ValidState_FulfillCanActiveDevReadActiveTDPreConditions(k:State)
    requires IsValidState(k)
    ensures forall td_id2, dev_id, tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    dev_id in AllActiveDevs(k) && 
                    td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> CanActiveDevReadActiveTD_PreConditions(KToKParams(k), tds_state2, dev_id, td_id2)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k:State, k_params:ReachableTDsKParams)
    requires IsValidState(k) && IsSecureState(k)
    
    requires k_params == KToKParams(k) 

    ensures forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k:State, k_params:ReachableTDsKParams)
    requires IsValidState(k) && IsSecureState(k)
    
    requires k_params == KToKParams(k)  

    ensures FindAllTDsReadByDev_KParams_PreConditions(k_params)
{
    var k_params := KToKParams(k);

    assert (forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
        ==> SubjPID(k, s_id) == ObjPID(k, o_id));

    assert k.subjects == k_params.subjects;
    forall s_id, o_id | s_id in AllSubjsIDs(k_params.subjects) &&
                    DoOwnObj_SlimState(k_params.subjects, s_id, o_id)
        ensures o_id in k_params.objs_pids
        ensures k_params.objs_pids[o_id] == SubjPID_SlimState(k_params.subjects, s_id)
    {
        assert s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id);
        assert SubjPID(k, s_id) == ObjPID(k, o_id);
    }
}

// Lemma: Hardcoded TDs are unmodified between states
lemma Lemma_NewStateVars_HCodedTDsAreUnmodified(k:State, k'_subjects:Subjects, k'_objects:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are in devices
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)
        // Requirement: Hardcoded TDs IDs and immutable values are stored in <k.objects.hcoded_tds>

    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids
        // Requirement: The IDs of TDs owned by a device is not changed

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'_objects.hcoded_tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val)

    ensures AllHCodedTDIDs(k'_subjects) == AllHCodedTDIDs(k.subjects)
    ensures BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects) == BuildMap_DevsToHCodedTDVals(k.subjects, k.objects)
    ensures MapGetKeys(BuildMap_ObjIDsToPIDs(k'_objects)) == MapGetKeys(BuildMap_ObjIDsToPIDs(k.objects))
{
    Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);
}

lemma Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(k:State, k'_active_tds:set<TD_ID>)
    requires IsValidState(k)
    requires k'_active_tds <= AllTDIDs(k.objects)

    ensures k'_active_tds in k.tds_to_all_states
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewK_FulfillIsValidStateObjects(k:State, k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)

    requires MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'.objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'.objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'.objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'.objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires forall drv_id :: drv_id in k.subjects.drvs
                ==> (k'.subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'.subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'.subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id)

    requires AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects)
    requires BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects) == BuildMap_DevsToHCodedTDVals(k.subjects, k.objects)
    requires k'.tds_to_all_states == k.tds_to_all_states

    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k'.objects)

    requires IsValidState_Objects(k)

    ensures IsValidState_Objects(k')
{
    assert forall dev_id :: dev_id in k'.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids);
    Lemma_SameObjsOwnershipInSuccessiveStates(k, k');

    Lemma_NewK_FulfillCondition28(k, k');

    Lemma_NewK_FulfillCondition27(k, k');
}

lemma Lemma_IsValidState_SubjectsObjects_Properties(k:State, k_params:ReachableTDsKParams)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires k_params == KToKParams(k)

    ensures TDsStateGetTDIDs(ActiveTDsState(k)) == AllActiveTDs(k)
    ensures forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    
    ensures forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= AllTDIDs(k.objects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewKParams_FindAllTDsReadByDev_KParams_PreConditions_StillHold(k_params:ReachableTDsKParams, k'_params:ReachableTDsKParams)
    //requires k'_params.subjects == k_params.subjects
    requires MapGetKeys<Drv_ID, Drv_State>(k'_params.subjects.drvs) == MapGetKeys<Drv_ID, Drv_State>(k_params.subjects.drvs)
    requires MapGetKeys<Dev_ID, Dev_State>(k'_params.subjects.devs) == MapGetKeys<Dev_ID, Dev_State>(k_params.subjects.devs)
    requires forall drv_id :: drv_id in k_params.subjects.drvs
                ==> (k'_params.subjects.drvs[drv_id].td_ids == k_params.subjects.drvs[drv_id].td_ids) &&
                    (k'_params.subjects.drvs[drv_id].fd_ids == k_params.subjects.drvs[drv_id].fd_ids) &&
                    (k'_params.subjects.drvs[drv_id].do_ids == k_params.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k_params.subjects.devs
                ==> (k'_params.subjects.devs[dev_id].td_ids == k_params.subjects.devs[dev_id].td_ids) &&
                    (k'_params.subjects.devs[dev_id].fd_ids == k_params.subjects.devs[dev_id].fd_ids) &&
                    (k'_params.subjects.devs[dev_id].do_ids == k_params.subjects.devs[dev_id].do_ids)
    requires forall dev_id :: dev_id in k_params.subjects.devs
                ==> k'_params.subjects.devs[dev_id].hcoded_td_id == k_params.subjects.devs[dev_id].hcoded_td_id

    requires k'_params.objs_td_ids == k_params.objs_td_ids
    requires k'_params.objs_fd_ids == k_params.objs_fd_ids
    requires k'_params.objs_do_ids == k_params.objs_do_ids
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds
    requires MapGetKeys(k'_params.objs_pids) == MapGetKeys(k_params.objs_pids)

    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    requires forall td_id2 :: td_id2 in k'_params.all_active_tds
                <==> td_id2 in k'_params.objs_td_ids &&
                    ObjPID_SlimState(k'_params.objs_pids, td_id2.oid) != NULL
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
                ==> o_id in k'_params.objs_pids &&
                    k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)

    ensures FindAllTDsReadByDev_KParams_PreConditions(k'_params)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewKParams_SameSubjIDsOwnershipInSuccessiveStates(
    k:State, k'_subjects:Subjects, k_params:ReachableTDsKParams, k'_params:ReachableTDsKParams
)
    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires (forall drv_id :: drv_id in k'_subjects.drvs
            ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
            (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
            (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids))
    requires (forall dev_id :: dev_id in k'_subjects.devs
            ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
            (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
            (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
            (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids))

    requires k_params.subjects == k.subjects
    requires k'_params.subjects == k'_subjects

    ensures MapGetKeys<Drv_ID, Drv_State>(k'_params.subjects.drvs) == MapGetKeys<Drv_ID, Drv_State>(k_params.subjects.drvs)
    ensures MapGetKeys<Dev_ID, Dev_State>(k'_params.subjects.devs) == MapGetKeys<Dev_ID, Dev_State>(k_params.subjects.devs)
    ensures forall drv_id :: drv_id in k_params.subjects.drvs
                ==> (k'_params.subjects.drvs[drv_id].td_ids == k_params.subjects.drvs[drv_id].td_ids) &&
                    (k'_params.subjects.drvs[drv_id].fd_ids == k_params.subjects.drvs[drv_id].fd_ids) &&
                    (k'_params.subjects.drvs[drv_id].do_ids == k_params.subjects.drvs[drv_id].do_ids)
    ensures forall dev_id :: dev_id in k_params.subjects.devs
                ==> (k'_params.subjects.devs[dev_id].td_ids == k_params.subjects.devs[dev_id].td_ids) &&
                    (k'_params.subjects.devs[dev_id].fd_ids == k_params.subjects.devs[dev_id].fd_ids) &&
                    (k'_params.subjects.devs[dev_id].do_ids == k_params.subjects.devs[dev_id].do_ids)
    ensures forall dev_id :: dev_id in k_params.subjects.devs
                ==> k'_params.subjects.devs[dev_id].hcoded_td_id == k_params.subjects.devs[dev_id].hcoded_td_id
{
    assert forall drv_id :: drv_id in k_params.subjects.drvs
                ==> (k'_params.subjects.drvs[drv_id].td_ids == k_params.subjects.drvs[drv_id].td_ids) &&
                    (k'_params.subjects.drvs[drv_id].fd_ids == k_params.subjects.drvs[drv_id].fd_ids) &&
                    (k'_params.subjects.drvs[drv_id].do_ids == k_params.subjects.drvs[drv_id].do_ids);
}

// Lemma:  In the current active TDs' state of k, any active TDs read by any 
// active devices have no invalid references to I/O objects
// (needs 50s to verify)
lemma Lemma_CurrentActiveTDsStateOnlyHasValidRefs(k:State, k_reachable_active_tds_states:set<TDs_Vals>)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
        // Requirement: Subjects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)

    requires forall tds_state2 :: tds_state2 in k_reachable_active_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
        // Requirement: k fulfills Condition 5.1 of <IsValidState_ReachableTDsStates>
    requires forall tds_state2 :: tds_state2 in k_reachable_active_tds_states
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2))
        // Requirement: k fulfills Condition 5.5 of <IsValidState_HelperStateVariables>
    requires ActiveTDsState(k) in k_reachable_active_tds_states
        // Requirement: k fulfills Condition 5.6 of <IsValidState_HelperStateVariables>

    ensures forall td_id2, dev_id :: 
            dev_id in AllActiveDevs(k) && 
                // The device (<dev_id>) is active
            td_id2 in AllActiveTDs(k) &&
                // The TD (<td_id2>) is active
            CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id2)
                // The TD is read by the device
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), ActiveTDsState(k), td_id2)
        // Property: In the current active TDs' state of k, any active TDs read 
        // by any active devices have no invalid references to I/O objects
{
    // Dafny can automatically prove this lemma
}

// Lemma: If tds_states, status == FindReachableActiveTDsStatesFromActiveTDsState(k'.objects.tds), 
// and status == true, then AllReachableActiveTDsStates(k') == tds_states
lemma Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
    k:State, tds_states:set<TDs_Vals>
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
    requires forall tds_state2 :: tds_state2 in tds_states
                ==> (ActiveTDsState(k) == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k), AllActiveDevs(k), ActiveTDsState(k), tds_state2))
    requires forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                        (tds_state2 == ActiveTDsState(k) || 
                            IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k), AllActiveDevs(k), ActiveTDsState(k), tds_state2))
                                                    // tds_state -->* tds_state2
                    ==> tds_state2 in tds_states

    ensures AllReachableActiveTDsStates(k) == tds_states
{
    // Dafny can automatically prove this lemma
}

// Lemma: If tds_states, status == FindReachableActiveTDsStatesFromActiveTDsState(k'.objects.tds), 
// and status == true, and if k' fulfills IsValidState_Objects and IsValidState_SubjsOwnObjsThenInSamePartition, then 
// IsValidState_ReachableTDsStates(k')
lemma Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
    k':State, k'_params:ReachableTDsKParams, tds_states:set<TDs_Vals>, status:bool
)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k'_params)
    // Requirements required by functions in this function method
    
    requires TDsStateGetTDIDs(ActiveTDsState(k')) == k'_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k'_params.all_active_tds
        // Requirement: <tds_states> must includes all active TDs
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k')
                ==> IsDevID_SlimState(k'_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k'_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k')
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in tds_states
                ==> (ActiveTDsState(k') == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params,
                                                        AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
        // Requirement: Forall tds_state2 in tds_states, ActiveTDsState(k') -->* tds_state2
    requires (status == true)
                ==> (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k') &&
                        (tds_state2 == ActiveTDsState(k') || 
                            IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                                AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
                                                    // ActiveTDsState(k') -->* tds_state2
                    ==> tds_state2 in tds_states)
        // Requirement: Forall tds_state2, ActiveTDsState(k') -->* tds_state2 ==> tds_state2 in tds_states
    requires status <==> AllReachableActiveTDsStatesAreSecure(k'_params, AllActiveDevs(k'), tds_states)
        // Requirement: Any active TDs read by any active devices have no invalid
        // references to I/O objects

    requires forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k'.subjects.drvs) && (Dev_ID(dev_sid) in k'.subjects.devs)
                 ==> (drv_sid != dev_sid)
    requires IsValidState_Objects(k')
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k')
    requires k'_params == KToKParams(k')

    requires status == true
    requires AllReachableActiveTDsStates(k') == tds_states

    ensures IsValidState_ReachableTDsStates(k')
    ensures IsSecureState_SI1(k')
    ensures StatePropertiesCorollary1(k')
{
    var k'_reachable_active_tds_states := AllReachableActiveTDsStates(k');

    Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateOfReachableTDsStates(k', k'_params, tds_states, k'_reachable_active_tds_states, status);
    Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant_More(k');

    Lemma_IfFulfillCondition55AndIsValidState_SubjsOwnObjsThenInSamePartition_ThenFulfillCorollary1(k', k'_params, k'_reachable_active_tds_states);
}

lemma Lemma_AllActiveDevs_ReturnCorrectResult(k:State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
        
    requires K_UniqueIDsAndOwnedObjs(k.subjects, AllTDIDs(k.objects), AllFDIDs(k.objects), AllDOIDs(k.objects))
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds

    ensures forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> IsDevID_SlimState(KToKParams(k).subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(KToKParams(k).subjects, dev_id2) != NULL
{
    assert IsValidState_Objects_UniqueObjIDs(k.objects);
    reveal IsValidState_Objects_UniqueObjIDs();

    assert KToKParams(k).subjects == k.subjects;

    forall dev_id2 | dev_id2 in AllActiveDevs(k)
        ensures IsDevID_SlimState(KToKParams(k).subjects, dev_id2)
        ensures SubjPID_DevID_SlimState(KToKParams(k).subjects, dev_id2) != NULL
    {
        assert IsDevID_SlimState(k.subjects, dev_id2);
    }
}

lemma Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)

    ensures K_UniqueIDsAndOwnedObjs(k.subjects, AllTDIDs(k.objects), AllFDIDs(k.objects), AllDOIDs(k.objects))
{
    // Dafny can automatically prove this lemma
}

// (needs 200s to verify)
lemma Lemma_AllReachableActiveTDsStates_ActiveTDsStateIsSecure_Property(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
     
    requires forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2))

    ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), tds_state2, td_id2))

    ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToObjOutsidePartition(KToKParams(k), tds_state2, td_id2))
{
    var k_params := KToKParams(k);

    forall tds_state2 | tds_state2 in AllReachableActiveTDsStates(k)
        ensures (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, tds_state2, td_id2))
        ensures (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToObjOutsidePartition(k_params, tds_state2, td_id2))
    {
        forall td_id2, dev_id | dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
            ensures !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, tds_state2, td_id2)
            ensures !DoActiveTDIncludeTransfersToObjOutsidePartition(k_params, tds_state2, td_id2)
        {
            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2);
        }
    }
}

lemma Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k:State)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    ensures P_ObjsInSubjsAreAlsoInState(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_AllReachableActiveTDsStates_PreConditions(k:State)
    requires IsValidState(k)

    ensures forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)
{
    // Dafny can automatically prove this lemma
}




//******** Lemmas for Specific Operations  ********//
// Lemma: In DevWrite, KToKParams(k) == KToKParams(k')
lemma Lemma_DrvDevWrite_NewKParams_SameWithKParams(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are in devices
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)
        // Requirement: Hardcoded TDs IDs and immutable values are stored in <k.objects.hcoded_tds>
    
    requires k'_subjects == k.subjects
    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires forall td_id :: td_id in AllTDIDs(k.objects)
                ==> ObjPID_KObjects(k'_objects, td_id.oid) == ObjPID_KObjects(k.objects, td_id.oid)
    requires forall fd_id :: fd_id in AllFDIDs(k.objects)
                ==> ObjPID_KObjects(k'_objects, fd_id.oid) == ObjPID_KObjects(k.objects, fd_id.oid)
    requires forall do_id :: do_id in AllDOIDs(k.objects)
                ==> ObjPID_KObjects(k'_objects, do_id.oid) == ObjPID_KObjects(k.objects, do_id.oid)
        // Requirement: Unchanged IDs and PIDs between k and k'
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids
        // Requirement: The IDs of TDs owned by a device is not changed
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'_objects.hcoded_tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val)

    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))
 
    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_subjects.devs[dev_id].td_ids
    ensures KToKParams(k) == k'_params
{
    assert AllTDIDs(k'_objects) == AllTDIDs(k.objects);
    assert AllFDIDs(k'_objects) == AllFDIDs(k.objects);
    assert AllDOIDs(k'_objects) == AllDOIDs(k.objects);

    assert forall dev_id :: dev_id in k.subjects.devs
                ==> k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids;
        // Requirement: The IDs of TDs owned by a device is not changed
    assert forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'_objects.hcoded_tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val);

    var k_params := KToKParams(k);

    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'_subjects, k'_objects);
    assert k'_params.hcoded_td_ids == k_params.hcoded_td_ids;
    assert k'_params.hcoded_tds == k_params.hcoded_tds;

    assert k'_params.objs_pids == k_params.objs_pids;

    assert k'_params.all_active_tds == k_params.all_active_tds;
}

lemma Lemma_DevWrite_ReachableActiveTDsStatesFromNewKActiveTDsStatesMustBeSecure(
    k:State, k_params:ReachableTDsKParams, k'_active_tds_state:TDs_Vals
)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
    requires k_params == KToKParams(k)

    requires TDsStateGetTDIDs(k'_active_tds_state) == k_params.all_active_tds

    requires (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
    requires forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (k'_active_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2))
                                                // k'_active_tds_state -->* tds_state2
                ==> IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        AllActiveDevs(k), ActiveTDsState(k), tds_state2)
                                                // ActiveTDsState(k) -->1+ tds_state2
        // Requirement: If k'_active_tds_state -->* tds_state2, then 
        // ActiveTDsState(k) -->1+ tds_state2

    ensures forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (k'_active_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2))
                ==> (forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2))
{
    forall tds_state2 | TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (k'_active_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2))
        ensures (forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2))
    {
        assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        AllActiveDevs(k), ActiveTDsState(k), tds_state2);
        assert tds_state2 in AllReachableActiveTDsStates(k);
    }
}

// (needs 360s to verify)
lemma Lemma_DevWrite_WrittenTDsFDsDOsExistInSystem(
    k:State, dev_id:Dev_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>,
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
        // Requirement: Subjects have different internal IDs
    requires IsValidState_Objects(k)
    
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= AllTDIDs(k.objects)

    requires forall td_id2 :: td_id2 in td_id_val_map
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD in the system 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    td_id2 in GetTDVal(k, td_id).trans_params_tds &&
                    W in GetTDVal(k, td_id).trans_params_tds[td_id2].amodes &&
                        // The TD references the target TD (<td_id2>) with W
                    td_id_val_map[td_id2] in GetTDVal(k, td_id).trans_params_tds[td_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each TD writes in <td_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD in the system 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    fd_id2 in GetTDVal(k, td_id).trans_params_fds &&
                    W in GetTDVal(k, td_id).trans_params_fds[fd_id2].amodes && 
                        // The TD references the target FD (<fd_id2>) with W
                    fd_id_val_map[fd_id2] in GetTDVal(k, td_id).trans_params_fds[fd_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each FD writes in <fd_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)
    requires forall do_id2 :: do_id2 in do_id_val_map
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD in the system 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    do_id2 in GetTDVal(k, td_id).trans_params_dos &&
                    W in GetTDVal(k, td_id).trans_params_dos[do_id2].amodes &&
                        // The TD references the target DO (<do_id2>) with W 
                    do_id_val_map[do_id2] in GetTDVal(k, td_id).trans_params_dos[do_id2].vals) 
                        // The TD specifies the new value to be written
        // Requirement: For each DO writes in <do_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)
    requires forall td_id2, dev_id2 :: 
            dev_id2 in AllActiveDevs(k) && 
                // The device (<dev_id2>) is active
            td_id2 in AllActiveTDs(k) &&
                // The TD (<td_id2>) is active
            CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id2, td_id2)
                // The TD is read by the device
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), ActiveTDsState(k), td_id2)
        // Requirement: In the current TDs' state of k, any active TDs read by any
        // active devices have no invalid references to I/O objects
    requires StatePropertiesCorollary2(k)

    ensures forall td_id :: td_id in td_id_val_map 
            ==> td_id in AllTDIDs(k.objects) &&
                td_id !in KToKParams(k).hcoded_td_ids &&
                ObjPID(k, td_id.oid) == SubjPID_DevID(k, dev_id)
    ensures forall fd_id :: fd_id in fd_id_val_map 
            ==> fd_id in AllFDIDs(k.objects) &&
                ObjPID(k, fd_id.oid) == SubjPID_DevID(k, dev_id)
    ensures forall do_id :: do_id in do_id_val_map 
            ==> do_id in AllDOIDs(k.objects) &&
                ObjPID(k, do_id.oid) == SubjPID_DevID(k, dev_id)
    ensures forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                    FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                    DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
            ==> {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, o_id)
{
    var k_params := KToKParams(k);

    forall td_id2 | td_id2 in td_id_val_map
        ensures td_id2 in AllTDIDs(k.objects) && ObjPID(k, td_id2.oid) == SubjPID_DevID(k, dev_id)
        ensures td_id2 !in k_params.hcoded_td_ids
        ensures {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, td_id2.oid)
    {
        assert exists td_id :: td_id in AllTDIDs(k.objects) &&
                ObjPID(k, td_id.oid) != NULL &&
                    // Exists an active TD in the system 
                CanActiveDevReadActiveTD(k_params, ActiveTDsState(k), dev_id, td_id) &&
                    // The device can read the active TD
                td_id2 in GetTDVal(k, td_id).trans_params_tds &&
                W in GetTDVal(k, td_id).trans_params_tds[td_id2].amodes &&
                    // The TD references the target TD (<td_id2>) with W
                td_id_val_map[td_id2] in GetTDVal(k, td_id).trans_params_tds[td_id2].vals;
        assert DevAModesToObjFromTDs_ExistW_SlimState(k_params, ActiveTDsState(k), dev_id, td_id2.oid);
        assert {W} <= DevAModesToObjFromTDs_SlimState(k_params, ActiveTDsState(k), dev_id, td_id2.oid);
        assert {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, td_id2.oid);

        assert td_id2.oid in AllObjsIDs(k.objects);
        assert SubjPID_DevID(k, dev_id) == ObjPID(k, td_id2.oid);
    }

    forall fd_id2 | fd_id2 in fd_id_val_map
        ensures fd_id2 in AllFDIDs(k.objects) && ObjPID(k, fd_id2.oid) == SubjPID_DevID(k, dev_id)
        ensures {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, fd_id2.oid)
    {
        assert exists td_id :: td_id in AllTDIDs(k.objects) &&
                ObjPID(k, td_id.oid) != NULL &&
                    // Exists an active TD in the system 
                CanActiveDevReadActiveTD(k_params, ActiveTDsState(k), dev_id, td_id) &&
                    // The device can read the active TD
                fd_id2 in GetTDVal(k, td_id).trans_params_fds &&
                W in GetTDVal(k, td_id).trans_params_fds[fd_id2].amodes && 
                    // The TD references the target FD (<fd_id2>) with W
                fd_id_val_map[fd_id2] in GetTDVal(k, td_id).trans_params_fds[fd_id2].vals;
        assert DevAModesToObjFromTDs_ExistW_SlimState(k_params, ActiveTDsState(k), dev_id, fd_id2.oid);
        assert {W} <= DevAModesToObjFromTDs_SlimState(k_params, ActiveTDsState(k), dev_id, fd_id2.oid);
        assert {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, fd_id2.oid);

        assert fd_id2.oid in AllObjsIDs(k.objects);
        assert SubjPID_DevID(k, dev_id) == ObjPID(k, fd_id2.oid);
    }

    forall do_id2 | do_id2 in do_id_val_map
        ensures do_id2 in AllDOIDs(k.objects) && ObjPID(k, do_id2.oid) == SubjPID_DevID(k, dev_id)
        ensures {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, do_id2.oid)
    {
        assert exists td_id :: td_id in AllTDIDs(k.objects) &&
                ObjPID(k, td_id.oid) != NULL &&
                    // Exists an active TD in the system 
                CanActiveDevReadActiveTD(k_params, ActiveTDsState(k), dev_id, td_id) &&
                    // The device can read the active TD
                do_id2 in GetTDVal(k, td_id).trans_params_dos &&
                W in GetTDVal(k, td_id).trans_params_dos[do_id2].amodes &&
                    // The TD references the target DO (<do_id2>) with W 
                do_id_val_map[do_id2] in GetTDVal(k, td_id).trans_params_dos[do_id2].vals;
        assert DevAModesToObjFromTDs_ExistW_SlimState(k_params, ActiveTDsState(k), dev_id, do_id2.oid);
        assert {W} <= DevAModesToObjFromTDs_SlimState(k_params, ActiveTDsState(k), dev_id, do_id2.oid);
        assert {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, do_id2.oid);

        assert do_id2.oid in AllObjsIDs(k.objects);
        assert SubjPID_DevID(k, dev_id) == ObjPID(k, do_id2.oid);
    }
}

lemma Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed(
    k:State, dev_sid:Subject_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>,
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires IDToDev(k, Dev_ID(dev_sid)).pid != NULL
        // Requirement: The driver is in the I/O system and is active
    requires forall td_id2 :: td_id2 in td_id_val_map
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    td_id2 in GetTDVal(k, td_id).trans_params_tds &&
                    W in GetTDVal(k, td_id).trans_params_tds[td_id2].amodes &&
                        // The TD references the target TD (<td_id2>) with W
                    td_id_val_map[td_id2] in GetTDVal(k, td_id).trans_params_tds[td_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each TD writes in <td_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<Dev_ID(dev_sid)>)
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    fd_id2 in GetTDVal(k, td_id).trans_params_fds &&
                    W in GetTDVal(k, td_id).trans_params_fds[fd_id2].amodes && 
                        // The TD references the target FD (<fd_id2>) with W
                    fd_id_val_map[fd_id2] in GetTDVal(k, td_id).trans_params_fds[fd_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each FD writes in <fd_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<Dev_ID(dev_sid)>)
    requires forall do_id2 :: do_id2 in do_id_val_map
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    do_id2 in GetTDVal(k, td_id).trans_params_dos &&
                    W in GetTDVal(k, td_id).trans_params_dos[do_id2].amodes &&
                        // The TD references the target DO (<do_id2>) with W 
                    do_id_val_map[do_id2] in GetTDVal(k, td_id).trans_params_dos[do_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each DO writes in <do_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<Dev_ID(dev_sid)>)

    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(k.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(k.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(k.objects))
        // Property 1: Written TDs, FDs and DOs are in the I/O system
    ensures forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                    FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                    DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
                ==> o_id in AllObjsIDs(k.objects) &&
                    ObjPID(k, o_id) == SubjPID(k, dev_sid)
        // Property 2: All written objects are in the same partition with the device
    ensures forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Property 3: device does not write any hardcoded TDs
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.active_non_hcoded_tds) &&
            (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.active_fds) &&
            (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.active_dos)
        // Property 4: Written TDs, FDs and DOs are in the I/O system
{
    var obj_id_list := TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map));
    Lemma_ActiveDevsHaveHcodedPtrsToOwnedObjs(k);
    
    // Prove StatePropertiesCorollary2(k)
    Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
    Lemma_StatePropertyCorollary1_ImpliesCorollary2(k);
    assert StatePropertiesCorollary2(k);

    Lemma_CurrentActiveTDsStateOnlyHasValidRefs(k, AllReachableActiveTDsStates(k));
    Lemma_DevWrite_WrittenTDsFDsDOsExistInSystem(
        k, Dev_ID(dev_sid), td_id_val_map, fd_id_val_map, do_id_val_map);
    assert forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(k.objects);
    assert forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(k.objects);
    assert forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(k.objects);

    Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed_Property2(
        k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    assert forall dev_id :: dev_id in k.subjects.devs
            ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map;

    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
}

lemma Lemma_DevDeactivate_ProveTDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues_InNewK(
    k:State, dev_id:Dev_ID
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.active_dos)

    requires var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
            var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
            var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
            todeactive_hcoded_td_id in t_objs3.hcoded_tds

    ensures var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
            var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
            var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
            var k'_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);
            var dev_state := IDToDev(k, dev_id);
            var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
            var new_devs := k.subjects.devs[dev_id := new_dev_state];
            var k'_subjects := Subjects(k.subjects.drvs, new_devs);
            var k'_objs_td_ids := AllTDIDs(k'_objects);
            var k'_objs_fd_ids := AllFDIDs(k'_objects);
            var k'_objs_do_ids := AllDOIDs(k'_objects);
            var k'_active_tds := AllActiveTDs_SlimState(k'_objects);
            var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);
            var k'_active_tds_state := ActiveTDsState_SlimState(k'_objects);
            TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
    var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
    var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
    var k'_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);
    var dev_state := IDToDev(k, dev_id);
    var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
    var new_devs := k.subjects.devs[dev_id := new_dev_state];
    var k'_subjects := Subjects(k.subjects.drvs, new_devs);
    var k'_objs_td_ids := AllTDIDs(k'_objects);
    var k'_objs_fd_ids := AllFDIDs(k'_objects);
    var k'_objs_do_ids := AllDOIDs(k'_objects);
    var k'_active_tds := AllActiveTDs_SlimState(k'_objects);
    var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);
    var k'_active_tds_state := ActiveTDsState_SlimState(k'_objects);

    forall dev_id | IsDevID_SlimState(k'_params.subjects, dev_id) &&
                     k'_params.subjects.devs[dev_id].hcoded_td_id in k'_active_tds_state
        ensures k'_active_tds_state[k'_params.subjects.devs[dev_id].hcoded_td_id] == k'_params.hcoded_tds[dev_id]
    {
        // Dafny can automatically prove it
    }
}

lemma Lemma_DrvDevWrite_ProveTargetTDsAreActive(k:State, td_id_val_map:map<TD_ID, TD_Val>)
    requires IsValidState(k)

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.active_non_hcoded_tds)

    ensures forall o_id :: o_id in TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map))
                        // Forall o_id that is an internal ID of any TD/FD/DO in *_id_val_map
                ==> o_id in AllObjsIDs(k.objects) &&
                    ObjPID(k, o_id) != NULL
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    // Dafny can automatically prove this lemma.
}

lemma Lemma_DrvDevWrite_WrittenTDsMustBeActiveInK(k:State, td_id_val_map:map<TD_ID, TD_Val>)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs

    requires forall o_id :: o_id in TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map))
                        // Forall o_id that is an internal ID of any TD/FD/DO in *_id_val_map
                ==> o_id in AllObjsIDs(k.objects) &&
                    ObjPID(k, o_id) != NULL
    requires forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(k.objects)

    ensures forall td_id:: td_id in td_id_val_map ==> td_id in ActiveTDsState(k)
{
    forall td_id | td_id in td_id_val_map
        ensures td_id in ActiveTDsState(k)
    {
        assert td_id.oid in AllObjsIDs(k.objects);
        assert ObjPID(k, td_id.oid) != NULL;
    }
}

lemma Lemma_DrvDevWrite_CorrectlyUpdateTDsState(k:State, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.active_non_hcoded_tds) &&
            (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.active_fds) &&
            (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.active_dos)

    ensures var t_objs1 := WriteActiveNonHCodedTDsVals(k.objects, td_id_val_map);
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
            var k_active_tds_state := ActiveTDsState(k);
            var k'_active_tds_state := ActiveTDsState_SlimState(t_objs3);
            forall td_id :: td_id in k_active_tds_state
                ==> (td_id in td_id_val_map ==> k'_active_tds_state[td_id] == td_id_val_map[td_id]) &&
                    (td_id !in td_id_val_map ==> k'_active_tds_state[td_id] == k_active_tds_state[td_id])
{
    var t_objs1 := WriteActiveNonHCodedTDsVals(k.objects, td_id_val_map);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
    var k_active_tds_state := ActiveTDsState(k);
    var k'_active_tds_state := ActiveTDsState_SlimState(t_objs3);

    forall td_id | td_id in k_active_tds_state
        ensures (td_id in td_id_val_map ==> k'_active_tds_state[td_id] == td_id_val_map[td_id])
        ensures (td_id !in td_id_val_map ==> k'_active_tds_state[td_id] == k_active_tds_state[td_id])
    {
        // Dafny can automatically prove it
    }
}

// Lemma: After DrvWrite/DevWrite, the PIDs of objects are unchanged
lemma Lemma_DrvDevWrite_PreserveObjPIDs(
    k_objs:Objects, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires IsValidState_Objects_UniqueObjIDs(k_objs)
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k_objs.active_non_hcoded_tds) &&
            (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k_objs.active_fds) &&
            (forall do_id :: do_id in do_id_val_map ==> do_id in k_objs.active_dos)

    ensures var t_objs1 := WriteActiveNonHCodedTDsVals(k_objs, td_id_val_map);
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            var k'_objs := WriteActiveDOsVals(t_objs2, do_id_val_map);
            IsValidState_Objects_UniqueObjIDs(k'_objs) &&
            AllObjsIDs(k_objs) == AllObjsIDs(k'_objs) &&
            (forall id :: id in AllTDIDs(k'_objs)
                ==> ObjPID_KObjects(k'_objs, id.oid) == ObjPID_KObjects(k_objs, id.oid)) &&
            (forall id :: id in AllFDIDs(k'_objs)
                ==> ObjPID_KObjects(k'_objs, id.oid) == ObjPID_KObjects(k_objs, id.oid)) &&
            (forall id :: id in AllDOIDs(k'_objs)
                ==> ObjPID_KObjects(k'_objs, id.oid) == ObjPID_KObjects(k_objs, id.oid)) &&
            (forall id :: id in AllObjsIDs(k'_objs)
                ==> ObjPID_KObjects(k'_objs, id) == ObjPID_KObjects(k_objs, id))
{
    var t_objs1 := WriteActiveNonHCodedTDsVals(k_objs, td_id_val_map);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var k'_objs := WriteActiveDOsVals(t_objs2, do_id_val_map);
    
    reveal IsValidState_Objects_UniqueObjIDs();

    assert (forall id :: id in AllTDIDs(t_objs1)
                ==> ObjPID_KObjects(t_objs1, id.oid) == ObjPID_KObjects(k_objs, id.oid)) &&
            (forall id :: id in AllFDIDs(t_objs1)
                ==> ObjPID_KObjects(t_objs1, id.oid) == ObjPID_KObjects(k_objs, id.oid)) &&
            (forall id :: id in AllDOIDs(t_objs1)
                ==> ObjPID_KObjects(t_objs1, id.oid) == ObjPID_KObjects(k_objs, id.oid));

    forall id | id in AllTDIDs(k'_objs)
        ensures ObjPID_KObjects(k'_objs, id.oid) == ObjPID_KObjects(k_objs, id.oid)
    {
        // Dafny can automatically prove it
    }
}

lemma Lemma_DrvDevWrite_ProveActiveObjsMustHaveNonNULLPID(
    k_objs:Objects, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>, k'_objs:Objects
)
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k_objs)
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k_objs.active_non_hcoded_tds) &&
            (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k_objs.active_fds) &&
            (forall do_id :: do_id in do_id_val_map ==> do_id in k_objs.active_dos)

    requires var t_objs1 := WriteActiveNonHCodedTDsVals(k_objs, td_id_val_map);
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
            k'_objs == t_objs3

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k'_objs)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    // Dafny can automatically prove this lemma.
}

lemma Lemma_DrvActivate_ProveActiveObjsMustHaveNonNULLPID(
    k:State, drv_id:Drv_ID, pid:Partition_ID
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k.objects)

    requires drv_id in k.subjects.drvs
    requires (forall id :: id in k.subjects.drvs[drv_id].td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in k.subjects.drvs[drv_id].fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in k.subjects.drvs[drv_id].do_ids ==> id in k.objects.inactive_dos)
    requires pid != NULL

    ensures var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
            var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
            var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, tds_owned_by_drv, pid);
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_drv, pid);
            var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_drv, pid);
            IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(new_objects)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, tds_owned_by_drv, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_drv, pid);
    var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_drv, pid);

    assert forall id :: id in new_objects.active_non_hcoded_tds
        ==> new_objects.active_non_hcoded_tds[id].pid != NULL;
}

lemma Lemma_DrvDeactivate_ProveActiveObjsMustHaveNonNULLPID(
    k:State, drv_id:Drv_ID
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k.objects)

    requires drv_id in k.subjects.drvs
    requires (forall id :: id in k.subjects.drvs[drv_id].td_ids ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in k.subjects.drvs[drv_id].fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in k.subjects.drvs[drv_id].do_ids ==> id in k.objects.active_dos)

    ensures var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
            var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
            var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, tds_owned_by_drv);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_drv);
            var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_drv);
            IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(new_objects)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, tds_owned_by_drv);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_drv);
    var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_drv);

    assert forall id :: id in new_objects.active_non_hcoded_tds
        ==> new_objects.active_non_hcoded_tds[id].pid != NULL;
}

lemma Lemma_DevActivate_ProveHCodedTDsAreRecordedInObjs_InNewK(
    k:State, dev_id:Dev_ID, pid:Partition_ID, k'_subjects:Subjects, k'_objects:Objects
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos)
    requires pid != NULL

    requires var dev_state := IDToDev(k, dev_id);
            var new_dev_state := Dev_State(pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
            var new_devs := k.subjects.devs[dev_id := new_dev_state];
            k'_subjects == Subjects(k.subjects.drvs, new_devs)

    ensures var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var toactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
            var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, toclear_td_ids, pid);
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
            var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);
            toactive_hcoded_td_id in t_objs3.hcoded_tds &&

            var k'_objects := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid);
            forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_objects.hcoded_tds
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var toactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
    var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, toclear_td_ids, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
    var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);

    // Prove toactive_hcoded_td_id in t_objs3.hcoded_tds
    assert toactive_hcoded_td_id in k.objects.hcoded_tds;
    assert toactive_hcoded_td_id in t_objs3.hcoded_tds;

    var new_objects := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid);

    assert forall id :: id in new_objects.active_non_hcoded_tds
        ==> new_objects.active_non_hcoded_tds[id].pid != NULL;
}

lemma Lemma_DevActivate_ProveActiveObjsMustHaveNonNULLPID(
    k:State, dev_id:Dev_ID, pid:Partition_ID
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos)
    requires pid != NULL

    ensures var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var toactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
            var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, toclear_td_ids, pid);
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
            var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);
            toactive_hcoded_td_id in t_objs3.hcoded_tds &&

            var new_objects := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid);
            IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(new_objects)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var toactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
    var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, toclear_td_ids, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
    var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);

    // Prove toactive_hcoded_td_id in t_objs3.hcoded_tds
    assert toactive_hcoded_td_id in k.objects.hcoded_tds;
    assert toactive_hcoded_td_id in t_objs3.hcoded_tds;

    var new_objects := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid);

    assert forall id :: id in new_objects.active_non_hcoded_tds
        ==> new_objects.active_non_hcoded_tds[id].pid != NULL;
}

lemma Lemma_DevDeactivate_ProvePreConditionsOfSetHCodedTDsPIDs(
    k:State, dev_id:Dev_ID
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.active_dos)

    ensures var dev_state := IDToDev(k, dev_id);
            var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var todeactive_hcoded_td_id := dev_state.hcoded_td_id;
            var hcoded_tds := {todeactive_hcoded_td_id};
            var todeactive_other_td_ids := tds_owned_by_dev - hcoded_tds;
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
            var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
            (forall td_id:: td_id in hcoded_tds ==> td_id in t_objs3.hcoded_tds)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
    var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
    var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);

    // Prove toactive_hcoded_td_id in t_objs3.hcoded_tds
    assert todeactive_hcoded_td_id in k.objects.hcoded_tds;
    assert todeactive_hcoded_td_id in t_objs3.hcoded_tds;
}

lemma Lemma_DevDeactivate_ProveAboutAllObjsIDs(
    k:State, dev_id:Dev_ID
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.active_dos)

    ensures var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
            var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
            var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
            todeactive_hcoded_td_id in t_objs3.hcoded_tds &&

            var k'_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);
            AllTDIDs(k'_objects) == AllTDIDs(k.objects) &&
            AllFDIDs(k'_objects) == AllFDIDs(k.objects) &&
            AllDOIDs(k'_objects) == AllDOIDs(k.objects)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
    var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
    var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);

    // Prove toactive_hcoded_td_id in t_objs3.hcoded_tds
    assert todeactive_hcoded_td_id in k.objects.hcoded_tds;
    var k'_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);

    assert AllTDIDs(t_objs1) == AllTDIDs(k.objects) &&
            AllFDIDs(t_objs1) == AllFDIDs(k.objects) &&
            AllDOIDs(t_objs1) == AllDOIDs(k.objects);

    assert AllTDIDs(t_objs2) == AllTDIDs(k.objects) &&
            AllFDIDs(t_objs2) == AllFDIDs(k.objects) &&
            AllDOIDs(t_objs2) == AllDOIDs(k.objects);

    assert AllTDIDs(t_objs3) == AllTDIDs(k.objects) &&
            AllFDIDs(t_objs3) == AllFDIDs(k.objects) &&
            AllDOIDs(t_objs3) == AllDOIDs(k.objects);

    assert AllTDIDs(k'_objects) == AllTDIDs(k.objects) &&
            AllFDIDs(k'_objects) == AllFDIDs(k.objects) &&
            AllDOIDs(k'_objects) == AllDOIDs(k.objects);
}

lemma Lemma_DevDeactivate_ProveActiveObjsMustHaveNonNULLPID(
    k:State, dev_id:Dev_ID
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.active_dos)

    ensures var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
            var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
            var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
            todeactive_hcoded_td_id in t_objs3.hcoded_tds &&

            var new_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);
            IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(new_objects)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
    var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
    var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);

    // Prove toactive_hcoded_td_id in t_objs3.hcoded_tds
    assert todeactive_hcoded_td_id in k.objects.hcoded_tds;
    assert todeactive_hcoded_td_id in t_objs3.hcoded_tds;

    var new_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);

    assert forall id :: id in new_objects.active_non_hcoded_tds
        ==> new_objects.active_non_hcoded_tds[id].pid != NULL;
}

lemma Lemma_ExternalObjsActivate_ProveActiveObjsMustHaveNonNULLPID(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, pid:Partition_ID
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k.objects)

    requires td_ids <= AllTDIDs(k.objects)
    requires fd_ids <= AllFDIDs(k.objects)
    requires do_ids <= AllDOIDs(k.objects)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
    requires (forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) == NULL) &&
            (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) == NULL) &&
            (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) == NULL)

    requires (forall id :: id in td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in do_ids ==> id in k.objects.inactive_dos)

    requires pid != NULL

    ensures var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, td_ids, pid);
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fd_ids, pid);
            var k'_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, do_ids, pid);
            IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k'_objects)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, td_ids, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fd_ids, pid);
    var k'_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, do_ids, pid);

    assert forall id :: id in k'_objects.active_non_hcoded_tds
        ==> k'_objects.active_non_hcoded_tds[id].pid != NULL;
}

lemma Lemma_ExternalObjsDeactivate_ProveActiveObjsMustHaveNonNULLPID(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k.objects)

    requires td_ids <= AllTDIDs(k.objects)
    requires fd_ids <= AllFDIDs(k.objects)
    requires do_ids <= AllDOIDs(k.objects)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
    requires (forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) != NULL) &&
            (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) != NULL) &&
            (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) != NULL)

    requires (forall id :: id in td_ids ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in do_ids ==> id in k.objects.active_dos)

    ensures var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, td_ids);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fd_ids);
            var k'_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, do_ids);
            IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k'_objects)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fd_ids);
    var k'_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, do_ids);

    assert forall id :: id in k'_objects.active_non_hcoded_tds
        ==> k'_objects.active_non_hcoded_tds[id].pid != NULL;
}

// (needs 50s to verify)
lemma Lemma_UnmodifiedSubjObjPIDs_NewKFulfillIsValidState_SubjsOwnObjsThenInSamePartition(k:State, k':State)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs

    requires MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'.objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'.objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'.objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'.objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires forall drv_id :: drv_id in k'.subjects.drvs
                ==> (k'.subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'.subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'.subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'.objects.hcoded_tds[k'.subjects.devs[dev_id].hcoded_td_id].val == k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val)

    requires forall s_id :: s_id in AllSubjsIDs(k.subjects)
                ==> SubjPID(k, s_id) == SubjPID(k', s_id)
    requires forall o_id :: o_id in AllObjsIDs(k.objects)
                ==> ObjPID(k, o_id) == ObjPID(k', o_id)

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
                ==> o_id in AllObjsIDs(k'.objects) &&
                    SubjPID(k', s_id) == ObjPID(k', o_id)
{
    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'.subjects, k'.objects);

    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);
    forall s_id, o_id | s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
        ensures o_id in AllObjsIDs(k'.objects)
        ensures SubjPID(k', s_id) == ObjPID(k', o_id)
    {
        assert s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id);
    }
}

lemma Lemma_DrvWrite_ProveProperty3(
    k:State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val> // IDs of DOs, and values to be written
)
    requires IsValidState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(k.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(k.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(k.objects))

    requires forall fd_id :: fd_id in fd_id_val_map ==>    
            SubjPID(k, drv_sid) == ObjPID(k, fd_id.oid)
    requires forall do_id :: do_id in do_id_val_map ==>        
            SubjPID(k, drv_sid) == ObjPID(k, do_id.oid)
    requires forall td_id :: td_id in td_id_val_map ==>        
            SubjPID(k, drv_sid) == ObjPID(k, td_id.oid)

    ensures (forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                        FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                        DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
                ==> o_id in AllObjsIDs(k.objects) &&
                    ObjPID(k, o_id) == SubjPID(k, drv_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ExternalObjActivateDeactivate_NoSubjsOwnsExternalObjs_EquivilantRepresentation(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires td_ids <= AllTDIDs(k.objects)
    requires fd_ids <= AllFDIDs(k.objects)
    requires do_ids <= AllDOIDs(k.objects)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    (TD_ID(o_id) in td_ids || FD_ID(o_id) in fd_ids || DO_ID(o_id) in do_ids)
                ==> !DoOwnObj(k, s_id, o_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_EmptyPartitionCreate_ProvePreConditions(k:State, k':State, k'_params:ReachableTDsKParams, new_pid:Partition_ID, k'_active_tds_state:TDs_Vals, explored_tds_states:seq<set<TDs_Vals>>)
    requires IsValidState(k) && IsSecureState(k)

    requires var k'_subjects := k.subjects;
            var k'_objects := k.objects;
            var k'_objs_td_ids := AllTDIDs(k.objects);
            var k'_objs_fd_ids := AllFDIDs(k.objects);
            var k'_objs_do_ids := AllDOIDs(k.objects);
            var k'_active_tds := AllActiveTDs_SlimState(k'_objects);
            k'_params == ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

    requires new_pid != NULL
    requires new_pid !in k.pids

    requires var k'_objects := k.objects;
             k'_active_tds_state == ActiveTDsState_SlimState(k'_objects)
    requires MapGetKeys(k'_active_tds_state) == k'_params.all_active_tds
    requires explored_tds_states == [{k'_active_tds_state}]

    requires var k'_subjects := k.subjects;
            var k'_objects := k.objects;
            var pids' := k.pids + {new_pid};
            k' == State(k'_subjects, k'_objects, pids', k.tds_to_all_states);
           
    ensures k'_params == KToKParams(k')
    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k'_params.all_active_tds
    ensures var k'_subjects := k.subjects;
            var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);
            forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (k'_active_tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params, k'_active_devs, k'_active_tds_state, tds_state2))
    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, tds_state2)
{
    forall tds_state2 | tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
        ensures TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, tds_state2)
    {
        assert tds_state2 == k'_active_tds_state;
    }
}

lemma Lemma_DrvActivate_DrvObjsInKMustBeInactive(k:State, drv_id:Drv_ID)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires drv_id in k.subjects.drvs
    requires SubjPID(k, drv_id.sid) == NULL

    ensures (forall id :: id in k.subjects.drvs[drv_id].td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in k.subjects.drvs[drv_id].fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in k.subjects.drvs[drv_id].do_ids ==> id in k.objects.inactive_dos)
{
    forall id | id in k.subjects.drvs[drv_id].td_ids
        ensures ObjPID(k, id.oid) == NULL
    {
        assert DoOwnObj(k, drv_id.sid, id.oid);
    }

    forall id | id in k.subjects.drvs[drv_id].fd_ids
        ensures ObjPID(k, id.oid) == NULL
    {
        assert DoOwnObj(k, drv_id.sid, id.oid);
    }

    forall id | id in k.subjects.drvs[drv_id].do_ids
        ensures ObjPID(k, id.oid) == NULL
    {
        assert DoOwnObj(k, drv_id.sid, id.oid);
    }

    forall id | id in k.subjects.drvs[drv_id].td_ids 
        ensures id in k.objects.inactive_non_hcoded_tds
    {
        if(id in k.objects.hcoded_tds)
        {
            var dev_id :| dev_id in k.subjects.devs && k.subjects.devs[dev_id].hcoded_td_id == id;
            Lemma_DevsOwnHCodedTDs(k.subjects, dev_id, id);
            assert DoOwnObj(k, dev_id.sid, id.oid);

            assert id in k.subjects.drvs[drv_id].td_ids;
            assert DoOwnObj(k, drv_id.sid, id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                    s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                    DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                        ==> s_id1 == s_id2);
            assert false;
        }
        assert id !in k.objects.hcoded_tds;

        Lemma_InActiveObjsMustInInActiveSet_TD(k, id);
    }

    forall id | id in k.subjects.drvs[drv_id].fd_ids 
        ensures id in k.objects.inactive_fds
    {
        Lemma_InActiveObjsMustInInActiveSet_FD(k, id);
    }

    forall id | id in k.subjects.drvs[drv_id].do_ids 
        ensures id in k.objects.inactive_dos
    {
        Lemma_InActiveObjsMustInInActiveSet_DO(k, id);
    }
}

lemma Lemma_DevActivate_DevObjsInKMustBeInactive(k:State, dev_id:Dev_ID)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires dev_id in k.subjects.devs
    requires SubjPID(k, dev_id.sid) == NULL

    ensures (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos)
{
    forall id | id in k.subjects.devs[dev_id].td_ids
        ensures ObjPID(k, id.oid) == NULL
    {
        assert DoOwnObj(k, dev_id.sid, id.oid);
    }

    forall id | id in k.subjects.devs[dev_id].fd_ids
        ensures ObjPID(k, id.oid) == NULL
    {
        assert DoOwnObj(k, dev_id.sid, id.oid);
    }

    forall id | id in k.subjects.devs[dev_id].do_ids
        ensures ObjPID(k, id.oid) == NULL
    {
        assert DoOwnObj(k, dev_id.sid, id.oid);
    }

    forall id | id in k.subjects.devs[dev_id].td_ids &&
                id != k.subjects.devs[dev_id].hcoded_td_id
        ensures id in k.objects.inactive_non_hcoded_tds
    {
        if(id in k.objects.hcoded_tds)
        {
            var dev_id2 :| dev_id2 in k.subjects.devs && k.subjects.devs[dev_id2].hcoded_td_id == id;
            Lemma_DevsOwnHCodedTDs(k.subjects, dev_id2, id);
            assert DoOwnObj(k, dev_id2.sid, id.oid);

            assert id in k.subjects.devs[dev_id].td_ids;
            assert DoOwnObj(k, dev_id.sid, id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                    s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                    DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                        ==> s_id1 == s_id2);
            assert false;
        }
        assert id !in k.objects.hcoded_tds;

        Lemma_InActiveObjsMustInInActiveSet_TD(k, id);
    }

    forall id | id in k.subjects.devs[dev_id].fd_ids 
        ensures id in k.objects.inactive_fds
    {
        Lemma_InActiveObjsMustInInActiveSet_FD(k, id);
    }

    forall id | id in k.subjects.devs[dev_id].do_ids 
        ensures id in k.objects.inactive_dos
    {
        Lemma_InActiveObjsMustInInActiveSet_DO(k, id);
    }
}

lemma Lemma_DrvDeactivate_DrvObjsInKMustBeActive(k:State, drv_id:Drv_ID)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires drv_id in k.subjects.drvs
    requires SubjPID(k, drv_id.sid) != NULL

    ensures (forall id :: id in k.subjects.drvs[drv_id].td_ids ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in k.subjects.drvs[drv_id].fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in k.subjects.drvs[drv_id].do_ids ==> id in k.objects.active_dos)
{
    forall id | id in k.subjects.drvs[drv_id].td_ids
        ensures ObjPID(k, id.oid) != NULL
    {
        assert DoOwnObj(k, drv_id.sid, id.oid);
    }

    forall id | id in k.subjects.drvs[drv_id].fd_ids
        ensures ObjPID(k, id.oid) != NULL
    {
        assert DoOwnObj(k, drv_id.sid, id.oid);
    }

    forall id | id in k.subjects.drvs[drv_id].do_ids
        ensures ObjPID(k, id.oid) != NULL
    {
        assert DoOwnObj(k, drv_id.sid, id.oid);
    }

    forall id | id in k.subjects.drvs[drv_id].td_ids 
        ensures id in k.objects.active_non_hcoded_tds
    {
        if(id in k.objects.hcoded_tds)
        {
            var dev_id :| dev_id in k.subjects.devs && k.subjects.devs[dev_id].hcoded_td_id == id;
            Lemma_DevsOwnHCodedTDs(k.subjects, dev_id, id);
            assert DoOwnObj(k, dev_id.sid, id.oid);

            assert id in k.subjects.drvs[drv_id].td_ids;
            assert DoOwnObj(k, drv_id.sid, id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                    s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                    DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                        ==> s_id1 == s_id2);
            assert false;
        }
        assert id !in k.objects.hcoded_tds;

        Lemma_ActiveObjsMustInActiveSet_TD(k, id);
    }

    forall id | id in k.subjects.drvs[drv_id].fd_ids 
        ensures id in k.objects.active_fds
    {
        Lemma_ActiveObjsMustInActiveSet_FD(k, id);
    }

    forall id | id in k.subjects.drvs[drv_id].do_ids 
        ensures id in k.objects.active_dos
    {
        Lemma_ActiveObjsMustInActiveSet_DO(k, id);
    }
}

lemma Lemma_DevDeactivate_DevObjsInKMustBeActive(k:State, dev_id:Dev_ID)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires dev_id in k.subjects.devs
    requires SubjPID(k, dev_id.sid) != NULL

    ensures (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.active_dos)

    ensures forall td_id:: td_id in {k.subjects.devs[dev_id].hcoded_td_id} ==> td_id in k.objects.hcoded_tds
{
    forall id | id in k.subjects.devs[dev_id].td_ids
        ensures ObjPID(k, id.oid) != NULL
    {
        assert DoOwnObj(k, dev_id.sid, id.oid);
    }

    forall id | id in k.subjects.devs[dev_id].fd_ids
        ensures ObjPID(k, id.oid) != NULL
    {
        assert DoOwnObj(k, dev_id.sid, id.oid);
    }

    forall id | id in k.subjects.devs[dev_id].do_ids
        ensures ObjPID(k, id.oid) != NULL
    {
        assert DoOwnObj(k, dev_id.sid, id.oid);
    }

    forall id | id in k.subjects.devs[dev_id].td_ids &&
                id != k.subjects.devs[dev_id].hcoded_td_id
        ensures id in k.objects.active_non_hcoded_tds
    {
        if(id in k.objects.hcoded_tds)
        {
            var dev_id2 :| dev_id2 in k.subjects.devs && k.subjects.devs[dev_id2].hcoded_td_id == id;
            Lemma_DevsOwnHCodedTDs(k.subjects, dev_id2, id);
            assert DoOwnObj(k, dev_id2.sid, id.oid);

            assert id in k.subjects.devs[dev_id].td_ids;
            assert DoOwnObj(k, dev_id.sid, id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                    s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                    DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                        ==> s_id1 == s_id2);
            assert false;
        }
        assert id !in k.objects.hcoded_tds;

        Lemma_ActiveObjsMustInActiveSet_TD(k, id);
    }

    forall id | id in k.subjects.devs[dev_id].fd_ids 
        ensures id in k.objects.active_fds
    {
        Lemma_ActiveObjsMustInActiveSet_FD(k, id);
    }

    forall id | id in k.subjects.devs[dev_id].do_ids 
        ensures id in k.objects.active_dos
    {
        Lemma_ActiveObjsMustInActiveSet_DO(k, id);
    }
}

lemma Lemma_ExternalObjsActivate_ExternalObjsInKMustBeInactive(k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k)
    
    requires td_ids <= AllTDIDs(k.objects)
    requires fd_ids <= AllFDIDs(k.objects)
    requires do_ids <= AllDOIDs(k.objects)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
    requires (forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) == NULL) &&
            (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) == NULL) &&
            (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) == NULL)

    ensures (forall id :: id in td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in do_ids ==> id in k.objects.inactive_dos)

    ensures (forall id :: id in td_ids ==> id.oid in AllObjsIDs(k.objects)) &&
            (forall id :: id in fd_ids ==> id.oid in AllObjsIDs(k.objects)) &&
            (forall id :: id in do_ids ==> id.oid in AllObjsIDs(k.objects))
{
    forall id | id in td_ids 
        ensures id in k.objects.inactive_non_hcoded_tds
    {
        if(id in k.objects.hcoded_tds)
        {
            var dev_id :| dev_id in k.subjects.devs && k.subjects.devs[dev_id].hcoded_td_id == id;
            Lemma_DevsOwnHCodedTDs(k.subjects, dev_id, id);
            assert DoOwnObj(k, dev_id.sid, id.oid);

            assert false;
        }
        assert id !in k.objects.hcoded_tds;

        Lemma_InActiveObjsMustInInActiveSet_TD(k, id);
    }

    forall id | id in fd_ids 
        ensures id in k.objects.inactive_fds
    {
        Lemma_InActiveObjsMustInInActiveSet_FD(k, id);
    }

    forall id | id in do_ids 
        ensures id in k.objects.inactive_dos
    {
        Lemma_InActiveObjsMustInInActiveSet_DO(k, id);
    }
}

lemma Lemma_ExternalObjsDeactivate_ExternalObjsInKMustBeActive(k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k)
    
    requires td_ids <= AllTDIDs(k.objects)
    requires fd_ids <= AllFDIDs(k.objects)
    requires do_ids <= AllDOIDs(k.objects)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
    requires (forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) != NULL) &&
            (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) != NULL) &&
            (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) != NULL)

    ensures (forall id :: id in td_ids ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in do_ids ==> id in k.objects.active_dos)
{
    forall id | id in td_ids 
        ensures id in k.objects.active_non_hcoded_tds
    {
        if(id in k.objects.hcoded_tds)
        {
            var dev_id :| dev_id in k.subjects.devs && k.subjects.devs[dev_id].hcoded_td_id == id;
            Lemma_DevsOwnHCodedTDs(k.subjects, dev_id, id);
            assert DoOwnObj(k, dev_id.sid, id.oid);

            assert false;
        }
        assert id !in k.objects.hcoded_tds;

        Lemma_ActiveObjsMustInActiveSet_TD(k, id);
    }

    forall id | id in fd_ids 
        ensures id in k.objects.active_fds
    {
        Lemma_ActiveObjsMustInActiveSet_FD(k, id);
    }

    forall id | id in do_ids 
        ensures id in k.objects.active_dos
    {
        Lemma_ActiveObjsMustInActiveSet_DO(k, id);
    }
}

lemma Lemma_DevDeactivate_ProveReachableTDsStatesAreSeucre(k:State)
    requires IsValidState(k) && IsSecureState(k)
    ensures var k_tds_states := AllReachableActiveTDsStates(k);
            var k_params := KToKParams(k);
            forall tds_state2 :: tds_state2 in k_tds_states
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)
{
    var k_tds_states := AllReachableActiveTDsStates(k);
    var k_params := KToKParams(k);

    forall tds_state2 | tds_state2 in k_tds_states
        ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)
    {
        // Dafny can automatically prove it
    }
}




//******** Private Lemmas  ********//
lemma Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed_Property2(
    k:State, dev_sid:Subject_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>,
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires IDToDev(k, Dev_ID(dev_sid)).pid != NULL
        // Requirement: The driver is in the I/O system and is active

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(k.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(k.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(k.objects))
        // Requirement: Written TDs, FDs and DOs are in the I/O system
    requires forall td_id :: td_id in td_id_val_map 
            ==> td_id in AllTDIDs(k.objects) &&
                ObjPID(k, td_id.oid) == SubjPID_DevID(k, Dev_ID(dev_sid))
    requires forall fd_id :: fd_id in fd_id_val_map 
            ==> fd_id in AllFDIDs(k.objects) &&
                ObjPID(k, fd_id.oid) == SubjPID_DevID(k, Dev_ID(dev_sid))
    requires forall do_id :: do_id in do_id_val_map 
            ==> do_id in AllDOIDs(k.objects) &&
                ObjPID(k, do_id.oid) == SubjPID_DevID(k, Dev_ID(dev_sid))

    ensures forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                    FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                    DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
            ==> o_id in AllObjsIDs(k.objects) &&
                ObjPID(k, o_id) == SubjPID(k, dev_sid)
        // Property: All written objects are in the same partition with the device 
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevWrite_CurrentTDsStateReachNewTDsStateInOneStep(
    k:State, dev_id:Dev_ID, td_id_val_map:map<TD_ID, TD_Val>, new_tds_state:TDs_Vals
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)
    
    requires TDsStateGetTDIDs(new_tds_state) == AllActiveTDs(k) 
        // Requirement: <new_tds_state> must includes all active TDs

    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= AllTDIDs(k.objects)

    requires TDsStateGetTDIDs(ActiveTDsState(k)) == AllActiveTDs(k) 
    requires forall td_id2 :: td_id2 in TDsStateDiff(new_tds_state, ActiveTDsState(k))
                ==>  td_id2 in td_id_val_map &&
                     TDsStateDiff(new_tds_state, ActiveTDsState(k))[td_id2] == td_id_val_map[td_id2]
        // Requirement: The differences of active TDs' states (new_tds_state,  
        // ActiveTDsState(k)) must be included in td_id_val_map
    requires forall td_id2 :: td_id2 in td_id_val_map ==> td_id2 in AllTDIDs(k.objects)
    requires forall td_id2 :: td_id2 in td_id_val_map
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    td_id2 in GetTDVal(k, td_id).trans_params_tds &&
                    W in GetTDVal(k, td_id).trans_params_tds[td_id2].amodes &&
                        // The TD references the target TD (<td_id2>) with W
                    td_id_val_map[td_id2] in GetTDVal(k, td_id).trans_params_tds[td_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each TD writes in <td_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)

    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(KToKParams(k), dev_id, ActiveTDsState(k), new_tds_state)
        // Property: ActiveTDsState(k) can reach <new_tds_state> in one TDs write 
        // operation
{
    // Dafny can automatically prove this lemma.
}

lemma Lemma_DevWrite_NewReachableActiveTDsStatesIsSubsetOfTheOneInK(
    k:State, k_params:ReachableTDsKParams, dev_id:Dev_ID, k':State, k'_active_tds_state:TDs_Vals
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)

    requires k_params == KToKParams(k)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params);
    requires forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
        // Requirements: Proved propertis of k_params

    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The device must be active

    requires MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'.objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'.objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'.objects) == AllDOIDs(k.objects)

    requires k'.subjects == k.subjects
    requires AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects)
    requires AllObjsIDs(k'.objects) == AllObjsIDs(k.objects)

    requires TDsStateGetTDIDs(k'_active_tds_state) == AllActiveTDs(k')
        // Requirement: <k'_active_tds_state> includes all active TDs in k' 

    requires forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2)

    requires IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params, 
                dev_id, ActiveTDsState(k), k'_active_tds_state)
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, 
                dev_id, ActiveTDsState(k), k'_active_tds_state)

    ensures forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
                ==> IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2)
    ensures forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
                ==> IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            AllActiveDevs(k), ActiveTDsState(k), tds_state2)
        // Properties needed by the property below
    ensures AllActiveTDs(k') == AllActiveTDs(k)
    ensures forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k') &&
                    (k'_active_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2))
                                                // k'_active_tds_state -->* tds_state2
                ==> IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        AllActiveDevs(k), ActiveTDsState(k), tds_state2)
                                                // ActiveTDsState(k) -->1+ tds_state2
{
    assert AllActiveTDs(k') == AllActiveTDs(k);
    Lemma_TDsStateAReachTDsStateBInOneStep_ThenTDsStatesReachedByBInChainAlsoReachedByAInChain(k_params, 
        dev_id, AllActiveDevs(k), ActiveTDsState(k), k'_active_tds_state);
}

lemma Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
    requires IsValidState_ReachableTDsStates(k)
    requires IsSecureState_SI1(k)

    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
{
    // Dafny can automatically prove this lemma
}

// (needs ~100s to verify)
lemma Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant_More(k:State)
    requires (forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                 ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)

    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                            dev_id in AllActiveDevs(k) &&
                            td_id2 in TDsStateGetTDIDs(tds_state2)
                        ==> CanActiveDevReadActiveTD_PreConditions(KToKParams(k), tds_state2, dev_id, td_id2)))
        // Property needed by the properties below
    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
             <==>
            (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), tds_state2, td_id2))) &&
                        // The TD contains valid references only 
            (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))

    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
            <==> 
            (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2))
{
    Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant_More_Private1(k);
    Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant_More_Private2(k);
}

lemma Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant_More_Private1(k:State)
    requires (forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                 ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)

    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                            dev_id in AllActiveDevs(k) &&
                            td_id2 in TDsStateGetTDIDs(tds_state2)
                        ==> CanActiveDevReadActiveTD_PreConditions(KToKParams(k), tds_state2, dev_id, td_id2)))
        // Property needed by the properties below
    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
             <==>
            (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), tds_state2, td_id2))) &&
                        // The TD contains valid references only 
            (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
{
    // Dafny can automatically prove this lemma
}

// Note: need 100s to verify
lemma Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant_More_Private2(k:State)
    requires (forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                 ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)

    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                            dev_id in AllActiveDevs(k) &&
                            td_id2 in TDsStateGetTDIDs(tds_state2)
                        ==> CanActiveDevReadActiveTD_PreConditions(KToKParams(k), tds_state2, dev_id, td_id2)))
        // Property needed by the properties below
    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
            <==> 
            (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2))
{
    var k_params := KToKParams(k);
    forall tds_state2 | tds_state2 in AllReachableActiveTDsStates(k)
        ensures (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2))
                <==> (
                        CanActiveDevReadActiveTD_KParams_PreConditions(k_params) &&
                        ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)
                    )
        ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)
                    <==> (
                        CanActiveDevReadActiveTD_KParams_PreConditions(k_params) &&
                        ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)
                    )
                
    {
        // Dafny can automatically prove this statement
    }
}

// Note: need 100s to verify
lemma Lemma_ActiveTDsUnchanged_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
    k:State, k_params:ReachableTDsKParams, from_tds_state:TDs_Vals, found_tds_states:set<TDs_Vals>, status:bool
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)

    requires k_params == KToKParams(k)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params);
    requires forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
        // Requirements: Proved propertis of k_params

    requires TDsStateGetTDIDs(from_tds_state) == AllActiveTDs(k)
    requires forall tds_state2 :: tds_state2 in found_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
        // Requirement: The TDs' state in k includes all active TDs. In other 
        // words, active TDs are unchanged
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> IsDevID(k, dev_id2) &&
                    SubjPID_DevID(k, dev_id2) != NULL
        // Requirement: The devices in AllActiveDevs(k) must be active

    requires forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
                ==> IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            AllActiveDevs(k), from_tds_state, tds_state2)
    requires forall td_id2, dev_id, tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    dev_id in AllActiveDevs(k) && 
                    td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> CanActiveDevReadActiveTD_PreConditions(k_params, tds_state2, dev_id, td_id2)

    requires forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (from_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), from_tds_state, tds_state2))
                ==> (forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2))

    requires forall tds_state2 :: tds_state2 in found_tds_states
                ==> (from_tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                                                        AllActiveDevs(k), from_tds_state, tds_state2))
        // Requirement: from_tds_state -->* found_tds_states

    requires status <==> AllReachableActiveTDsStatesAreSecure(k_params, AllActiveDevs(k), found_tds_states)
        // Requirement: Any active TDs read by any active devices have no invalid
        // references to I/O objects in each of <found_tds_states> 

    ensures status == true
{
    // Dafny can automatically prove this lemma.
}