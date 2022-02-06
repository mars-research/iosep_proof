include "../Abstract/Properties.dfy"
include "../Abstract/Lemmas_Ops.dfy"
include "../Abstract/Model.dfy"

//******** TDsStateGetTDIDs ********//
lemma Lemma_K_TDsStateGetTDIDs_TDsAreInAllObjs(k:State, tds_states:seq<TDs_Vals>)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires forall tds_state2 :: tds_state2 in tds_states
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
    
    ensures forall tds_state, td_id :: tds_state in tds_states &&
                    td_id in TDsStateGetTDIDs(tds_state)
                ==> td_id.oid in AllObjsIDs(k.objects)
{
    Lemma_SameIDsIffSameInternalIDs();
    forall tds_state, td_id | tds_state in tds_states &&
                td_id in TDsStateGetTDIDs(tds_state)
        ensures td_id.oid in AllObjsIDs(k.objects)
    {
        assert TDsStateGetTDIDs(tds_state) == AllActiveTDs(k);

        assert td_id in AllActiveTDs(k);
        assert td_id in AllTDIDs(k.objects);
    }
}

lemma Lemma_K_TDsStateGetTDIDs_SameInSeq_LastTwoElems(tds_states:seq<TDs_Vals>, s:set<TD_ID>)
    requires |tds_states| >= 2
    requires forall tds_state2 :: tds_state2 in tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == s

    ensures forall td_id :: td_id in TDsStateGetTDIDs(tds_states[|tds_states|-2])
                <==> td_id in tds_states[|tds_states|-2] && td_id in tds_states[|tds_states|-1]
    ensures forall td_id :: td_id in TDsStateGetTDIDs(tds_states[|tds_states|-1])
                <==> td_id in tds_states[|tds_states|-2] && td_id in tds_states[|tds_states|-1]
{
    // Dafny can automatically prove this lemma
    forall td_id | td_id in TDsStateGetTDIDs(tds_states[|tds_states|-2])
        ensures td_id in tds_states[|tds_states|-2] && td_id in tds_states[|tds_states|-1]
    {
        assert td_id in tds_states[|tds_states|-2];
        assert td_id in s;

        assert tds_states[|tds_states|-1] in tds_states;
        assert td_id in tds_states[|tds_states|-1];
    }
}

lemma Lemma_K_TDsInAllActiveTDsAreInState(k:State, tds_state:TDs_Vals, td_id:TD_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs_SlimState(k.objects)
    requires td_id in TDsStateGetTDIDs(tds_state)

    ensures td_id in AllTDIDs(k.objects)
{
    assert td_id in AllTDIDs(k.objects);
}

lemma Lemma_K_TDsStateGetTDIDs_SameBetweenTwo(tds_state1:TDs_Vals, tds_state2:TDs_Vals)
    requires TDsStateGetTDIDs(tds_state1) == TDsStateGetTDIDs(tds_state2)

    ensures forall td_id :: td_id in TDsStateGetTDIDs(tds_state1)
                <==> td_id in tds_state1 && td_id in tds_state2
    ensures forall td_id :: td_id in TDsStateGetTDIDs(tds_state2)
                <==> td_id in tds_state1 && td_id in tds_state2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_TDsStateGetTDIDs_SameInSeq(tds_states:seq<TDs_Vals>, s:set<TD_ID>)
    requires |tds_states| > 0
    requires forall tds_state2 :: tds_state2 in tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == s

    ensures forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_states[0])
{
    // Dafny can automatically prove this lemma
}




//******** State Properties ********//
lemma Lemma_K_SameObjIDs_ProveIsValidState_Objects_UniqueObjIDs(k_objs:Objects, k'_objs:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objs)
        // Requirement: Objects have different internal IDs

    requires MapGetKeys(k'_objs.active_non_hcoded_tds) == MapGetKeys(k_objs.active_non_hcoded_tds)
    requires MapGetKeys(k'_objs.active_fds) == MapGetKeys(k_objs.active_fds)
    requires MapGetKeys(k'_objs.active_dos) == MapGetKeys(k_objs.active_dos)
    requires k'_objs.inactive_non_hcoded_tds == k_objs.inactive_non_hcoded_tds
    requires k'_objs.inactive_fds == k_objs.inactive_fds
    requires k'_objs.inactive_dos == k_objs.inactive_dos
    requires MapGetKeys(k'_objs.hcoded_tds) == MapGetKeys(k_objs.hcoded_tds)

    ensures IsValidState_Objects_UniqueObjIDs(k'_objs)
{
    reveal IsValidState_Objects_UniqueObjIDs();
}

// Lemma: Return the device that owns the target hardcoded TD
lemma Lemma_K_HCodedTDGetOwnerDev(k:State, hcoded_td_id:TD_ID) returns (dev_id:Dev_ID)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires hcoded_td_id in k.objects.hcoded_tds 

    ensures dev_id in k.subjects.devs
    ensures k.subjects.devs[dev_id].hcoded_td_id == hcoded_td_id
    ensures forall s_id:Subject_ID :: IsSubjID(k.subjects, s_id) && s_id != dev_id.sid
                ==> !DoOwnObj(k, s_id, hcoded_td_id.oid)
{
    var t_dev_id :|  t_dev_id in k.subjects.devs && k.subjects.devs[t_dev_id].hcoded_td_id == hcoded_td_id;

    forall s_id:Subject_ID | IsSubjID(k.subjects, s_id) && s_id != t_dev_id.sid
        ensures !DoOwnObj(k, s_id, hcoded_td_id.oid)
    {
        if(DoOwnObj(k, s_id, hcoded_td_id.oid))
        {
            assert DoOwnObj(k, t_dev_id.sid, hcoded_td_id.oid);
            assert false;
        }
    }

    return t_dev_id;
}

lemma Lemma_K_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    
    ensures forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= AllTDIDs(k.objects)
{
    // Dafny can automatically prove this lemma
}

// [NOTE] Needs 40s to verify
lemma Lemma_K_FindAllActiveTDsStatesByDev_KParams_PreConditions_Prove(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k) 
    ensures FindAllActiveTDsStatesByDev_KParams_PreConditions(KToKParams(k))
{
    var k_params := KToKParams(k); 

    Lemma_ObjsInSubjsAreAlsoInState(k);

    forall s_id, o_id | s_id in AllSubjsIDs(k_params.subjects) &&
                    DoOwnObj_SlimState(k_params.subjects, s_id, o_id)
        ensures o_id in k_params.objs_pids
        ensures k_params.objs_pids[o_id] == SubjPID_SlimState(k_params.subjects, s_id)
    {
        assert s_id in AllSubjsIDs(k.subjects);
        assert DoOwnObj(k, s_id, o_id);

        assert o_id in AllObjsIDs(k.objects);
        assert o_id in k_params.objs_pids;

        assert SubjPID(k, s_id) == ObjPID(k, o_id);
    }
}

lemma Lemma_K_IsValidState_ReachableTDsStates_Apply(
    k:State, k_tds_state:TDs_Vals,
    dev_id:Dev_ID, td_id:TD_ID
)
    requires IsValidState(k) 

    requires dev_id in AllActiveDevs(k)
    requires td_id in k_tds_state
    requires k_tds_state == ActiveTDsState(k)
    requires CanActiveDevReadActiveTD(KToKParams(k), k_tds_state, dev_id, td_id)

    ensures !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), k_tds_state, td_id);
{
    assert IsValidState_ReachableTDsStates(k);
    assert k_tds_state in AllReachableActiveTDsStates(k);
}




//******** Reachable TDs and TDs' States ********//
predicate P_ExistsTDXDevHasReadTransferToAndIncludeWriteTransferToTD(
    k_params:ReachableTDsKParams, dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals, td_id:TD_ID
)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k_params.subjects.drvs) && (Dev_ID(dev_sid) in k_params.subjects.devs)
                 ==> (drv_sid != dev_sid)

    requires TDsStateGetTDIDs(from_tds_state) == k_params.all_active_tds
    requires TDsStateGetTDIDs(to_tds_state) == k_params.all_active_tds
        // Requirement: <from_tds_state> and <to_tds_state> must includes all active TDs
    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires td_id in to_tds_state;
{
    exists tdx_id :: (dev_id in AllActiveDevs_SlimState(k_params.subjects) &&
                                tdx_id in k_params.all_active_tds &&
                                CanActiveDevReadActiveTD_PreConditions(k_params, from_tds_state, dev_id, tdx_id) &&
                                CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id) &&
                                td_id in from_tds_state[tdx_id].trans_params_tds &&
                                W in from_tds_state[tdx_id].trans_params_tds[td_id].amodes &&
                                    // The TD references the target TD (<td_id2>) with W
                                to_tds_state[td_id] in from_tds_state[tdx_id].trans_params_tds[td_id].vals)
}

lemma Lemma_K_IsActiveTDsStateReachActiveTDsStateInOneStep_TDModificationsAreFromTDs(
    k_params:ReachableTDsKParams, dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k_params.subjects.drvs) && (Dev_ID(dev_sid) in k_params.subjects.devs)
                 ==> (drv_sid != dev_sid)

    requires TDsStateGetTDIDs(from_tds_state) == k_params.all_active_tds
    requires TDsStateGetTDIDs(to_tds_state) == k_params.all_active_tds
        // Requirement: <from_tds_state> and <to_tds_state> must includes all active TDs
    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_tds_state, to_tds_state)

    ensures forall td_id :: td_id in TDsStateDiff(to_tds_state, from_tds_state)
                ==> P_ExistsTDXDevHasReadTransferToAndIncludeWriteTransferToTD(k_params, dev_id, from_tds_state, to_tds_state, td_id)
{
    assert dev_id in k_params.subjects.devs;
    Lemma_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(k_params.subjects, dev_id);
    assert SubjPID_SlimState(k_params.subjects, dev_id.sid) != NULL;
    assert dev_id in AllActiveDevs_SlimState(k_params.subjects);

    var tds_diff := TDsStateDiff(to_tds_state, from_tds_state);
    var tds_state := from_tds_state;
    assert forall td_id, td_new_cfg :: td_id in tds_diff &&
                td_new_cfg == tds_diff[td_id]
                    ==> (exists tdx_id :: 
                            tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(tds_state, tdx_id, td_id, td_new_cfg));
                                    // the active TD refs the TD with W and the new TD cfg

    forall td_id | td_id in tds_diff
        ensures exists tdx_id :: 
                    (    tdx_id in k_params.all_active_tds &&
                        CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id) &&
                        td_id in from_tds_state[tdx_id].trans_params_tds &&
                        W in from_tds_state[tdx_id].trans_params_tds[td_id].amodes &&
                            // The TD references the target TD (<td_id2>) with W
                        to_tds_state[td_id] in from_tds_state[tdx_id].trans_params_tds[td_id].vals)
    {
        {
            var td_new_cfg := tds_diff[td_id];
            var tdx_id :|   tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(tds_state, tdx_id, td_id, td_new_cfg);

            assert tdx_id in k_params.all_active_tds &&
                    CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id);
        }
    }
}

lemma Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_Prove(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, tds_states:seq<TDs_Vals>, devs:seq<Dev_ID>,
    from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, active_devs, from_tds_state, to_tds_state)
    requires |tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
                |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
                tds_states[0] == from_tds_state &&
                tds_states[|tds_states|-1] == to_tds_state &&
                (forall i :: 0<=i<|tds_states| - 1 
                    ==> (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            devs[i], tds_states[i], tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            devs[i], tds_states[i], tds_states[i+1])))

    
    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, from_tds_state, to_tds_state)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_IfExistsASequence_ThenReturnsTrue(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, tds_states:seq<TDs_Vals>, devs:seq<Dev_ID>
)
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> dev_id2 in k_params.hcoded_tds
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires |tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
                |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
                (forall i :: 0<=i<|tds_states| - 1 
                    ==> (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            devs[i], tds_states[i], tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            devs[i], tds_states[i], tds_states[i+1])))

    ensures forall tds_state :: tds_state in tds_states
                ==> (tds_states[0] == tds_state || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                                active_devs, tds_states[0], tds_state) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                                active_devs, tds_states[0], tds_state)));
{
    var i := 0;

    while (i < |tds_states|)
        invariant i <= |tds_states|

        invariant forall tds_state :: tds_state in tds_states[..i]
                ==> (tds_states[0] == tds_state || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                                active_devs, tds_states[0], tds_state) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                                active_devs, tds_states[0], tds_state)))
    {
        if(i > 0)
        {
            var part_tds_states := tds_states[..i];
            var new_tds_states := SeqAppend(part_tds_states, tds_states[i]);
            var new_devs := SeqAppend(devs[..i-1], devs[i-1]);

            assert |new_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in new_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
                |new_devs| == |new_tds_states| - 1 && (forall dev_id2 :: dev_id2 in new_devs ==> dev_id2 in active_devs) &&
                new_tds_states[0] == tds_states[0] &&
                new_tds_states[|new_tds_states|-1] == tds_states[i];

            Lemma_SequenceHighlightLastElemOfSubSeq(new_tds_states, part_tds_states);
            assert new_tds_states[|new_tds_states|-2] == part_tds_states[|part_tds_states|-1];
            
            forall i | 0<=i<|new_tds_states| - 1 
                    ensures (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            new_devs[i], new_tds_states[i], new_tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            new_devs[i], new_tds_states[i], new_tds_states[i+1]))
            {
                if(i != |new_tds_states| - 2)
                {
                    assert (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            new_devs[i], new_tds_states[i], new_tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            new_devs[i], new_tds_states[i], new_tds_states[i+1]));
                }
                else
                {
                    assert (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            new_devs[i], new_tds_states[i], new_tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            new_devs[i], new_tds_states[i], new_tds_states[i+1]));
                }
            }
            assert IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, active_devs, tds_states[0], tds_states[i]);

            Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_Prove(k_params, active_devs, new_tds_states, new_devs, tds_states[0], tds_states[i]);
            assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_states[0], tds_states[i]);

            Lemma_SequenceHighlightLastElem(tds_states[..i+1]);
            forall tds_state | tds_state in tds_states[..i+1]
                ensures (tds_states[0] == tds_state || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                                active_devs, tds_states[0], tds_state) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                                active_devs, tds_states[0], tds_state)))
            {
                if(tds_state !in tds_states[..i])
                {
                    assert tds_state == tds_states[i];
                }
            }
        }
        
        i := i + 1;
    }
}

lemma Lemma_K_SecureState_IfDevHasTransferToTD_ThenTheyAreInSamePartition(
    k:State, k_params:ReachableTDsKParams, active_devs:set<Dev_ID>,
    tds_state:TDs_Vals, dev_id:Dev_ID, td_id:TD_ID
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)

    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds_state, dev_id, td_id)
    requires k_params == KToKParams(k)

    requires active_devs <= AllActiveDevs(k)
    requires dev_id in active_devs
    requires ActiveTDsStateIsSecure(k_params, active_devs, tds_state)
        // Requirement: <tds_state> is secure
    requires CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)
        // Requirement: Device (<dev_id>) can read the TD (<td_id>)

    ensures SubjPID_DevID(k, dev_id) == ObjPID(k, td_id.oid)
{
    Lemma_SecureActiveTDsState_TDsReadByActiveDevAreInSamePartitionWithDev_ForSubsetOfActiveDevs(
        k, k_params, active_devs, tds_state, dev_id, td_id);
}

lemma Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_Apply(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
) returns (result_tds_states:seq<TDs_Vals>, result_devs:seq<Dev_ID>)
    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(
                    k_params, active_devs, from_tds_state, to_tds_state)
    requires IsActiveTDsStateReachActiveTDsStateInChain(
                    k_params, active_devs, from_tds_state, to_tds_state)

    ensures |result_tds_states| >= 2 && 
            (forall tds_state2 :: tds_state2 in result_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == 
                    k_params.all_active_tds) &&
            |result_devs| == |result_tds_states| - 1 && (forall dev_id2 :: dev_id2 in result_devs ==> dev_id2 in active_devs) &&
            result_tds_states[|result_tds_states| - 1] == to_tds_state && // last TDs' state is the <to_tds_state>
            result_tds_states[0] == from_tds_state && // first TDs' state is the <from_tds_state>
            (forall i :: 0<=i<|result_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params, result_devs[i], result_tds_states[i], result_tds_states[i+1]) &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, result_devs[i], result_tds_states[i], result_tds_states[i+1]))
{
    var tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> :|
                        |tds_states| >= 2 && 
                        (forall tds_state2 :: tds_state2 in tds_states 
                            ==> TDsStateGetTDIDs(tds_state2) == 
                                k_params.all_active_tds) &&
                        |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
                        tds_states[|tds_states| - 1] == to_tds_state && // last TDs' state is the <to_tds_state>
                        tds_states[0] == from_tds_state && // first TDs' state is the <from_tds_state>
                        (forall i :: 0<=i<|tds_states| - 1 
                            ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params, devs[i], tds_states[i], tds_states[i+1]) &&
                                IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs[i], tds_states[i], tds_states[i+1]));

    return tds_states, devs;
}

// [NOTE] Needs 80s to verify
lemma Lemma_K_AllReachableActiveTDsStates_Prove(k:State, tds_state:TDs_Vals, active_devs:set<Dev_ID>)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)

    requires active_devs <= AllActiveDevs(k)

    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs_SlimState(k.objects) &&
                    (ActiveTDsState(k) == tds_state || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(KToKParams(k), 
                                active_devs, ActiveTDsState(k), tds_state) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k), 
                                active_devs, ActiveTDsState(k), tds_state)))

    ensures tds_state in AllReachableActiveTDsStates(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_AllReachableActiveTDsStates_Apply(k:State, tds_state:TDs_Vals)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)

    requires tds_state in AllReachableActiveTDsStates(k)

    ensures IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(KToKParams(k), AllActiveDevs(k), ActiveTDsState(k), tds_state)
    ensures tds_state == ActiveTDsState(k) || IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k), AllActiveDevs(k), ActiveTDsState(k), tds_state)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_IfTDsStateCanBeReachedViaSmallSetOfActiveDevs_ThenCanBeReachedViaLargeSetToo(
    k_params:ReachableTDsKParams, 
    small_active_devs:set<Dev_ID>, large_active_devs:set<Dev_ID>, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(
                    k_params, large_active_devs, from_tds_state, to_tds_state)
    requires small_active_devs <= large_active_devs

    requires IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                    small_active_devs, from_tds_state, to_tds_state)

    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                    large_active_devs, from_tds_state, to_tds_state)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_ActiveTDsStateIsSecure_ThenIsValidState_ReachableTDsStatesAndSI1ReturnsTrue(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)

    requires forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2)

    ensures IsValidState_ReachableTDsStates(k)
    ensures IsSecureState_SI1(k)
{
    forall tds_state2 | tds_state2 in AllReachableActiveTDsStates(k)
        ensures (forall td_id2, dev_id :: dev_id in AllActiveDevs(k) && 
                    // The device (<dev_id>) is active
                td_id2 in TDsStateGetTDIDs(tds_state2) &&
                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                    // The TD is read by the device
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2))
    {
        assert ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2);
    }

    Lemma_AllReachableActiveTDsStates_ActiveTDsStateIsSecure_Property(k);
}

lemma Lemma_K_CanActiveDevReadActiveTD_Prove(
    k_params:ReachableTDsKParams,
    tds:map<TD_ID, TD_Val>, dev_id:Dev_ID, td_id:TD_ID
)
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds, dev_id, td_id)

    requires (exists td_ids:seq<TD_ID> :: |td_ids| >= 1 && 
                     (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds) &&
                                                      // A list of active TDs
                     td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
                     td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                     (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]])))

    ensures CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id)
{
    // Dafny can automatically prove this lemma
}

predicate P_Lemma_K_OneRefsTheOtherOneWithRInTDIDs(tds_state:TDs_Vals, td_ids:seq<TD_ID>)
{
    (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i] in tds_state) &&
    (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]]))
}

predicate P_Lemma_K_OneRefsTheOtherOneWithRInTDIDs_FromHCodedTDToTD(
    k_params:ReachableTDsKParams,
    tds:map<TD_ID, TD_Val>, td_ids:seq<TD_ID>, dev_id:Dev_ID, td_id:TD_ID
)
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds, dev_id, td_id)
{
    (|td_ids| >= 1) &&
    ((forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds)) &&
                                                      // A list of active TDs
    (td_ids[|td_ids| - 1] == td_id) && // last TD is the TD (<td_id>)
    (td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id) &&
                                            // first TD must be the hardcoded TD
    (P_Lemma_K_OneRefsTheOtherOneWithRInTDIDs(tds, td_ids)) &&
    
    (true)
}

lemma Lemma_K_CanActiveDevReadActiveTD_Prove2(
    k_params:ReachableTDsKParams,
    tds:map<TD_ID, TD_Val>, td_ids:seq<TD_ID>, dev_id:Dev_ID, td_id:TD_ID
)
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds, dev_id, td_id)
    requires P_Lemma_K_OneRefsTheOtherOneWithRInTDIDs_FromHCodedTDToTD(k_params, tds, td_ids, dev_id, td_id)

    ensures CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_DevAModesToObj_Property(
    k:State, tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID 
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                 ==> (drv_sid != dev_sid)
        // Requirement: Subjects have different internal IDs
    requires forall td_id, fd_id :: TD_ID(td_id) in AllTDIDs(k.objects) && FD_ID(fd_id) in AllFDIDs(k.objects)
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in AllTDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in AllFDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> fd_id != do_id 
        // Requirements: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are TDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)
    // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds) == AllActiveTDs(k)

    requires IsDevID(k, dev_id)
    requires SubjPID(k, dev_id.sid) != NULL
    // Requirement: The device is active

    ensures R in DevAModesToObj(k, tds, dev_id, o_id) 
                ==> DevAModesToObjFromTDs_ExistR_SlimState(KToKParams(k), tds, dev_id, o_id)
    ensures W in DevAModesToObj(k, tds, dev_id, o_id) 
                ==> DevAModesToObjFromTDs_ExistW_SlimState(KToKParams(k), tds, dev_id, o_id)
    ensures DevAModesToObj(k, tds, dev_id, o_id) != {}
                ==> (exists td_id :: td_id in tds && 
                                CanActiveDevReadActiveTD(KToKParams(k), tds, dev_id, td_id) &&
                                o_id in GetObjIDsRefedInTD(tds, td_id) &&
                                GetAModesOfObjRefedInTD(tds, td_id, o_id) != {})
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_DevAModesToObj_NonEmpty_Prove(
    k:State, tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID, td_id:TD_ID
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                 ==> (drv_sid != dev_sid)
        // Requirement: Subjects have different internal IDs
    requires forall td_id, fd_id :: TD_ID(td_id) in AllTDIDs(k.objects) && FD_ID(fd_id) in AllFDIDs(k.objects)
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in AllTDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in AllFDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> fd_id != do_id 
        // Requirements: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are TDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)
    // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds) == AllActiveTDs(k)

    requires IsDevID(k, dev_id)
    requires SubjPID(k, dev_id.sid) != NULL
    // Requirement: The device is active
    
    requires td_id in tds && 
                CanActiveDevReadActiveTD(KToKParams(k), tds, dev_id, td_id) &&
                o_id in GetObjIDsRefedInTD(tds, td_id) &&
                GetAModesOfObjRefedInTD(tds, td_id, o_id) != {}

    ensures DevAModesToObj(k, tds, dev_id, o_id) != {}
{
    AllReqNonEmptyAModesMustContainROrW();
    assert R in GetAModesOfObjRefedInTD(tds, td_id, o_id) || W in GetAModesOfObjRefedInTD(tds, td_id, o_id);
}

lemma Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_EmptyTDProperty(
    k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, td_id:TD_ID
)
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
        // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state
        // Requirement: The TD (<td_id>) is active

    requires tds_state[td_id] == TD_Val(map[], map[], map[])

    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id)
{
    // Dafny can automatically prove this lemma
}

predicate P_CanActiveDevReadActiveTD_Def(
    k_params:ReachableTDsKParams, tds_state:TDs_Vals, dev_id:Dev_ID, 
    td_ids:seq<TD_ID>, target_td_id:TD_ID
)
    requires dev_id in k_params.subjects.devs
{
    |td_ids| >= 1 && 
    (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds_state) &&
                                    // A list of active TDs
    td_ids[|td_ids| - 1] == target_td_id && // last TD is the target TD (<target_td_id>)
    td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                    // first TD must be the hardcoded TD
    (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]]))
}

lemma Lemma_DM_CanActiveDevReadActiveTD_Apply(
    k_params:ReachableTDsKParams,
    tds:map<TD_ID, TD_Val>, dev_id:Dev_ID, td_id:TD_ID
) returns (td_ids:seq<TD_ID>)
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds, dev_id, td_id)
    requires CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id)

    ensures |td_ids| >= 1 && 
                     (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds) &&
                                                      // A list of active TDs
                     td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
                     td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                     (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]]))
    ensures P_CanActiveDevReadActiveTD_Def(k_params, tds, dev_id, td_ids, td_id)
{
    var result_td_ids:seq<TD_ID> :| |result_td_ids| >= 1 && 
                     (forall td_id2 :: td_id2 in result_td_ids ==> td_id2 in tds) &&
                                                      // A list of active TDs
                     result_td_ids[|result_td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
                     result_td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                     (forall i :: 0<=i<|result_td_ids| - 1 ==> result_td_ids[i+1] in TDIDReadsInTDCfg(tds[result_td_ids[i]]));
    return result_td_ids;
}

lemma Lemma_K_IfActiveDevReadsTDIndirectly_ThenDevCanReadTDX(
    k:State, k_params:ReachableTDsKParams, tds:map<TD_ID, TD_Val>, td_ids:seq<TD_ID>, dev_id:Dev_ID, td_id:TD_ID
) returns (tdx_id:TD_ID)
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
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds, dev_id, td_id)

    requires |td_ids| > 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]]))
                                            // previous TD always refs the current TD with R access mode

    ensures tdx_id in AllActiveTDs(k) &&
            CanActiveDevReadActiveTD(k_params, tds, dev_id, tdx_id) &&
            td_id in tds[tdx_id].trans_params_tds &&
            R in tds[tdx_id].trans_params_tds[td_id].amodes
                // The TD references the target TD (<td_id>) with R
{
    var tdx_idx := |td_ids|-2;
    var t_tdx_id := td_ids[tdx_idx];

    // Prove CanActiveDevReadActiveTD(k_params, tds, dev_id, tdx_id)
    Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(k_params, tds, dev_id, td_ids, td_id);
    
    // Prove td_id in TDIDReadsInTDCfg(tds[t_tdx_id])
    assert td_id in TDIDReadsInTDCfg(tds[t_tdx_id]);

    // Prove t_tdx_id in tds;
    assert forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds;
    assert t_tdx_id in tds;

    assert td_id in tds[t_tdx_id].trans_params_tds;
    assert R in tds[t_tdx_id].trans_params_tds[td_id].amodes;

    return t_tdx_id;
}

lemma Lemma_K_DevAModesToObjFromTDs_ExistR_SlimState_ProveDevAModesToObj_SlimState(
    k:State, dev_id:Dev_ID, o_id:Object_ID
)
    requires IsValidState(k)
    requires DevAModesToObj_SlimState_PreConditions(KToKParams(k), ActiveTDsState(k), dev_id, o_id)
    requires DevAModesToObjFromTDs_ExistR_SlimState(KToKParams(k), ActiveTDsState(k), dev_id, o_id)

    ensures R in DevAModesToObj(k, ActiveTDsState(k), dev_id, o_id)
{
    var k_params := KToKParams(k);
    var k_tds_state := ActiveTDsState(k);

    var t_slim := DevAModesToObj_SlimState(k_params, k_tds_state, dev_id, o_id);
    var t := DevAModesToObj(k, ActiveTDsState(k), dev_id, o_id);

    assert R in t_slim;
    assert t == t_slim;
}




//******** Read/Write ********//
lemma Lemma_WriteActiveNonHCodedTDsVals_ProveIsValidState_Objects_UniqueObjIDs(k_objs:Objects, td_id_val_map:map<TD_ID, TD_Val>)
    requires IsValidState_Objects_UniqueObjIDs(k_objs)

    requires forall td_id :: td_id in td_id_val_map ==> td_id in k_objs.active_non_hcoded_tds
    requires var t_objs1 := WriteActiveNonHCodedTDsVals(k_objs, td_id_val_map);
             IsValidState_Objects_UniqueObjIDs(t_objs1)

    ensures var t_objs1 := WriteActiveNonHCodedTDsVals(k_objs, td_id_val_map);
            AllActiveTDs_SlimState(t_objs1) == AllActiveTDs_SlimState(k_objs)
{
    var t_objs1 := WriteActiveNonHCodedTDsVals(k_objs, td_id_val_map);

    forall td_id | td_id in AllTDIDs(k_objs)
        ensures ObjPID_KObjects(k_objs, td_id.oid) == ObjPID_KObjects(t_objs1, td_id.oid)
    {
        reveal IsValidState_Objects_UniqueObjIDs();
    }
}




//******** Others ********//
lemma Lemma_K_TDIDReadsInTDCfg_TDMustInTransParamsTDs(
    tds_state:TDs_Vals, td_id:TD_ID, target_td_id:TD_ID
)
    requires td_id in tds_state
    requires target_td_id in TDIDReadsInTDCfg(tds_state[td_id])

    ensures target_td_id in MapGetKeys(tds_state[td_id].trans_params_tds)
    ensures tds_state[td_id].trans_params_tds[target_td_id].amodes != {}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_DifferentTDsState_MustIncludeOneTDWithDifferentVals(tds_state1:TDs_Vals, tds_state2:TDs_Vals)
    requires TDsStateGetTDIDs(tds_state1) == TDsStateGetTDIDs(tds_state2)

    requires tds_state1 != tds_state2

    ensures exists td_id :: td_id in tds_state1 && tds_state1[td_id] != tds_state2[td_id]
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_DevSubjPIDEqualsToSubjDevPID(k_subjects:Subjects)
    requires forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
                 ==> (drv_sid != dev_sid)

    ensures forall dev_id :: IsDevID_SlimState(k_subjects, dev_id)
                ==> SubjPID_DevID_SlimState(k_subjects, dev_id) == SubjPID_SlimState(k_subjects, dev_id.sid)
{
    forall dev_id | IsDevID_SlimState(k_subjects, dev_id)
        ensures SubjPID_DevID_SlimState(k_subjects, dev_id) == SubjPID_SlimState(k_subjects, dev_id.sid)
    {
        assert dev_id in k_subjects.devs;

        assert SubjPID_SlimState(k_subjects, dev_id.sid) == k_subjects.devs[dev_id].pid;
    }
}

lemma Lemma_K_ValidAndSecureState_ThenActiveTDsStateIsSecureIsTrue(k:State)
    requires IsValidState(k) && IsSecureState(k)

    ensures ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), ActiveTDsState(k))
{
    // Dafny can automatically prove this lemma
}

// Prove ActiveTDsStateIsSecure
lemma Lemma_K_ActiveTDsStateIsSecure_Prove(
    k_params:ReachableTDsKParams,
    active_devs:set<Dev_ID>, tds_state:TDs_Vals
)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds

    requires forall td_id2, dev_id :: 
                    dev_id in active_devs && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                        // The TD is read by the device
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)

    ensures ActiveTDsStateIsSecure(k_params, active_devs, tds_state)
{
    // Dafny can automatically prove this lemma
}

// Lemma: If a device's hardcoded TD do not have any transfers to TDs, then the
// device can only read its hardcoded TD
lemma Lemma_K_CanActiveDevReadActiveTD_DevWithoutHCodedTransToTDsCanOnlyReadItsHCodedTD(
    k:State, k_tds_state:TDs_Vals, dev_id:Dev_ID, td_id:TD_ID
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)

    requires CanActiveDevReadActiveTD_PreConditions(KToKParams(k), k_tds_state, dev_id, td_id)
    requires CanActiveDevReadActiveTD(KToKParams(k), k_tds_state, dev_id, td_id)

    requires k.subjects.devs[dev_id].hcoded_td_id in k_tds_state
    requires k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val == k_tds_state[k.subjects.devs[dev_id].hcoded_td_id]
        // Requirement: Hardcoded TD of the device is not changed between <k.objects.tds> and <k_tds_state>
    requires MapGetKeys(k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val.trans_params_tds) == {}

    ensures td_id == k.subjects.devs[dev_id].hcoded_td_id
{
    var k_params := KToKParams(k);

    if(td_id != k.subjects.devs[dev_id].hcoded_td_id)
    {
        var td_ids:seq<TD_ID> :| |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in k_tds_state) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k_tds_state[td_ids[i]]));

        assert |td_ids| > 1;
        assert td_ids[1] in k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val.trans_params_tds;
        assert MapGetKeys(k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val.trans_params_tds) != {};
    }
}

lemma Lemma_K_IsTDRefTDWithAModes_Prove(
    tds_state:TDs_Vals, td_id:TD_ID, target_td_id:TD_ID
)
    requires td_id in tds_state
    requires target_td_id in tds_state[td_id].trans_params_tds
    requires W in tds_state[td_id].trans_params_tds[target_td_id].amodes

    ensures IsTDRefTDWithAModes(tds_state, td_id, target_td_id, {W})
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_IsTDRefTDWithAModes_IfAllTransParamsTDsIsR_ThenReqToWReturnsFalse(
    tds_state:TDs_Vals, td_id:TD_ID, target_td_id:TD_ID
)
    requires td_id in tds_state
    requires forall td_id2 :: td_id2 in tds_state[td_id].trans_params_tds &&
                    tds_state[td_id].trans_params_tds[td_id2].amodes != {}
                ==> tds_state[td_id].trans_params_tds[td_id2].amodes == {R}

    ensures !IsTDRefTDWithAModes(tds_state, td_id, target_td_id, {W})
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_IsTDRefTDWithAModes_IfRefsNoTDs_ThenReqToWReturnsFalse(
    tds_state:TDs_Vals, td_id:TD_ID, target_td_id:TD_ID
)
    requires td_id in tds_state
    requires MapGetKeys(tds_state[td_id].trans_params_tds) == {}

    ensures !IsTDRefTDWithAModes(tds_state, td_id, target_td_id, {W})
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_IfTranfersToTDsAreReadOnly_ThenTranfersToTDsAreReadOnly(
    trans_params_tds:map<TD_ID, TD_Trans_Param>, td_id:TD_ID
)
    requires trans_params_tds == map[td_id := TD_Trans_Param({R}, {})]

    ensures forall td_id :: td_id in trans_params_tds &&
                    trans_params_tds[td_id].amodes != {}
                ==> trans_params_tds[td_id].amodes == {R}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_KToKParams_HCodedTDIDsIsAllHCodedTDIDs(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)

    ensures AllHCodedTDIDs(k.subjects) == KToKParams(k).hcoded_td_ids
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_CanActiveDevReadActiveTD_KParams_PreConditions_Prove(k:State, k_params:ReachableTDsKParams)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    ensures CanActiveDevReadActiveTD_KParams_PreConditions(KToKParams(k))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_ActiveTDsStateIsSecure_Property_MergeOfTwo_ProveAllPreConditions(
    k:State, k_params:ReachableTDsKParams, active_devs1:set<Dev_ID>, active_devs2:set<Dev_ID>, tds_state:TDs_Vals
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires k_params == KToKParams(k)

    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)

    requires AllActiveDevs(k) == active_devs1 + active_devs2

    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    ensures forall dev_id2 :: dev_id2 in active_devs1
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
    ensures forall dev_id2 :: dev_id2 in active_devs2
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Property: The devices in <active_devs1>, <active_devs2> must be active
    ensures TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_ActiveTDsStateIsSecure_Property_MergeOfTwo(
    k:State, k_params:ReachableTDsKParams, active_devs1:set<Dev_ID>, active_devs2:set<Dev_ID>, tds_state:TDs_Vals
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) 
    requires k_params == KToKParams(k)

    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)

    requires AllActiveDevs(k) == active_devs1 + active_devs2
    requires ActiveTDsStateIsSecure(k_params, active_devs1, tds_state)
    requires ActiveTDsStateIsSecure(k_params, active_devs2, tds_state)

    ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_ActiveTDsState_AllActiveTDs(k:State, tds_state:TDs_Vals)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)

    ensures forall td_id :: td_id in tds_state
                ==> td_id in ActiveTDsState(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_ProveIsValidState_SubjsOwnObjsThenInSamePartition(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && 
            IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
                ==> o_id in AllObjsIDs(k.objects) &&
                    SubjPID(k, s_id) == ObjPID(k, o_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_ValidState_Drv_Property(k:State, drv_id:Drv_ID)
    requires IsValidState(k)
    
    requires drv_id in k.subjects.drvs
    
    ensures k.subjects.drvs[drv_id].td_ids <= AllTDIDs(k.objects)
    ensures k.subjects.drvs[drv_id].fd_ids <= AllFDIDs(k.objects)
    ensures k.subjects.drvs[drv_id].do_ids <= AllDOIDs(k.objects)
{
    assert (forall drv_id, td_id :: 
        drv_id in k.subjects.drvs && td_id in k.subjects.drvs[drv_id].td_ids
        ==> td_id in AllTDIDs(k.objects));
}

lemma Lemma_K_ValidState_Dev_Property(k:State, dev_id:Dev_ID)
    requires IsValidState(k)
    
    requires dev_id in k.subjects.devs
    
    ensures k.subjects.devs[dev_id].td_ids <= AllTDIDs(k.objects)
    ensures k.subjects.devs[dev_id].fd_ids <= AllFDIDs(k.objects)
    ensures k.subjects.devs[dev_id].do_ids <= AllDOIDs(k.objects)
{
    assert (forall dev_id, td_id :: 
        dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
        ==> td_id in AllTDIDs(k.objects));
}

lemma Lemma_K_ActiveTDsAreInActiveTDsState(k:State, td_id1:TD_ID, td_id2:TD_ID, td_ids:seq<TD_ID>)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires td_id1 in AllTDIDs(k.objects)
    requires td_id2 in AllTDIDs(k.objects)

    requires ObjPID(k, td_id1.oid) != NULL
    requires ObjPID(k, td_id2.oid) != NULL
    requires td_ids == [td_id1, td_id2]

    ensures forall td_id2 :: td_id2 in td_ids ==> td_id2 in ActiveTDsState(k)
    ensures forall i :: 0<=i<|td_ids| ==> td_ids[i] in ActiveTDsState(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_DevWrite_WriteTDWithValMustBeInATransfer_Apply(
    k:State, dev_sid:Subject_ID, target_td_id:TD_ID, write_val:TD_Val
) returns (td_id:TD_ID)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
        
    requires DevWrite_WriteTDWithValMustBeInATransfer(k, dev_sid, target_td_id, write_val)
    
    ensures td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_td_id in GetTDVal(k, td_id).trans_params_tds &&
                    W in GetTDVal(k, td_id).trans_params_tds[target_td_id].amodes &&
                        // The TD references the target TD (<target_td_id>) with W
                    write_val in GetTDVal(k, td_id).trans_params_tds[target_td_id].vals
{
    td_id :| td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_td_id in GetTDVal(k, td_id).trans_params_tds &&
                    W in GetTDVal(k, td_id).trans_params_tds[target_td_id].amodes &&
                        // The TD references the target TD (<target_td_id>) with W
                    write_val in GetTDVal(k, td_id).trans_params_tds[target_td_id].vals;
}

lemma Lemma_K_SubjAndItsObjHasSamePID(k:State, s_id:Subject_ID, o_id:Object_ID, pid:Partition_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires IsValidState(k)
    requires IsSubjID(k.subjects, s_id)
    requires SubjPID(k, s_id) == pid
    requires o_id in OwnObjIDs(k, s_id)
    
    ensures ObjPID(k, o_id) == pid
{
    assert s_id in AllSubjsIDs(k.subjects);

    // Prove DoOwnObj(k, s_id, o_id)
    Lemma_OwnObjIDs_Property(k, s_id);
    assert DoOwnObj(k, s_id, o_id);
    assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
}

lemma Lemma_K_AllActiveObjs_Prove(k:State, o_id:Object_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires forall td_id, fd_id :: TD_ID(td_id) in AllTDIDs(k.objects) && FD_ID(fd_id) in AllFDIDs(k.objects)
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in AllTDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in AllFDIDs(k.objects) && DO_ID(do_id) in AllDOIDs(k.objects)
                ==> fd_id != do_id
                
    requires o_id in AllObjsIDs(k.objects)
    requires ObjPID(k, o_id) != NULL
    
    ensures o_id in AllActiveObjs(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_GetObjIDsRefedInTD_Equal(tds_state1:TDs_Vals, tds_state2:TDs_Vals, td_id:TD_ID)
    requires td_id in tds_state1 && td_id in tds_state2
    requires tds_state1[td_id] == tds_state2[td_id]
    
    ensures GetObjIDsRefedInTD(tds_state1, td_id) == GetObjIDsRefedInTD(tds_state2, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_GetAModesOfObjRefedInTD_Equal(tds_state1:TDs_Vals, tds_state2:TDs_Vals, td_id:TD_ID, o_id:Object_ID)
    requires td_id in tds_state1 && td_id in tds_state2
    requires tds_state1[td_id] == tds_state2[td_id]
    requires GetObjIDsRefedInTD(tds_state1, td_id) == GetObjIDsRefedInTD(tds_state2, td_id)
    requires o_id in GetObjIDsRefedInTD(tds_state1, td_id)
    
    ensures GetAModesOfObjRefedInTD(tds_state1, td_id, o_id) == GetAModesOfObjRefedInTD(tds_state2, td_id, o_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_P_ObjsInSubjsAreAlsoInState_Prove(k:State)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    ensures P_ObjsInSubjsAreAlsoInState(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_AllActiveTDs_SlimState_Property(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)

    ensures forall td_id2 :: td_id2 in AllActiveTDs_SlimState(k.objects)
                ==> td_id2.oid in AllObjsIDs(k.objects) &&
                    ObjPID(k, td_id2.oid) != NULL
{
    var k_params := KToKParams(k);
    forall td_id2 | td_id2 in AllActiveTDs_SlimState(k.objects)
        ensures td_id2.oid in AllObjsIDs(k.objects)
        ensures ObjPID(k, td_id2.oid) != NULL
    {
        assert td_id2 in AllTDIDs(k.objects);
        assert ObjPID_KObjects(k.objects, td_id2.oid) != NULL;

        assert k_params.objs_pids[td_id2.oid] == ObjPID_KObjects(k.objects, td_id2.oid);
        assert ObjPID(k, td_id2.oid) == ObjPID_KObjects(k.objects, td_id2.oid);
    }
}

lemma Lemma_K_AllActiveSubjs_SlimState_Property(k_subjects:Subjects)
    ensures forall s_id :: s_id in AllActiveSubjs_SlimState(k_subjects)
                ==> IsSubjID(k_subjects, s_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID_Subjects(k_subjects:Subjects)
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
                 ==> (drv_sid != dev_sid)

    ensures forall dev_id :: IsDevID_SlimState(k_subjects, dev_id)
                ==> SubjPID_DevID_SlimState(k_subjects, dev_id) == SubjPID_SlimState(k_subjects, dev_id.sid)
{
    forall dev_id | IsDevID_SlimState(k_subjects, dev_id)
        ensures SubjPID_DevID_SlimState(k_subjects, dev_id) == SubjPID_SlimState(k_subjects, dev_id.sid)
    {
        Lemma_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(k_subjects, dev_id);
    }
}

lemma Lemma_K_IfSubjOwnHCodedTD_ThenSubjOwnRefedTDs(k:State, s_id:Subject_ID, hcoded_td_id:TD_ID, td_id2:TD_ID)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires IsSubjID(k.subjects, s_id)
    requires hcoded_td_id in AllHCodedTDIDs(k.subjects)
    requires hcoded_td_id in k.objects.hcoded_tds
    requires td_id2 in k.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
    requires DoOwnObj(k, s_id, hcoded_td_id.oid)

    ensures DoOwnObj(k, s_id, td_id2.oid)
    ensures td_id2 in OwnedTDs(k, s_id)
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var k_params := KToKParams(k);
    var dev_id := Lemma_K_HCodedTDGetOwnerDev(k, hcoded_td_id);

    assert Dev_ID(s_id) == dev_id;

    Lemma_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(k);
}

lemma Lemma_K_IfSubjOwnHCodedTD_ThenSubjOwnRefedFDs(k:State, s_id:Subject_ID, hcoded_td_id:TD_ID, fd_id2:FD_ID)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires IsSubjID(k.subjects, s_id)
    requires hcoded_td_id in AllHCodedTDIDs(k.subjects)
    requires hcoded_td_id in k.objects.hcoded_tds
    requires fd_id2 in k.objects.hcoded_tds[hcoded_td_id].val.trans_params_fds
    requires DoOwnObj(k, s_id, hcoded_td_id.oid)

    ensures DoOwnObj(k, s_id, fd_id2.oid)
    ensures fd_id2 in OwnedFDs(k, s_id)
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var k_params := KToKParams(k);
    var dev_id := Lemma_K_HCodedTDGetOwnerDev(k, hcoded_td_id);

    assert Dev_ID(s_id) == dev_id;

    Lemma_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(k);
}

lemma Lemma_K_IfSubjOwnHCodedTD_ThenSubjOwnRefedDOs(k:State, s_id:Subject_ID, hcoded_td_id:TD_ID, do_id2:DO_ID)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires IsSubjID(k.subjects, s_id)
    requires hcoded_td_id in AllHCodedTDIDs(k.subjects)
    requires hcoded_td_id in k.objects.hcoded_tds
    requires do_id2 in k.objects.hcoded_tds[hcoded_td_id].val.trans_params_dos
    requires DoOwnObj(k, s_id, hcoded_td_id.oid)

    ensures DoOwnObj(k, s_id, do_id2.oid)
    ensures do_id2 in OwnedDOs(k, s_id)
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var k_params := KToKParams(k);
    var dev_id := Lemma_K_HCodedTDGetOwnerDev(k, hcoded_td_id);

    assert Dev_ID(s_id) == dev_id;

    Lemma_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(k);
}

lemma Lemma_K_IntersectionOfDevTDIDsAndHCodedTDIDsIsHCodedTDOfDev(k:State, dev_id:Dev_ID)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires dev_id in k.subjects.devs

    ensures forall td_id :: td_id in AllHCodedTDIDs(k.subjects) &&
                    td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id == k.subjects.devs[dev_id].hcoded_td_id
{
    if(exists td_id :: td_id in AllHCodedTDIDs(k.subjects) &&
                    td_id in k.subjects.devs[dev_id].td_ids &&
                 td_id != k.subjects.devs[dev_id].hcoded_td_id)
    {
        var td_id :| td_id in AllHCodedTDIDs(k.subjects) &&
                    td_id in k.subjects.devs[dev_id].td_ids &&
                 td_id != k.subjects.devs[dev_id].hcoded_td_id;

        assert td_id in AllHCodedTDIDs(k.subjects);
        assert exists dev_id :: dev_id in k.subjects.devs &&
                      td_id == k.subjects.devs[dev_id].hcoded_td_id;
        var dev_id1 :| dev_id1 in k.subjects.devs &&
                      td_id == k.subjects.devs[dev_id1].hcoded_td_id;
        assert DoOwnObj(k, dev_id1.sid, td_id.oid);

        assert td_id in k.subjects.devs[dev_id].td_ids &&
                td_id != k.subjects.devs[dev_id].hcoded_td_id;
        assert DoOwnObj(k, dev_id.sid, td_id.oid);
        assert dev_id != dev_id1;
        
        assert (forall o_id, s_id1, s_id2 :: 
            s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
            DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
            ==> s_id1 == s_id2);

        assert false;
    }
}

lemma Lemma_K_GetObjIDsRefedInTD_NotIn(k_tds_state:TDs_Vals, td_id:TD_ID, o_id:Object_ID)
    requires td_id in k_tds_state
    requires TD_ID(o_id) !in k_tds_state[td_id].trans_params_tds
    requires FD_ID(o_id) !in k_tds_state[td_id].trans_params_fds
    requires DO_ID(o_id) !in k_tds_state[td_id].trans_params_dos

    ensures o_id !in GetObjIDsRefedInTD(k_tds_state, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_SecureActiveTDsState_IfDevHasReadTransferToTD_ThenAllIntermediateTDsAreInSamePartitionWithDev(
    k:State, k_params:ReachableTDsKParams, k_tds_state:TDs_Vals, dev_id:Dev_ID, 
    td_ids:seq<TD_ID>, target_td_id:TD_ID
)
    requires IsValidState(k)

    requires k_params == KToKParams(k)
    requires k_tds_state == ActiveTDsState(k)
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state)

    requires dev_id in k_params.subjects.devs
    requires SubjPID_DevID(k, dev_id) != NULL
    requires P_CanActiveDevReadActiveTD_Def(k_params, k_tds_state, dev_id, td_ids, target_td_id)

    ensures forall td_id :: td_id in td_ids
                ==> ObjPID(k, td_id.oid) == SubjPID(k, dev_id.sid)
{
    Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(k_params, k_tds_state, dev_id, td_ids, target_td_id);
    forall td_id2 | td_id2 in td_ids
        ensures ObjPID(k, td_id2.oid) == SubjPID(k, dev_id.sid)
    {
        assert CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2);
        Lemma_SecureActiveTDsState_TDsReadByActiveDevAreInSamePartitionWithDev_ForSubsetOfActiveDevs(
            k, k_params, AllActiveDevs(k), k_tds_state, dev_id, td_id2);
    }
}

lemma Lemma_ValidK_ActiveTDsHaveNonNullPIDs(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && 
            IsValidState_Partitions(k)

    ensures forall tds_state2, td_id2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k.objects) &&
            td_id2 in TDsStateGetTDIDs(tds_state2)
        ==> td_id2 in AllTDIDs(k.objects) &&
            ObjPID_KObjects(k.objects, td_id2.oid) != NULL;
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ValidK_FulFills_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && 
            IsValidState_Partitions(k)

    ensures DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(KToKParams(k));
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_DevActivate_ModificationToState_Properties(k:State, dev_sid:Subject_ID, pid:Partition_ID, k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires pid != NULL

    requires forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].td_ids && 
                    id != k.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].fd_ids ==> id in k.objects.inactive_fds
    requires forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].do_ids ==> id in k.objects.inactive_dos
    requires k.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id in k.objects.hcoded_tds

    requires P_DevActivate_ModificationToState(k, dev_sid, pid, k')

    ensures forall id :: id in k.subjects.devs
                ==> k'.subjects.devs[id].hcoded_td_id == k.subjects.devs[id].hcoded_td_id
{
    // Dafny can automatically prove this lemma
}