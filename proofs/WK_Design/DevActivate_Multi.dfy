include "Utils.i.dfy"

predicate P_WSD_DevActivate_Multi_SubjObjModifications(
    ws:DM_State, ws':DM_State,
    dev_ids:set<Dev_ID>, // ID of the devices to be activated
    pid:Partition_ID // ID of the target partition
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires DM_IsValidState_Objects(ws)

    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
{
    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids);

    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids);

    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_ProvePreConditionForObjModifications(ws, dev_ids, pid);
    assert P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid);

    // Unchanged state vars
    ws'.pids == ws.pids &&
    ws'.tds_to_all_states == ws.tds_to_all_states &&
    ws'.red_pid == ws.red_pid &&
    ws'.devs_activatecond == ws.devs_activatecond &&
    ws'.subjects.drvs == ws.subjects.drvs &&

    // Modify subjects
    P_WSD_DevActivate_Multi_SubjObjModifications_Subjs(ws, ws', dev_ids, pid) &&

    // Modify objects
    P_WSD_DevActivate_Multi_SubjObjModifications_Objs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid) &&

    (true)
}

function method DevActivateMulti_ToTraceOps(dev_ids:seq<Dev_ID>, pid:Partition_ID) : (t:seq<DM_Op>)
    ensures |t| == |dev_ids|
    ensures forall i :: 0 <= i < |t| ==> t[i] == DM_DevActivateOp(dev_ids[i].sid, pid)
{
    if(|dev_ids| == 0) then
        []
    else
        [DM_DevActivateOp(dev_ids[0].sid, pid)] + DevActivateMulti_ToTraceOps(dev_ids[1..], pid)
}

// [NOTE] Needs 380s to verify
/*method {:timeLimitMultiplier 40} WSD_DevActivate_Multi(
    ws:DM_State,
    dev_ids:seq<Dev_ID>, // ID of the devices to be deactivated
    pid:Partition_ID // ID of the target partition
) returns (ghost t:DM_Trace, ghost t_detailed:DM_Trace_Detailed, last_ws:DM_State, d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires pid != NULL

    requires forall i, j :: 0 <= i < |dev_ids| && 0 <= j < |dev_ids|
                ==> (i == j <==> dev_ids[i] == dev_ids[j])
        // Requirement: No duplicate device ID in <dev_ids>
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    ensures d ==> t.ws0 == ws
    ensures d ==> |t.ops| == |dev_ids|
    ensures d ==> (forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_DevActivateOp(dev_ids[i].sid, pid))
    ensures d ==> t.ops == DevActivateMulti_ToTraceOps(dev_ids, pid)
        // Property 3
    ensures d ==> DM_IsValidTrace(t)
                
    ensures d ==> last_ws == SeqLastElem(DM_CalcNewStates(t))
        // Property 5: <last_ws> is the last state of the trace <t>

    ensures d ==> ConvertTraceToDetailedTrace(t) == (t_detailed, true)
    ensures d ==> DM_DetailedTrace_IsValidTrace(t_detailed)
        // Property 7
    ensures d ==> (forall i :: 0 <= i < |t_detailed.ops|
                    ==> DM_IsSecureOps(t_detailed.states[i], t_detailed.states[i+1]))
    ensures d ==> (last_ws == SeqLastElem(t_detailed.states))
    ensures d ==> DM_IsValidState(last_ws) && DM_IsSecureState(last_ws)
    ensures d ==> DM_IsSecureOps(ws, last_ws)
        // Properties from DM_IsSecureOps

    ensures d ==> P_WSD_DevActivate_Multi_SubjObjModifications(ws, last_ws, SeqToSet(dev_ids), pid)
        // Properties of devices activation
        // Property 11

    decreases |dev_ids|
{
    if(|dev_ids| == 0)
    {
        reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
        reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();
        Lemma_WSD_DevActivate_Multi_Prove_EmptyDevIDs(ws, dev_ids, pid);
        return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, true;
    }
    else
    {
        var dev_id := dev_ids[0];
        var ws', ws_d := DM_DevActivate(ws, dev_id.sid, pid);
        if(!ws_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}

        reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
        var next_dev_ids := dev_ids[1..];
        Lemma_WSD_DevActivate_Multi_DevIDsLargerThan1_ProveP_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', pid, dev_ids, next_dev_ids);
        Lemma_WSD_DevActivate_Multi_DevIDsLargerThan1_ProvePreConditionsForNextRun(ws, ws', pid, dev_ids, next_dev_ids);
        var next_t, detailed_next_t, next_last_ws, next_d := WSD_DevActivate_Multi(ws', next_dev_ids, pid); 
        if(!next_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}
        else
        {
            var op := DM_DevActivateOp(dev_id.sid, pid);

            t := DM_Trace(ws, [op] + next_t.ops);
            last_ws := next_last_ws;
            d := true;

            // Prove property 3
            Lemma_WSD_DevActivate_Multi_DevIDsLargerThan1_NextReturnTrue_ProveNumOfOpsAndDevIDs(t, next_t, op, dev_ids, next_dev_ids);
            Lemma_WSD_DevActivate_Multi_Private(next_t, next_dev_ids, op, t, dev_ids, pid);

            // Prove property 4
            ghost var result := ConvertTraceToDetailedTrace(next_t);
            assert detailed_next_t == result.0;
            ghost var status := result.1;

            assert status == true;

            t_detailed := DM_Trace_Detailed([ws] + detailed_next_t.states, [op] + detailed_next_t.ops);

            assert DM_CalcNewState(ws, op) == (ws', ws_d);
            Lemma_ValidDetailedTraceInsertValidStateAndChainedAtFirst(detailed_next_t, ws, op, t_detailed);
            assert DM_DetailedTrace_IsValidTrace(t_detailed);

            assert t == ConvertDetailedTraceToTrace(t_detailed);
            assert DM_IsValidTrace(t);

            // Prove property 5
            assert DM_CalcNewStates(t) == t_detailed.states;
            Lemma_Seq_LastElemIsUnchanged_IfInsertElemAtFirst(t_detailed.states, detailed_next_t.states, ws);
            assert SeqLastElem(t_detailed.states) == SeqLastElem(detailed_next_t.states);
            assert t_detailed.states[|t_detailed.states|-1] == SeqLastElem(DM_CalcNewStates(t));

            // Prove property 7
            assert DM_IsSecureOps(ws, ws');
            assert DM_IsSecureOps(ws', last_ws);
            Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps(ws, ws', last_ws, dev_ids, pid);
            Lemma_WSD_DevActivate_Multi_ProveConvertTraceToDetailedTrace_DevIDsNot0AndReturnTrue(ws, t, t_detailed, next_t, detailed_next_t, op);
            
            // Prove property 11
            Lemma_WSD_DevActivate_Multi_ProveProperty11(ws, ws', last_ws, dev_ids, pid);
        }
    }
} */




//******** Private Predicates for <P_WSD_DevActivate_Multi_SubjObjModifications> ********//
predicate {:opaque} P_WSD_DevActivate_Multi_SubjObjModifications_Subjs(
    ws:DM_State, ws':DM_State,
    dev_ids:set<Dev_ID>, // ID of the devices to be activated
    pid:Partition_ID // ID of the target partition
)
    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    ensures P_WSD_DevActivate_Multi_SubjObjModifications_Subjs(ws, ws', dev_ids, pid)
                ==> MapGetKeys(ws'.subjects.devs) == MapGetKeys(ws.subjects.devs)
{
    MapGetKeys(ws'.subjects.devs) == MapGetKeys(ws.subjects.devs) &&

    (forall id :: id in ws'.subjects.devs
        ==> (id in dev_ids ==> ws'.subjects.devs[id] == ws.subjects.devs[id].(pid := pid)) &&
            (id !in dev_ids ==> ws'.subjects.devs[id] == ws.subjects.devs[id])
    )
}

predicate {:opaque} P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(
    ws:DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>,
    pid:Partition_ID // ID of the target partition
)
{
    (P_DMSubjectsHasUniqueIDs(ws.subjects)) &&
    (P_DMObjectsHasUniqueIDs(ws.objects)) &&
    (DM_IsValidState_Objects(ws)) &&

    (pid != NULL) &&

    (dev_tds <= DM_AllTDIDs(ws.objects)) &&
    (dev_fds <= DM_AllFDIDs(ws.objects)) &&
    (dev_dos <= DM_AllDOIDs(ws.objects)) &&
    (dev_hcoded_td_ids <= dev_tds) &&
    (dev_hcoded_td_ids <= DM_AllHCodedTDIDs(ws.subjects)) &&
        // Requirement: <dev_tds/fds/dos/hcoded_tds> must exist in the system
    (forall id :: id in dev_tds &&
                    id !in dev_hcoded_td_ids
                ==> id !in DM_AllHCodedTDIDs(ws.subjects)) &&
        // Requirement: <dev_tds> do not contain any HCoded TDs other than <dev_hcoded_td_ids>

    (true)
}

predicate {:opaque} P_WSD_DevActivate_Multi_SubjObjModifications_Objs(
    ws:DM_State, ws':DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>,
    pid:Partition_ID // ID of the target partition
)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)

    ensures P_WSD_DevActivate_Multi_SubjObjModifications_Objs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
                ==> (DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects) &&
                    DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects) &&
                    DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects))
    ensures P_WSD_DevActivate_Multi_SubjObjModifications_Objs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
                ==> P_DMObjectsHasUniqueIDs(ws'.objects)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions();
    var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;

    // Move object IDs
    (MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds) + dev_non_hcoded_td_ids) &&
    (MapGetKeys(ws'.objects.active_fds) == MapGetKeys(ws.objects.active_fds) + dev_fds) &&
    (MapGetKeys(ws'.objects.active_dos) == MapGetKeys(ws.objects.active_dos) + dev_dos) &&
    (ws'.objects.inactive_non_hcoded_tds == ws.objects.inactive_non_hcoded_tds - dev_non_hcoded_td_ids) &&
    (ws'.objects.inactive_fds == ws.objects.inactive_fds - dev_fds) &&
    (ws'.objects.inactive_dos == ws.objects.inactive_dos - dev_dos) &&
    MapGetKeys(ws'.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds) &&

    // Objects to be activated are correctly modified
    (
        Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_ProveP_DMObjectsHasUniqueIDs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids);
        Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_ProveSameSetOfTDsFDsDOs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids);
        true
    ) &&
    (forall id :: id in dev_tds &&
            id !in dev_hcoded_td_ids
        ==> DM_ObjPID(ws'.objects, id.oid) == pid &&
            DM_IsTDClearVal(ws'.objects, id)
    ) &&
    (forall id :: id in dev_tds &&
            id in dev_hcoded_td_ids
        ==> DM_ObjPID(ws'.objects, id.oid) == pid &&
            ws'.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val
    ) &&
        // Only hardcoded TDs can be reused
    (forall id :: id in dev_fds
        ==> DM_ObjPID(ws'.objects, id.oid) == pid &&
            DM_IsFDClearVal(ws'.objects, id)
    ) &&
    (forall id :: id in dev_dos
        ==> DM_ObjPID(ws'.objects, id.oid) == pid &&
            DM_IsDOClearVal(ws'.objects, id)
    ) &&  
    
    // Objects not to be activated are unchanged
    (forall id :: id in DM_AllTDIDs(ws.objects) &&
            id !in dev_tds
        ==> DM_IsSameTD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in DM_AllFDIDs(ws.objects) &&
            id !in dev_fds
        ==> DM_IsSameFD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in DM_AllDOIDs(ws.objects) &&
            id !in dev_dos
        ==> DM_IsSameDO(ws'.objects, ws.objects, id)) &&

    (true)
}




//******** Private Lemmas for <P_WSD_DevActivate_Multi_SubjObjModifications> ********//
predicate {:opaque} P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1(
    ws:DM_State, ws':DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>,
    pid:Partition_ID // ID of the target partition
)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
    (MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds) + dev_non_hcoded_td_ids) &&
    (MapGetKeys(ws'.objects.active_fds) == MapGetKeys(ws.objects.active_fds) + dev_fds) &&
    (MapGetKeys(ws'.objects.active_dos) == MapGetKeys(ws.objects.active_dos) + dev_dos) &&
    (ws'.objects.inactive_non_hcoded_tds == ws.objects.inactive_non_hcoded_tds - dev_non_hcoded_td_ids) &&
    (ws'.objects.inactive_fds == ws.objects.inactive_fds - dev_fds) &&
    (ws'.objects.inactive_dos == ws.objects.inactive_dos - dev_dos) &&
    MapGetKeys(ws'.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds)
}

predicate {:opaque} P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part2(
    ws:DM_State, ws':DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>,
    pid:Partition_ID // ID of the target partition
)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1();
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_ProveP_DMObjectsHasUniqueIDs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids);
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_ProveSameSetOfTDsFDsDOs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids);

    (forall id :: id in dev_tds &&
            id !in dev_hcoded_td_ids
        ==> DM_ObjPID(ws'.objects, id.oid) == pid &&
            DM_IsTDClearVal(ws'.objects, id)
    ) &&
    (forall id :: id in dev_tds &&
            id in dev_hcoded_td_ids
        ==> DM_ObjPID(ws'.objects, id.oid) == pid &&
            ws'.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val
    ) &&
        // Only hardcoded TDs can be reused
    (forall id :: id in dev_fds
        ==> DM_ObjPID(ws'.objects, id.oid) == pid &&
            DM_IsFDClearVal(ws'.objects, id)
    ) &&
    (forall id :: id in dev_dos
        ==> DM_ObjPID(ws'.objects, id.oid) == pid &&
            DM_IsDOClearVal(ws'.objects, id)
    )
}

predicate {:opaque} P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part3(
    ws:DM_State, ws':DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>,
    pid:Partition_ID // ID of the target partition
)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1();
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_ProveP_DMObjectsHasUniqueIDs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids);
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_ProveSameSetOfTDsFDsDOs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids);

    (forall id :: id in DM_AllTDIDs(ws.objects) &&
            id !in dev_tds
        ==> DM_IsSameTD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in DM_AllFDIDs(ws.objects) &&
            id !in dev_fds
        ==> DM_IsSameFD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in DM_AllDOIDs(ws.objects) &&
            id !in dev_dos
        ==> DM_IsSameDO(ws'.objects, ws.objects, id))
}

lemma Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Subjs_Prove(
    ws:DM_State, ws':DM_State,
    dev_ids:set<Dev_ID>, // ID of the devices to be activated
    pid:Partition_ID // ID of the target partition
)
    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires MapGetKeys(ws'.subjects.devs) == MapGetKeys(ws.subjects.devs)
    requires forall id :: id in ws'.subjects.devs
                ==> (id in dev_ids ==> ws'.subjects.devs[id] == ws.subjects.devs[id].(pid := pid)) &&
                    (id !in dev_ids ==> ws'.subjects.devs[id] == ws.subjects.devs[id])

    ensures P_WSD_DevActivate_Multi_SubjObjModifications_Subjs(ws, ws', dev_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
}

lemma Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Prove(
    ws:DM_State, ws':DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>,
    pid:Partition_ID // ID of the target partition
)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)

    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part2(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part3(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)

    ensures P_WSD_DevActivate_Multi_SubjObjModifications_Objs(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part2();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part3();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();
}

lemma Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Apply(
    ws:DM_State, ws':DM_State,
    dev_ids:set<Dev_ID>, // ID of the devices to be activated
    pid:Partition_ID // ID of the target partition
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires DM_IsValidState_Objects(ws)

    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws, ws', dev_ids, pid)

    ensures forall id :: id in ws'.subjects.devs
                ==> (id !in dev_ids ==> ws'.subjects.devs[id] == ws.subjects.devs[id])
    ensures var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids);
            var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
            (MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds) + dev_non_hcoded_td_ids) &&
            MapGetKeys(ws'.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds)
    ensures var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids);
            (forall id :: id in dev_tds &&
                    id !in dev_hcoded_td_ids
                ==> id in ws'.objects.active_non_hcoded_tds &&
                    DM_ObjPID(ws'.objects, id.oid) == pid &&
                    DM_IsTDClearVal(ws'.objects, id)) &&
            (forall id :: id in dev_tds &&
                    id in dev_hcoded_td_ids
                ==> id in ws'.objects.hcoded_tds &&
                    DM_ObjPID(ws'.objects, id.oid) == pid &&
                    ws'.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val
            ) &&
            (forall id :: id in dev_fds
                ==> id in ws'.objects.active_fds &&
                    DM_ObjPID(ws'.objects, id.oid) == pid &&
                    DM_IsFDClearVal(ws'.objects, id)
            ) &&
            (forall id :: id in dev_dos
                ==> id in ws'.objects.active_dos &&
                    DM_ObjPID(ws'.objects, id.oid) == pid &&
                    DM_IsDOClearVal(ws'.objects, id)
            )
    ensures var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids);
            (forall id :: id in DM_AllTDIDs(ws.objects) &&
                    id !in dev_tds
                ==> DM_IsSameTD(ws'.objects, ws.objects, id)) &&
            (forall id :: id in DM_AllFDIDs(ws.objects) &&
                    id !in dev_fds
                ==> DM_IsSameFD(ws'.objects, ws.objects, id)) &&
            (forall id :: id in DM_AllDOIDs(ws.objects) &&
                    id !in dev_dos
                ==> DM_IsSameDO(ws'.objects, ws.objects, id))
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();
}

// Lemma: Prove P_DMObjectsHasUniqueIDs for P_WSD_DevActivate_Multi_SubjObjModifications_Objs
lemma Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_ProveP_DMObjectsHasUniqueIDs(
    ws:DM_State, ws':DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires DM_IsValidState_Objects(ws)

    requires dev_tds <= DM_AllTDIDs(ws.objects)
    requires dev_fds <= DM_AllFDIDs(ws.objects)
    requires dev_dos <= DM_AllDOIDs(ws.objects)
    requires dev_hcoded_td_ids <= dev_tds
    requires dev_hcoded_td_ids <= DM_AllHCodedTDIDs(ws.subjects)
        // Requirement: <dev_tds/fds/dos/hcoded_tds> must exist in the system
    requires forall id :: id in dev_tds &&
                    id !in dev_hcoded_td_ids
                ==> id !in DM_AllHCodedTDIDs(ws.subjects)
        // Requirement: <dev_tds> do not contain any HCoded TDs other than <dev_hcoded_td_ids>

    requires var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
            (MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds) + dev_non_hcoded_td_ids) &&
            (MapGetKeys(ws'.objects.active_fds) == MapGetKeys(ws.objects.active_fds) + dev_fds) &&
            (MapGetKeys(ws'.objects.active_dos) == MapGetKeys(ws.objects.active_dos) + dev_dos) &&
            (ws'.objects.inactive_non_hcoded_tds == ws.objects.inactive_non_hcoded_tds - dev_non_hcoded_td_ids) &&
            (ws'.objects.inactive_fds == ws.objects.inactive_fds - dev_fds) &&
            (ws'.objects.inactive_dos == ws.objects.inactive_dos - dev_dos) &&
            MapGetKeys(ws'.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds)

    ensures P_DMObjectsHasUniqueIDs(ws'.objects)
{
    reveal IsValidState_Objects_UniqueObjIDs();

    var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
    var objs := ws'.objects;

    assert forall id1, id2 :: id1 in DM_AllTDIDs(ws.objects) && id2 in DM_AllFDIDs(ws.objects)
                ==> id1.oid != id2.oid;

    forall id1 | id1 in objs.active_non_hcoded_tds
        ensures FD_ID(id1.oid) !in objs.active_fds &&
                DO_ID(id1.oid) !in objs.active_dos &&
                id1 !in objs.inactive_non_hcoded_tds &&
                FD_ID(id1.oid) !in objs.inactive_fds &&
                DO_ID(id1.oid) !in objs.inactive_dos &&
                id1 !in objs.hcoded_tds
                
    {
        assert id1 in ws.objects.active_non_hcoded_tds || id1 in dev_non_hcoded_td_ids;

        if(id1 in ws.objects.active_non_hcoded_tds)
        {
            assert id1 !in objs.hcoded_tds;
        }
        else
        {
            assert id1 in dev_tds;
            assert id1 !in dev_hcoded_td_ids;
            assert id1 !in DM_AllHCodedTDIDs(ws.subjects);

            assert MapGetKeys(objs.hcoded_tds) == DM_AllHCodedTDIDs(ws.subjects);
            assert id1 !in objs.hcoded_tds;
        }
    }

    forall id1 | id1 in objs.active_fds
        ensures DO_ID(id1.oid) !in objs.active_dos &&
                TD_ID(id1.oid) !in objs.inactive_non_hcoded_tds &&
                id1 !in objs.inactive_fds &&
                DO_ID(id1.oid) !in objs.inactive_dos &&
                TD_ID(id1.oid) !in objs.hcoded_tds
    {}

    forall id1 | id1 in objs.active_dos
        ensures TD_ID(id1.oid) !in objs.inactive_non_hcoded_tds &&
                FD_ID(id1.oid) !in objs.inactive_fds &&
                id1 !in objs.inactive_dos &&
                TD_ID(id1.oid) !in objs.hcoded_tds
    {}

    forall id1 | id1 in objs.inactive_non_hcoded_tds
        ensures FD_ID(id1.oid) !in objs.inactive_fds &&
                DO_ID(id1.oid) !in objs.inactive_dos &&
                id1 !in objs.hcoded_tds
    {}

    forall id1 | id1 in objs.inactive_fds
        ensures DO_ID(id1.oid) !in objs.inactive_dos &&
                TD_ID(id1.oid) !in objs.hcoded_tds
    {}

    forall id1 | id1 in objs.inactive_dos
        ensures (TD_ID(id1.oid) !in objs.hcoded_tds)
    {}

    assert IsValidState_Objects_UniqueObjIDs(objs);
    assert IsValidState_Objects_UniqueObjIDs(ws'.objects);
}

// Lemma: Prove P_WSD_DevActivate_Multi_SubjObjModifications_Objs have unchanged DM_AllTD/FD/DOIDs
lemma Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_ProveSameSetOfTDsFDsDOs(
    ws:DM_State, ws':DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>
)
    requires dev_tds <= DM_AllTDIDs(ws.objects)
    requires dev_fds <= DM_AllFDIDs(ws.objects)
    requires dev_dos <= DM_AllDOIDs(ws.objects)
    requires dev_hcoded_td_ids <= dev_tds
    requires dev_hcoded_td_ids <= DM_AllHCodedTDIDs(ws.subjects)
        // Requirement: <dev_tds/fds/dos/hcoded_tds> must exist in the system

    requires var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
            (MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds) + dev_non_hcoded_td_ids) &&
            (MapGetKeys(ws'.objects.active_fds) == MapGetKeys(ws.objects.active_fds) + dev_fds) &&
            (MapGetKeys(ws'.objects.active_dos) == MapGetKeys(ws.objects.active_dos) + dev_dos) &&
            (ws'.objects.inactive_non_hcoded_tds == ws.objects.inactive_non_hcoded_tds - dev_non_hcoded_td_ids) &&
            (ws'.objects.inactive_fds == ws.objects.inactive_fds - dev_fds) &&
            (ws'.objects.inactive_dos == ws.objects.inactive_dos - dev_dos) &&
            MapGetKeys(ws'.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds)

    ensures DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects) &&
            DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects) &&
            DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_ProvePreConditionForObjModifications(
    ws:DM_State, dev_ids:set<Dev_ID>, pid:Partition_ID
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires DM_IsValidState_Objects(ws)

    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    ensures var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids);
            P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions();

    Lemma_WSD_ObjsOwnedByDevs_Properties(ws, dev_ids);
    Lemma_WSD_ObjsOwnedByDevs_Properties_NonHCodedTDs(ws, dev_ids);
}

lemma Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part2_Prove(
    ws:DM_State, ws':DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>,
    pid:Partition_ID // ID of the target partition
)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
    
    requires P_DMObjectsHasUniqueIDs(ws'.objects) &&
            MapGetKeys(ws'.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds)
    requires (forall id :: id in dev_tds &&
                    id !in dev_hcoded_td_ids
                ==> id.oid in DM_AllObjsIDs(ws'.objects) &&
                    id in ws'.objects.active_non_hcoded_tds &&
                    DM_ObjPID(ws'.objects, id.oid) == pid &&
                    DM_IsTDClearVal(ws'.objects, id)
            ) &&
            (forall id :: id in dev_tds &&
                    id in dev_hcoded_td_ids
                ==> id.oid in DM_AllObjsIDs(ws'.objects) &&
                    id in ws'.objects.hcoded_tds &&
                    DM_ObjPID(ws'.objects, id.oid) == pid &&
                    ws'.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val
            ) &&
                // Only hardcoded TDs can be reused
            (forall id :: id in dev_fds
                ==> id in ws'.objects.active_fds &&
                    DM_ObjPID(ws'.objects, id.oid) == pid &&
                    DM_IsFDClearVal(ws'.objects, id)
            ) &&
            (forall id :: id in dev_dos
                ==> id in ws'.objects.active_dos &&
                    DM_ObjPID(ws'.objects, id.oid) == pid &&
                    DM_IsDOClearVal(ws'.objects, id)
            )

    ensures P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part2(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part2();
}

lemma Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part3_Prove(
    ws:DM_State, ws':DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>,
    pid:Partition_ID // ID of the target partition
)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
    requires P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
    
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects)
    requires DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects)
    requires DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects)
    requires (forall id :: id in DM_AllTDIDs(ws.objects) &&
                    id !in dev_tds
                ==> DM_IsSameTD(ws'.objects, ws.objects, id)) &&
            (forall id :: id in DM_AllFDIDs(ws.objects) &&
                    id !in dev_fds
                ==> DM_IsSameFD(ws'.objects, ws.objects, id)) &&
            (forall id :: id in DM_AllDOIDs(ws.objects) &&
                    id !in dev_dos
                ==> DM_IsSameDO(ws'.objects, ws.objects, id))

    ensures P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part3(ws, ws', dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part3();
}

lemma Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions_Prove(
    ws:DM_State,
    dev_tds:set<TD_ID>, dev_fds:set<FD_ID>, dev_dos:set<DO_ID>, dev_hcoded_td_ids:set<TD_ID>,
    pid:Partition_ID // ID of the target partition
)
    requires (P_DMSubjectsHasUniqueIDs(ws.subjects)) &&
            (P_DMObjectsHasUniqueIDs(ws.objects)) &&
            (DM_IsValidState_Objects(ws))
    requires pid != NULL

    requires (dev_tds <= DM_AllTDIDs(ws.objects)) &&
            (dev_fds <= DM_AllFDIDs(ws.objects)) &&
            (dev_dos <= DM_AllDOIDs(ws.objects)) &&
            (dev_hcoded_td_ids <= dev_tds) &&
            (dev_hcoded_td_ids <= DM_AllHCodedTDIDs(ws.subjects))
                // Requirement: <dev_tds/fds/dos/hcoded_tds> must exist in the system
    requires (forall id :: id in dev_tds &&
                    id !in dev_hcoded_td_ids
                ==> id !in DM_AllHCodedTDIDs(ws.subjects))

    ensures P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions();
}




//******** Private Lemmas for <WSD_DevActivate_Multi> ********//
lemma Lemma_WSD_DevActivate_Multi_ProveProperty3_Summary(
    ws:DM_State, dev_ids:seq<Dev_ID>, next_dev_ids:seq<Dev_ID>, pid:Partition_ID,
    t:DM_Trace, next_t:DM_Trace
)
    requires |dev_ids| > 0
    requires next_dev_ids == dev_ids[1..]
    requires var op := DM_DevActivateOp(dev_ids[0].sid, pid);
             t == DM_Trace(ws, [op] + next_t.ops);
    requires next_t.ops == DevActivateMulti_ToTraceOps(next_dev_ids, pid)

    ensures t.ops == DevActivateMulti_ToTraceOps(dev_ids, pid)
{
    // Dafny can automatically prove this lemma
}


lemma Lemma_WSD_DevActivate_Multi_ProveProperty4_Summary(
    ws:DM_State, op:DM_Op,
    t:DM_Trace, t_detailed:DM_Trace_Detailed,
    next_t:DM_Trace, detailed_next_t:DM_Trace_Detailed, 
    dev_id:Dev_ID, pid:Partition_ID
)
    requires |next_t.ops| >= 0
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsValidState(next_t.ws0) && DM_IsSecureState(next_t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties

    requires dev_id in ws.subjects.devs

    requires op == DM_DevActivateOp(dev_id.sid, pid);
    requires ConvertTraceToDetailedTrace(next_t) == (detailed_next_t, true)

    requires t == DM_Trace(ws, [op] + next_t.ops)
    requires t_detailed == DM_Trace_Detailed([ws] + detailed_next_t.states, [op] + detailed_next_t.ops);
    requires DM_DetailedTrace_IsValidTrace(t_detailed)

    ensures t == ConvertDetailedTraceToTrace(t_detailed)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty5_Summary(
    t:DM_Trace, t_calc_new_states:seq<DM_State>, t_detailed:DM_Trace_Detailed, last_ws:DM_State
)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_DM_OpsProperties
    requires DM_IsValidTrace(t)

    requires |t_detailed.states| > 0

    requires t_calc_new_states == DM_CalcNewStates(t)
    requires SeqLastElem(t_detailed.states) == last_ws
    requires SeqLastElem(t_calc_new_states) == last_ws

    ensures t_detailed.states[|t_detailed.states|-1] == SeqLastElem(DM_CalcNewStates(t))
{
    // Dafny can automatically prove this lemma
}

// [NOTE] Needs 70s to verify
lemma {:timeLimitMultiplier 10} Lemma_WSD_DevActivate_Multi_Prove_EmptyDevIDs(
    ws:DM_State,
    dev_ids:seq<Dev_ID>, // ID of the devices to be deactivated
    pid:Partition_ID // ID of the target partition
)
    requires DM_IsValidState(ws)
    requires pid != NULL

    requires |dev_ids| == 0

    ensures DM_IsSecureOps(ws, ws)
    ensures P_WSD_DevActivate_Multi_SubjObjModifications(ws, ws, SeqToSet(dev_ids), pid)
{
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();

    var dev_ids_set := SeqToSet(dev_ids);
    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);

    assert dev_ids_set == {};
    assert dev_tds == {};
    assert dev_fds == {};
    assert dev_dos == {};
    assert dev_hcoded_td_ids == {};

    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions();
    assert P_WSD_DevActivate_Multi_SubjObjModifications_Objs(ws, ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid);
}

lemma Lemma_WSD_DevActivate_Multi_ProveConvertTraceToDetailedTrace_DevIDsNot0AndReturnTrue(
    ws:DM_State, t:DM_Trace, t_detailed:DM_Trace_Detailed, next_t:DM_Trace, detailed_next_t:DM_Trace_Detailed, op:DM_Op
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires DM_IsValidState(next_t.ws0) && DM_IsSecureState(next_t.ws0)

    requires DM_DetailedTrace_IsValidTrace(t_detailed)

    requires |detailed_next_t.states| > 0
    requires P_DM_OpsFulfillPreConditions(ws, op)
    requires DM_CalcNewState(ws, op).0 == detailed_next_t.states[0]
    requires DM_CalcNewState(ws, op).1 == true

    requires ConvertTraceToDetailedTrace(next_t) == (detailed_next_t, true)

    requires t == DM_Trace(ws, [op] + next_t.ops)
    requires t_detailed == DM_Trace_Detailed([ws] + detailed_next_t.states, [op] + detailed_next_t.ops)

    ensures ConvertTraceToDetailedTrace(t) == (t_detailed, true)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
        
    ensures P_WSD_DevActivate_Multi_SubjObjModifications(ws, last_ws, SeqToSet(dev_ids), pid)
        // Properties of activate devices
        // Property 11 
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    var ws_devs_tds := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_tds := WSD_TDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_fds := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_fds := WSD_FDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_dos := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_dos := WSD_DOsOwnedByDevs(ws', next_dev_ids_set);

    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);

    Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws, dev_ids[0]);
    Lemma_WSD_ObjsOwnedByDevs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert ws_devs_tds == ws'_devs_tds;
    assert ws_devs_fds == ws'_devs_fds;
    assert ws_devs_dos == ws'_devs_dos;
    assert DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects);
    assert DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects);
    assert DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects);

    // Prove P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions()
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_ProvePreConditionForObjModifications(ws, dev_ids_set, pid);
    assert P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid);

    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property1(ws, ws', last_ws, dev_ids, pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2(ws, ws', last_ws, dev_ids, pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property3(ws, ws', last_ws, dev_ids, pid);

    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Prove(ws, last_ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid);
    assert P_WSD_DevActivate_Multi_SubjObjModifications_Objs(ws, last_ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid);

    // Use P_WSD_DevActivate_Multi_SubjObjModifications_Subjs
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Subjs(ws, ws', last_ws, dev_ids, pid);
    assert P_WSD_DevActivate_Multi_SubjObjModifications_Subjs(ws, last_ws, dev_ids_set, pid);
}

// Lemma: Prove DM_IsSecureOps(ws, last_ws)
lemma Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires DM_IsValidState(ws')
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)

    requires DM_IsSecureOps(ws, ws')
    requires DM_IsSecureOps(ws', last_ws)

    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)

    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)

    ensures DM_IsSecureOps(ws, last_ws)
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);

    var ws_devs_tds := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    var ws_devs_fds := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    var ws_devs_dos := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);

    var dev0_id_set := {dev_ids[0]};
    var dev0_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev0_id_set);
    var dev0_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev0_id_set);
    var dev0_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev0_id_set);

    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    assert P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, next_dev_ids_set, pid);
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();

    // [TODO] Prove
    assume P_Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_Inner_Preconditions(ws, ws', last_ws, dev0_tds, dev0_fds, dev0_dos, ws_devs_tds, ws_devs_fds, ws_devs_dos);
    Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_Inner_Wrapper(ws, ws', last_ws, dev0_tds, dev0_fds, dev0_dos, ws_devs_tds, ws_devs_fds, ws_devs_dos);
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Subjs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    ensures last_ws.pids == ws.pids &&
            last_ws.tds_to_all_states == ws.tds_to_all_states &&
            last_ws.red_pid == ws.red_pid &&
            last_ws.devs_activatecond == ws.devs_activatecond &&
            last_ws.subjects.drvs == ws.subjects.drvs

    ensures var dev_ids_set := SeqToSet(dev_ids);
            P_WSD_DevActivate_Multi_SubjObjModifications_Subjs(ws, last_ws, dev_ids_set, pid)
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();

    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(dev_ids[1..]);

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    assert P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, next_dev_ids_set, pid);
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();

    forall id | id in last_ws.subjects.devs
        ensures (id in dev_ids_set ==> last_ws.subjects.devs[id] == ws.subjects.devs[id].(pid := pid))
        ensures (id !in dev_ids_set ==> last_ws.subjects.devs[id] == ws.subjects.devs[id])
    {
        // Dafny can automatically prove this lemma
    }

    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Subjs_Prove(ws, last_ws, dev_ids_set, pid);
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs_TDs(
    ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID, td_id:TD_ID
)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')

    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws'.subjects.devs
    requires |dev_ids| > 0

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)

    requires td_id in WSD_TDsOwnedByDevs(ws', SeqToSet(dev_ids[1..]))

    ensures P_DMObjectsHasUniqueIDs(last_ws.objects)
    ensures (td_id !in DM_AllHCodedTDIDs(ws'.subjects)) ==> td_id in last_ws.objects.active_non_hcoded_tds
    ensures (td_id in DM_AllHCodedTDIDs(ws'.subjects)) ==> td_id in ws'.objects.hcoded_tds
    ensures MapGetKeys(ws'.objects.hcoded_tds) == MapGetKeys(last_ws.objects.hcoded_tds)
        // Properties needed by the following properties
    ensures DM_ObjPID(last_ws.objects, td_id.oid) == pid
    ensures (td_id !in DM_AllHCodedTDIDs(ws'.subjects)) ==> DM_IsTDClearVal(last_ws.objects, td_id)
    ensures (td_id in DM_AllHCodedTDIDs(ws'.subjects)) ==> ws'.objects.hcoded_tds[td_id].val == last_ws.objects.hcoded_tds[td_id].val
{
    reveal IsValidState_Objects_UniqueObjIDs();

    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs_FDs(
    ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID, fd_id:FD_ID
)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')

    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws'.subjects.devs
    requires |dev_ids| > 0

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)

    requires fd_id in WSD_FDsOwnedByDevs(ws', SeqToSet(dev_ids[1..]))

    ensures P_DMObjectsHasUniqueIDs(last_ws.objects)
    ensures fd_id in last_ws.objects.active_fds
        // Properties needed by the following properties
    ensures DM_ObjPID(last_ws.objects, fd_id.oid) == pid
    ensures DM_IsFDClearVal(last_ws.objects, fd_id)
{
    reveal IsValidState_Objects_UniqueObjIDs();

    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs_DOs(
    ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID, do_id:DO_ID
)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')

    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws'.subjects.devs
    requires |dev_ids| > 0

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)

    requires do_id in WSD_DOsOwnedByDevs(ws', SeqToSet(dev_ids[1..]))

    ensures P_DMObjectsHasUniqueIDs(last_ws.objects)
    ensures do_id in last_ws.objects.active_dos
        // Properties needed by the following properties
    ensures DM_ObjPID(last_ws.objects, do_id.oid) == pid
    ensures DM_IsDOClearVal(last_ws.objects, do_id)
{
    reveal IsValidState_Objects_UniqueObjIDs();

    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS_Inner(
    ws:DM_State, ws':DM_State, 
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    ensures var s_ids := SeqToSet(dev_ids[1..]);
            forall dev_id, o_id :: dev_id in s_ids && o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_DoOwnObj(ws'.subjects, dev_id.sid, o_id) == DM_DoOwnObj(ws.subjects, dev_id.sid, o_id)
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var s_ids := SeqToSet(dev_ids[1..]);

    assert DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects);
    assert DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects);
    assert DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects);
    assert DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects);
    assert DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects);
    assert forall dev_id, o_id :: dev_id in s_ids && o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_DoOwnObj(ws'.subjects, dev_id.sid, o_id) == DM_DoOwnObj(ws.subjects, dev_id.sid, o_id);
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS_HCodedTDs(
    ws:DM_State, ws':DM_State, 
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires MapGetKeys(ws.objects.hcoded_tds) == DM_AllHCodedTDIDs(ws.subjects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires var k := DMStateToState(ws);
             k.subjects.devs[dev_ids[0]].hcoded_td_id in k.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    ensures var s_ids := SeqToSet(dev_ids[1..]);
            WSD_HCodedTDsOwnedByDevs(ws, s_ids) == WSD_HCodedTDsOwnedByDevs(ws', s_ids)
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var next_dev_ids := SeqToSet(dev_ids[1..]);

    var htd_set1 := WSD_HCodedTDsOwnedByDevs(ws, next_dev_ids);
    var htd_set2 := WSD_HCodedTDsOwnedByDevs(ws', next_dev_ids);

    // Prove IDs of devices' HCoded TDs are unchanged
    var k := DMStateToState(ws);
    var k' := DMStateToState(ws');

    Lemma_P_DevActivate_ModificationToState_Properties(k, dev_ids[0].sid, pid, k');
    assert forall id :: id in ws.subjects.devs
                ==> ws.subjects.devs[id].hcoded_td_id == ws'.subjects.devs[id].hcoded_td_id;

    forall id | id in htd_set1
        ensures id in htd_set2
    {
        var dev_id := Lemma_WSD_HCodedTDsOwnedByDevs_PropertyGetOwnerDevice(ws, next_dev_ids, id);

        // Prove ws'.subjects.devs[dev_id].hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id;
        assert ws'.subjects.devs[dev_id].hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id;
    }

    forall id | id in htd_set2
        ensures id in htd_set1
    {
        var dev_id := Lemma_WSD_HCodedTDsOwnedByDevs_PropertyGetOwnerDevice(ws', next_dev_ids, id);

        // Prove ws'.subjects.devs[dev_id].hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id;
        assert ws'.subjects.devs[dev_id].hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id;
    }

    Lemma_Set_Equality(htd_set1, htd_set2);
    assert htd_set1 == htd_set2;
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(
    ws:DM_State, ws':DM_State, 
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)

    ensures MapGetKeys(ws.subjects.devs) == MapGetKeys(ws'.subjects.devs)
    ensures var s_ids := SeqToSet(dev_ids[1..]);
            WSD_TDsOwnedByDevs(ws, s_ids) == WSD_TDsOwnedByDevs(ws', s_ids) &&
            WSD_FDsOwnedByDevs(ws, s_ids) == WSD_FDsOwnedByDevs(ws', s_ids) &&
            WSD_DOsOwnedByDevs(ws, s_ids) == WSD_DOsOwnedByDevs(ws', s_ids) &&
            WSD_HCodedTDsOwnedByDevs(ws, s_ids) == WSD_HCodedTDsOwnedByDevs(ws', s_ids)
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
    assert MapGetKeys(ws.subjects.devs) == MapGetKeys(ws'.subjects.devs);

    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS_TDsFDsDOs(ws, ws', dev_ids, pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS_HCodedTDs(ws, ws', dev_ids, pid);
}

predicate {:opaque} P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(
    ws:DM_State, ws':DM_State, dev0_id:Dev_ID, pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires dev0_id in ws.subjects.devs

    ensures P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev0_id, pid)
                ==> MapGetKeys(ws.subjects.devs) == MapGetKeys(ws'.subjects.devs)
{
    var k := DMStateToState(ws);

    (pid != NULL) &&
    (k.subjects.devs[dev0_id].hcoded_td_id in k.objects.hcoded_tds) &&
    (forall id :: id in k.subjects.devs[dev0_id].td_ids && 
        id != k.subjects.devs[dev0_id].hcoded_td_id 
        ==> id in k.objects.inactive_non_hcoded_tds) &&
    (forall id :: id in k.subjects.devs[dev0_id].fd_ids ==> id in k.objects.inactive_fds) &&
    (forall id :: id in k.subjects.devs[dev0_id].do_ids ==> id in k.objects.inactive_dos) &&
    P_DevActivate_ModificationToState(DMStateToState(ws), dev0_id.sid, pid, DMStateToState(ws'))
}

lemma Lemma_P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0_Prove(
    ws:DM_State, ws':DM_State, dev0_id:Dev_ID, pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires dev0_id in ws.subjects.devs
    requires pid != NULL

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev0_id].td_ids && 
                    id != k.subjects.devs[dev0_id].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev0_id].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev0_id].do_ids ==> id in k.objects.inactive_dos
    requires var k := DMStateToState(ws);
             k.subjects.devs[dev0_id].hcoded_td_id in k.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev0_id.sid, pid, DMStateToState(ws'))
    
    ensures P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev0_id, pid)
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
}

// [NOTE] Needs 30s to verify
lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS_TDsFDsDOs(
    ws:DM_State, ws':DM_State, 
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    ensures var s_ids := SeqToSet(dev_ids[1..]);
            WSD_TDsOwnedByDevs(ws, s_ids) == WSD_TDsOwnedByDevs(ws', s_ids) &&
            WSD_FDsOwnedByDevs(ws, s_ids) == WSD_FDsOwnedByDevs(ws', s_ids) &&
            WSD_DOsOwnedByDevs(ws, s_ids) == WSD_DOsOwnedByDevs(ws', s_ids)
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var s_ids := SeqToSet(dev_ids[1..]);

    assert DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects);
    assert DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects);
    assert DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects);
    assert DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects);
    assert DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS_Inner(ws, ws', dev_ids, pid);
    assert forall dev_id, o_id :: dev_id in s_ids && o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_DoOwnObj(ws'.subjects, dev_id.sid, o_id) == DM_DoOwnObj(ws.subjects, dev_id.sid, o_id);

    var td_set1 := WSD_TDsOwnedByDevs(ws, s_ids);
    var td_set2 := WSD_TDsOwnedByDevs(ws', s_ids);
    assert forall id :: id in td_set1 ==> id in td_set2;
    assert forall id :: id in td_set2 ==> id in td_set1;
    Lemma_Set_Equality(td_set1, td_set2);
    assert td_set1 == td_set2;

    var fd_set1 := WSD_FDsOwnedByDevs(ws, s_ids);
    var fd_set2 := WSD_FDsOwnedByDevs(ws', s_ids);
    assert forall id :: id in fd_set1 ==> id in fd_set2;
    assert forall id :: id in fd_set2 ==> id in fd_set1;
    Lemma_Set_Equality(fd_set1, fd_set2);
    assert fd_set1 == fd_set2;

    var do_set1 := WSD_DOsOwnedByDevs(ws, s_ids);
    var do_set2 := WSD_DOsOwnedByDevs(ws', s_ids);
    assert forall id :: id in do_set1 ==> id in do_set2;
    assert forall id :: id in do_set2 ==> id in do_set1;
    Lemma_Set_Equality(do_set1, do_set2);
    assert do_set1 == do_set2;
}

lemma Lemma_WSD_DevActivate_Multi_Private(
    next_t:DM_Trace, next_dev_ids:seq<Dev_ID>, op:DM_Op, t:DM_Trace, dev_ids:seq<Dev_ID>, pid:Partition_ID
)
    requires |dev_ids| > 0

    requires t.ops == [op] + next_t.ops
    requires next_dev_ids == dev_ids[1..]
   
    requires op == DM_DevActivateOp(dev_ids[0].sid, pid)

    requires |next_dev_ids| == |next_t.ops|
    requires (forall i :: 0 <= i < |next_t.ops| ==> next_t.ops[i] == DM_DevActivateOp(next_dev_ids[i].sid, pid))

    requires |dev_ids| == |t.ops|

    ensures forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_DevActivateOp(dev_ids[i].sid, pid)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property3(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    requires var dev_ids_set := SeqToSet(dev_ids);
            var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
            var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
            P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid) &&
            P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1(ws, last_ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)

    ensures var dev_ids_set := SeqToSet(dev_ids);
            var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
            var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
            P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part3(ws, last_ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Sub_TD(ws, ws', last_ws, dev_ids, pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Sub_FD(ws, ws', last_ws, dev_ids, pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Sub_DO(ws, ws', last_ws, dev_ids, pid);

    var dev_ids_set := SeqToSet(dev_ids);
    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
    var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;

    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1();
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part3_Prove(ws, last_ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid);
}

predicate {:opaque} P_Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_Inner_Preconditions(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    td_ids1:set<TD_ID>, fd_ids1:set<FD_ID>, do_ids1:set<DO_ID>, // Modified objects between ws and ws'
    td_ids2:set<TD_ID>, fd_ids2:set<FD_ID>, do_ids2:set<DO_ID> // Modified objects between ws' and last_ws
)
    requires DM_AllTDIDs(ws.objects) == DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(last_ws.objects)
    requires DM_AllFDIDs(ws.objects) == DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(last_ws.objects)
    requires DM_AllDOIDs(ws.objects) == DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(last_ws.objects)
{
    var k := DMStateToState(ws);
    var k' := DMStateToState(ws');
    var last_k := DMStateToState(last_ws);

    (forall id :: id in AllTDIDs(k.objects) &&
            id !in td_ids1
        ==> ObjStateUnchanged_TD(k.objects, k'.objects, id)
    ) &&
    (forall id :: id in AllTDIDs(k.objects) &&
            id in td_ids1 && 
            id !in AllHCodedTDIDs(k.subjects)
        ==> id in k'.objects.active_non_hcoded_tds &&
            IsTDClearVal(k'.objects.active_non_hcoded_tds, id)
    ) &&
    (forall id :: id in AllFDIDs(k.objects) &&
            id !in fd_ids1
        ==> ObjStateUnchanged_FD(k.objects, k'.objects, id)
    ) &&
    (forall id :: id in AllFDIDs(k.objects) &&
            id in fd_ids1
        ==> id in k'.objects.active_fds &&
            IsFDClearVal(k'.objects.active_fds, id)
    ) &&
    (forall id :: id in AllDOIDs(k.objects) &&
            id !in do_ids1
        ==> ObjStateUnchanged_DO(k.objects, k'.objects, id)
    ) &&
    (forall id :: id in AllDOIDs(k.objects) &&
            id in do_ids1
        ==> id in k'.objects.active_dos &&
            IsDOClearVal(k'.objects.active_dos, id)
    ) &&
        // Requirement: Relationship betwen ws and ws'

    (forall id :: id in AllTDIDs(k'.objects) &&
            id !in td_ids2
        ==> ObjStateUnchanged_TD(k'.objects, last_k.objects, id)
    ) &&
    (forall id :: id in AllFDIDs(k'.objects) &&
            id !in fd_ids2
        ==> ObjStateUnchanged_FD(k'.objects, last_k.objects, id)
    ) &&
    (forall id :: id in AllDOIDs(k'.objects) &&
            id !in do_ids2
        ==> ObjStateUnchanged_DO(k'.objects, last_k.objects, id)
    ) &&
        // Requirement: Relationship betwen ws' and last_ws

    (td_ids1 * td_ids2 == {}) &&
    (fd_ids1 * fd_ids2 == {}) &&
    (do_ids1 * do_ids2 == {}) &&

    (true)
}

// [NOTE] Needs 40s to verify
lemma Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_Inner_Wrapper(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    td_ids1:set<TD_ID>, fd_ids1:set<FD_ID>, do_ids1:set<DO_ID>, // Modified objects between ws and ws'
    td_ids2:set<TD_ID>, fd_ids2:set<FD_ID>, do_ids2:set<DO_ID> // Modified objects between ws' and last_ws
)
    requires DM_IsValidState(ws)
    requires DM_IsValidState(ws')
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)

    requires DM_IsSecureOps(ws, ws')
    requires DM_IsSecureOps(ws', last_ws)

    requires P_Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_Inner_Preconditions(
                ws, ws', last_ws, td_ids1, fd_ids1, do_ids1, td_ids2, fd_ids2, do_ids2)

    ensures DM_IsSecureOps(ws, last_ws)
{
    reveal P_Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_Inner_Preconditions();
    Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_Inner(ws, ws', last_ws, td_ids1, fd_ids1, do_ids1, td_ids2, fd_ids2, do_ids2);
}

lemma Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_Inner(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    td_ids1:set<TD_ID>, fd_ids1:set<FD_ID>, do_ids1:set<DO_ID>, // Modified objects between ws and ws'
    td_ids2:set<TD_ID>, fd_ids2:set<FD_ID>, do_ids2:set<DO_ID> // Modified objects between ws' and last_ws
)
    requires DM_IsValidState(ws)
    requires DM_IsValidState(ws')
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)

    requires DM_IsSecureOps(ws, ws')
    requires DM_IsSecureOps(ws', last_ws)

    requires var k := DMStateToState(ws);
             var k' := DMStateToState(ws');
             (forall id :: id in AllTDIDs(k.objects) &&
                    id !in td_ids1
                ==> ObjStateUnchanged_TD(k.objects, k'.objects, id)) &&
             (forall id :: id in AllTDIDs(k.objects) &&
                    id in td_ids1 && 
                    id !in AllHCodedTDIDs(k.subjects)
                ==> id in k'.objects.active_non_hcoded_tds &&
                    IsTDClearVal(k'.objects.active_non_hcoded_tds, id))
    requires var k := DMStateToState(ws);
             var k' := DMStateToState(ws');
             (forall id :: id in AllFDIDs(k.objects) &&
                    id !in fd_ids1
                ==> ObjStateUnchanged_FD(k.objects, k'.objects, id)) &&
             (forall id :: id in AllFDIDs(k.objects) &&
                    id in fd_ids1
                ==> id in k'.objects.active_fds &&
                    IsFDClearVal(k'.objects.active_fds, id))
    requires var k := DMStateToState(ws);
             var k' := DMStateToState(ws');
             (forall id :: id in AllDOIDs(k.objects) &&
                    id !in do_ids1
                ==> ObjStateUnchanged_DO(k.objects, k'.objects, id)) &&
             (forall id :: id in AllDOIDs(k.objects) &&
                    id in do_ids1
                ==> id in k'.objects.active_dos &&
                    IsDOClearVal(k'.objects.active_dos, id))
        // Requirement: Relationship betwen ws and ws'

    requires var k' := DMStateToState(ws');
             var last_k := DMStateToState(last_ws);
             (forall id :: id in AllTDIDs(k'.objects) &&
                    id !in td_ids2
                ==> ObjStateUnchanged_TD(k'.objects, last_k.objects, id))
    requires var k' := DMStateToState(ws');
             var last_k := DMStateToState(last_ws);
             (forall id :: id in AllFDIDs(k'.objects) &&
                    id !in fd_ids2
                ==> ObjStateUnchanged_FD(k'.objects, last_k.objects, id))
    requires var k' := DMStateToState(ws');
             var last_k := DMStateToState(last_ws);
             (forall id :: id in AllDOIDs(k'.objects) &&
                    id !in do_ids2
                ==> ObjStateUnchanged_DO(k'.objects, last_k.objects, id))
        // Requirement: Relationship betwen ws' and last_ws

    requires td_ids1 * td_ids2 == {}
    requires fd_ids1 * fd_ids2 == {}
    requires do_ids1 * do_ids2 == {}

    ensures DM_IsSecureOps(ws, last_ws)
{
    Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_TDs(ws, ws', last_ws, td_ids1, fd_ids1, do_ids1, td_ids2, fd_ids2, do_ids2);
    Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_FDs(ws, ws', last_ws, td_ids1, fd_ids1, do_ids1, td_ids2, fd_ids2, do_ids2);
    Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_DOs(ws, ws', last_ws, td_ids1, fd_ids1, do_ids1, td_ids2, fd_ids2, do_ids2);
}

lemma Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_TDs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    td_ids1:set<TD_ID>, fd_ids1:set<FD_ID>, do_ids1:set<DO_ID>, // Modified objects between ws and ws'
    td_ids2:set<TD_ID>, fd_ids2:set<FD_ID>, do_ids2:set<DO_ID> // Modified objects between ws' and last_ws
)
    requires DM_IsValidState(ws)
    requires DM_IsValidState(ws')
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)

    requires DM_IsSecureOps(ws, ws')
    requires DM_IsSecureOps(ws', last_ws)

    requires var k := DMStateToState(ws);
             var k' := DMStateToState(ws');
             (forall id :: id in AllTDIDs(k.objects) &&
                    id !in td_ids1
                ==> ObjStateUnchanged_TD(k.objects, k'.objects, id)) &&
             (forall id :: id in AllTDIDs(k.objects) &&
                    id in td_ids1 && 
                    id !in AllHCodedTDIDs(k.subjects)
                ==> id in k'.objects.active_non_hcoded_tds &&
                    IsTDClearVal(k'.objects.active_non_hcoded_tds, id))
        // Requirement: Relationship betwen ws and ws'

    requires var k' := DMStateToState(ws');
             var last_k := DMStateToState(last_ws);
             (forall id :: id in AllTDIDs(k'.objects) &&
                    id !in td_ids2
                ==> ObjStateUnchanged_TD(k'.objects, last_k.objects, id))
        // Requirement: Relationship betwen ws' and last_ws

    requires td_ids1 * td_ids2 == {}

    ensures var k := DMStateToState(ws);
            var last_k := DMStateToState(last_ws);
            forall td_id:TD_ID :: td_id in AllTDIDs(last_k.objects) &&
                    ObjPID(last_k, td_id.oid) != ObjPID(k, td_id.oid) &&
                    ObjPID(last_k, td_id.oid) != NULL &&
                        // For a transition from k to last_k, if a TD is activated (or moved) into a partition
                    td_id !in AllHCodedTDIDs(last_k.subjects)
                        // TD is not a hardcoded TD
                ==> (td_id in last_k.objects.active_non_hcoded_tds &&
                    IsTDClearVal(last_k.objects.active_non_hcoded_tds, td_id))
                // TD is cleared
{
    var k := DMStateToState(ws);
    var k' := DMStateToState(ws');
    var last_k := DMStateToState(last_ws);

    assert AllTDIDs(k.objects) == AllTDIDs(k'.objects) == AllTDIDs(last_k.objects);

    forall td_id:TD_ID | td_id in AllTDIDs(last_k.objects) &&
                    ObjPID(last_k, td_id.oid) != ObjPID(k, td_id.oid) &&
                    ObjPID(last_k, td_id.oid) != NULL &&
                        // For a transition from k to last_k, if a TD is activated (or moved) into a partition
                    td_id !in AllHCodedTDIDs(last_k.subjects)
                        // TD is not a hardcoded TD
        ensures td_id in last_k.objects.active_non_hcoded_tds
        ensures IsTDClearVal(last_k.objects.active_non_hcoded_tds, td_id)
                // TD is cleared
    {
        assert td_id in last_k.objects.active_non_hcoded_tds;

        if(td_id in td_ids1)
        {
            assert IsTDClearVal(k'.objects.active_non_hcoded_tds, td_id);
            assert td_id !in td_ids2;
            assert IsTDClearVal(last_k.objects.active_non_hcoded_tds, td_id);
        }
        else if(td_id in td_ids2)
        {
            assert IsTDClearVal(last_k.objects.active_non_hcoded_tds, td_id);
        }
        else
        {
            assert ObjPID(last_k, td_id.oid) == ObjPID(k, td_id.oid);
        }
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_FDs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    td_ids1:set<TD_ID>, fd_ids1:set<FD_ID>, do_ids1:set<DO_ID>, // Modified objects between ws and ws'
    td_ids2:set<TD_ID>, fd_ids2:set<FD_ID>, do_ids2:set<DO_ID> // Modified objects between ws' and last_ws
)
    requires DM_IsValidState(ws)
    requires DM_IsValidState(ws')
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)

    requires DM_IsSecureOps(ws, ws')
    requires DM_IsSecureOps(ws', last_ws)

    requires var k := DMStateToState(ws);
             var k' := DMStateToState(ws');
             (forall id :: id in AllFDIDs(k.objects) &&
                    id !in fd_ids1
                ==> ObjStateUnchanged_FD(k.objects, k'.objects, id)) &&
             (forall id :: id in AllFDIDs(k.objects) &&
                    id in fd_ids1
                ==> id in k'.objects.active_fds &&
                    IsFDClearVal(k'.objects.active_fds, id))
        // Requirement: Relationship betwen ws and ws'

    requires var k' := DMStateToState(ws');
             var last_k := DMStateToState(last_ws);
             (forall id :: id in AllFDIDs(k'.objects) &&
                    id !in fd_ids2
                ==> ObjStateUnchanged_FD(k'.objects, last_k.objects, id))
        // Requirement: Relationship betwen ws' and last_ws

    requires fd_ids1 * fd_ids2 == {}

    ensures var k := DMStateToState(ws);
            var last_k := DMStateToState(last_ws);
            forall fd_id:FD_ID :: fd_id in AllFDIDs(last_k.objects) &&
                    ObjPID(last_k, fd_id.oid) != ObjPID(k, fd_id.oid) &&
                    ObjPID(last_k, fd_id.oid) != NULL
                        // For a transition from k to last_k, if a FD is activated (or moved) into a partition
                ==> fd_id in last_k.objects.active_fds &&
                    IsFDClearVal(last_k.objects.active_fds, fd_id)
{
    var k := DMStateToState(ws);
    var k' := DMStateToState(ws');
    var last_k := DMStateToState(last_ws);

    assert AllFDIDs(k.objects) == AllFDIDs(k'.objects) == AllFDIDs(last_k.objects);

    forall fd_id:FD_ID | fd_id in AllFDIDs(last_k.objects) &&
                    ObjPID(last_k, fd_id.oid) != ObjPID(k, fd_id.oid) &&
                    ObjPID(last_k, fd_id.oid) != NULL
                        // For a transition from k to last_k, if a FD is activated (or moved) into a partition
        ensures fd_id in last_k.objects.active_fds
        ensures IsFDClearVal(last_k.objects.active_fds, fd_id)
                // FD is cleared
    {
        assert fd_id in last_k.objects.active_fds;

        if(fd_id in fd_ids1)
        {
            assert IsFDClearVal(k'.objects.active_fds, fd_id);
            assert fd_id !in fd_ids2;
            assert IsFDClearVal(last_k.objects.active_fds, fd_id);
        }
        else if(fd_id in fd_ids2)
        {
            assert IsFDClearVal(last_k.objects.active_fds, fd_id);
        }
        else
        {
            assert ObjPID(last_k, fd_id.oid) == ObjPID(k, fd_id.oid);
        }
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveDM_IsSecureOps_DOs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    td_ids1:set<TD_ID>, fd_ids1:set<FD_ID>, do_ids1:set<DO_ID>, // Modified objects between ws and ws'
    td_ids2:set<TD_ID>, fd_ids2:set<FD_ID>, do_ids2:set<DO_ID> // Modified objects between ws' and last_ws
)
    requires DM_IsValidState(ws)
    requires DM_IsValidState(ws')
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)

    requires DM_IsSecureOps(ws, ws')
    requires DM_IsSecureOps(ws', last_ws)

    requires var k := DMStateToState(ws);
             var k' := DMStateToState(ws');
             (forall id :: id in AllDOIDs(k.objects) &&
                    id !in do_ids1
                ==> ObjStateUnchanged_DO(k.objects, k'.objects, id)) &&
             (forall id :: id in AllDOIDs(k.objects) &&
                    id in do_ids1
                ==> id in k'.objects.active_dos &&
                    IsDOClearVal(k'.objects.active_dos, id))
        // Requirement: Relationship betwen ws and ws'

    requires var k' := DMStateToState(ws');
             var last_k := DMStateToState(last_ws);
             (forall id :: id in AllDOIDs(k'.objects) &&
                    id !in do_ids2
                ==> ObjStateUnchanged_DO(k'.objects, last_k.objects, id))
        // Requirement: Relationship betwen ws' and last_ws

    requires do_ids1 * do_ids2 == {}

    ensures var k := DMStateToState(ws);
            var last_k := DMStateToState(last_ws);
            forall do_id:DO_ID :: do_id in AllDOIDs(last_k.objects) &&
                    ObjPID(last_k, do_id.oid) != ObjPID(k, do_id.oid) &&
                    ObjPID(last_k, do_id.oid) != NULL
                        // For a transition from k to last_k, if a DO is activated (or moved) into a partition
                ==> do_id in last_k.objects.active_dos &&
                    IsDOClearVal(last_k.objects.active_dos, do_id)
{
    var k := DMStateToState(ws);
    var k' := DMStateToState(ws');
    var last_k := DMStateToState(last_ws);

    assert AllDOIDs(k.objects) == AllDOIDs(k'.objects) == AllDOIDs(last_k.objects);

    forall do_id:DO_ID | do_id in AllDOIDs(last_k.objects) &&
                    ObjPID(last_k, do_id.oid) != ObjPID(k, do_id.oid) &&
                    ObjPID(last_k, do_id.oid) != NULL
                        // For a transition from k to last_k, if a DO is activated (or moved) into a partition
        ensures do_id in last_k.objects.active_dos
        ensures IsDOClearVal(last_k.objects.active_dos, do_id)
                // DO is cleared
    {
        assert do_id in last_k.objects.active_dos;

        if(do_id in do_ids1)
        {
            assert IsDOClearVal(k'.objects.active_dos, do_id);
            assert do_id !in do_ids2;
            assert IsDOClearVal(last_k.objects.active_dos, do_id);
        }
        else if(do_id in do_ids2)
        {
            assert IsDOClearVal(last_k.objects.active_dos, do_id);
        }
        else
        {
            assert ObjPID(last_k, do_id.oid) == ObjPID(k, do_id.oid);
        }
    }
}




//******** Private Lemmas of Private Lemmas for <WSD_DevActivate_Multi> ********//
lemma Lemma_WSD_DevActivate_Multi_DevIDsLargerThan1_NextReturnTrue_ProveNumOfOpsAndDevIDs(
    t:DM_Trace, next_t:DM_Trace, op:DM_Op, dev_ids:seq<Dev_ID>, next_dev_ids:seq<Dev_ID>
)
    requires |dev_ids| > 0

    requires t.ops == [op] + next_t.ops
    requires next_dev_ids == dev_ids[1..]
    requires |next_t.ops| == |next_dev_ids|

    ensures |t.ops| == |dev_ids| 
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Sub_TD(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
        
    ensures (forall id :: id in DM_AllTDIDs(ws.objects) &&
                    id !in WSD_TDsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> DM_IsSameTD(last_ws.objects, ws.objects, id))
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    var ws_devs_tds := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    var ws_devs_fds := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    var ws_devs_dos := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);

    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);

    Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws, dev_ids[0]);
    Lemma_WSD_ObjsOwnedByDevs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0_Prove(ws, ws', dev_ids[0], pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects);
    assert DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects);
    assert DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects);

    Lemma_SequenceHighlightFirstElem(dev_ids);
    assert dev_ids == [dev_ids[0]] + next_dev_ids;
    assert dev_ids_set == {dev_ids[0]} + next_dev_ids_set;

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    assert P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, next_dev_ids_set, pid);
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();

    forall id | id in DM_AllTDIDs(ws.objects) &&
            id !in WSD_TDsOwnedByDevs(ws, dev_ids_set)
        ensures DM_IsSameTD(last_ws.objects, ws.objects, id)
    {
        assert id !in WSD_TDsOwnedByDevs(ws, SeqToSet(dev_ids[1..])) && id !in ws.subjects.devs[dev_ids[0]].td_ids;
        
        assert DM_IsSameTD(last_ws.objects, ws'.objects, id);
        assert DM_IsSameTD(ws'.objects, ws.objects, id);
        assert DM_IsSameTD(last_ws.objects, ws.objects, id);
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Sub_FD(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
        
    ensures (forall id :: id in DM_AllFDIDs(ws.objects) &&
                    id !in WSD_FDsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> DM_IsSameFD(last_ws.objects, ws.objects, id))
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    var ws_devs_tds := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    var ws_devs_fds := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    var ws_devs_dos := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);

    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);

    Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws, dev_ids[0]);
    Lemma_WSD_ObjsOwnedByDevs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0_Prove(ws, ws', dev_ids[0], pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects);
    assert DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects);
    assert DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects);

    Lemma_SequenceHighlightFirstElem(dev_ids);
    assert dev_ids == [dev_ids[0]] + next_dev_ids;
    assert dev_ids_set == {dev_ids[0]} + next_dev_ids_set;

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    assert P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, next_dev_ids_set, pid);
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();

    forall id | id in DM_AllFDIDs(ws.objects) &&
            id !in WSD_FDsOwnedByDevs(ws, dev_ids_set)
        ensures DM_IsSameFD(last_ws.objects, ws.objects, id)
    {
        assert id !in WSD_FDsOwnedByDevs(ws, SeqToSet(dev_ids[1..])) && id !in ws.subjects.devs[dev_ids[0]].fd_ids;
        
        assert DM_IsSameFD(last_ws.objects, ws'.objects, id);
        assert DM_IsSameFD(ws'.objects, ws.objects, id);
        assert DM_IsSameFD(last_ws.objects, ws.objects, id);
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Sub_DO(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
    
    ensures (forall id :: id in DM_AllDOIDs(ws.objects) &&
                    id !in WSD_DOsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> DM_IsSameDO(last_ws.objects, ws.objects, id))
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    var ws_devs_tds := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    var ws_devs_fds := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    var ws_devs_dos := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);

    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);

    Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws, dev_ids[0]);
    Lemma_WSD_ObjsOwnedByDevs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0_Prove(ws, ws', dev_ids[0], pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects);
    assert DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects);
    assert DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects);

    Lemma_SequenceHighlightFirstElem(dev_ids);
    assert dev_ids == [dev_ids[0]] + next_dev_ids;
    assert dev_ids_set == {dev_ids[0]} + next_dev_ids_set;

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    assert P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, next_dev_ids_set, pid);
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();
    
    forall id | id in DM_AllDOIDs(ws.objects) &&
            id !in dev_dos
        ensures DM_IsSameDO(last_ws.objects, ws.objects, id)
    {
        assert id !in ws_devs_dos && id !in ws.subjects.devs[dev_ids[0]].do_ids;
        
        assert DM_IsSameDO(last_ws.objects, ws'.objects, id);
        assert DM_IsSameDO(ws'.objects, ws.objects, id);
        assert DM_IsSameDO(last_ws.objects, ws.objects, id);
    }
}

lemma Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_TDs(
    ws:DM_State, ws':DM_State, dev_id:Dev_ID, td_id:TD_ID, pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires pid != NULL

    requires dev_id in ws.subjects.devs
    requires td_id in ws.subjects.devs[dev_id].td_ids
    requires td_id !in DM_AllHCodedTDIDs(ws.subjects)
        // Requirement: TD must be owned by the device <dev_id>, and not a hardcoded TD

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].td_ids && 
                    id != k.subjects.devs[dev_id].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos
    requires ws.subjects.devs[dev_id].hcoded_td_id in ws.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_id.sid, pid, DMStateToState(ws'))
        // Requirement: ws' is the activation of the device <dev_id>

    ensures DM_ObjPID(ws'.objects, td_id.oid) == pid
    ensures DM_IsTDClearVal(ws'.objects, td_id)
    ensures td_id in ws'.objects.active_non_hcoded_tds
        // Properties of objects
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_TDIDs(
    ws:DM_State, ws':DM_State, dev_id:Dev_ID, pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires pid != NULL

    requires dev_id in ws.subjects.devs

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].td_ids && 
                    id != k.subjects.devs[dev_id].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos
    requires ws.subjects.devs[dev_id].hcoded_td_id in ws.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_id.sid, pid, DMStateToState(ws'))
        // Requirement: ws' is the activation of the device <dev_id>

    ensures var dev_tds := ws.subjects.devs[dev_id].td_ids;
            var dev_hcoded_td_ids := {ws.subjects.devs[dev_id].hcoded_td_id};
            var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
            (MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds) + dev_non_hcoded_td_ids) &&
            (ws'.objects.inactive_non_hcoded_tds == ws.objects.inactive_non_hcoded_tds - dev_non_hcoded_td_ids) &&
            MapGetKeys(ws'.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds)
        // Properties of object IDs
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_HCodedTDs(
    ws:DM_State, ws':DM_State, dev_id:Dev_ID, td_id:TD_ID, pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires MapGetKeys(ws.objects.hcoded_tds) == DM_AllHCodedTDIDs(ws.subjects)
    requires pid != NULL

    requires dev_id in ws.subjects.devs
    requires td_id in ws.subjects.devs[dev_id].td_ids
    requires td_id in DM_AllHCodedTDIDs(ws.subjects)
        // Requirement: TD must be owned by the device <dev_id>, and not a hardcoded TD

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].td_ids && 
                    id != k.subjects.devs[dev_id].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos
    requires ws.subjects.devs[dev_id].hcoded_td_id in ws.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_id.sid, pid, DMStateToState(ws'))
        // Requirement: ws' is the activation of the device <dev_id>

    ensures td_id in ws.objects.hcoded_tds
        // Property needed by the properties below
    ensures DM_ObjPID(ws'.objects, td_id.oid) == pid
    ensures ws'.objects.hcoded_tds[td_id].val == ws.objects.hcoded_tds[td_id].val
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_FDs(
    ws:DM_State, ws':DM_State, dev_id:Dev_ID, fd_id:FD_ID, pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires pid != NULL

    requires dev_id in ws.subjects.devs
    requires fd_id in ws.subjects.devs[dev_id].fd_ids
        // Requirement: FD must be owned by the device <dev_id>

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].td_ids && 
                    id != k.subjects.devs[dev_id].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos
    requires ws.subjects.devs[dev_id].hcoded_td_id in ws.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_id.sid, pid, DMStateToState(ws'))
        // Requirement: ws' is the activation of the device <dev_id>

    ensures DM_ObjPID(ws'.objects, fd_id.oid) == pid
    ensures DM_IsFDClearVal(ws'.objects, fd_id)
    ensures fd_id in ws'.objects.active_fds
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_FDIDs(
    ws:DM_State, ws':DM_State, dev_id:Dev_ID, pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires pid != NULL

    requires dev_id in ws.subjects.devs

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].td_ids && 
                    id != k.subjects.devs[dev_id].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos
    requires ws.subjects.devs[dev_id].hcoded_td_id in ws.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_id.sid, pid, DMStateToState(ws'))
        // Requirement: ws' is the activation of the device <dev_id>

    ensures var dev_fds := ws.subjects.devs[dev_id].fd_ids;
            (MapGetKeys(ws'.objects.active_fds) == MapGetKeys(ws.objects.active_fds) + dev_fds) &&
            (ws'.objects.inactive_fds == ws.objects.inactive_fds - dev_fds)
        // Properties of object IDs
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_DOs(
    ws:DM_State, ws':DM_State, dev_id:Dev_ID, do_id:DO_ID, pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires pid != NULL

    requires dev_id in ws.subjects.devs
    requires do_id in ws.subjects.devs[dev_id].do_ids
        // Requirement: DO must be owned by the device <dev_id>

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].td_ids && 
                    id != k.subjects.devs[dev_id].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos
    requires ws.subjects.devs[dev_id].hcoded_td_id in ws.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_id.sid, pid, DMStateToState(ws'))
        // Requirement: ws' is the activation of the device <dev_id>

    ensures DM_ObjPID(ws'.objects, do_id.oid) == pid
    ensures DM_IsDOClearVal(ws'.objects, do_id)
    ensures do_id in ws'.objects.active_dos
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_DOIDs(
    ws:DM_State, ws':DM_State, dev_id:Dev_ID, pid:Partition_ID
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires pid != NULL

    requires dev_id in ws.subjects.devs

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].td_ids && 
                    id != k.subjects.devs[dev_id].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos
    requires ws.subjects.devs[dev_id].hcoded_td_id in ws.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_id.sid, pid, DMStateToState(ws'))
        // Requirement: ws' is the activation of the device <dev_id>

    ensures var dev_dos := ws.subjects.devs[dev_id].do_ids;
            (MapGetKeys(ws'.objects.active_dos) == MapGetKeys(ws.objects.active_dos) + dev_dos) &&
            (ws'.objects.inactive_dos == ws.objects.inactive_dos - dev_dos)
        // Properties of object IDs
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property1(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    ensures var dev_ids_set := SeqToSet(dev_ids);
            var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
            var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;

            (MapGetKeys(last_ws.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds) + dev_non_hcoded_td_ids)  &&
            (MapGetKeys(last_ws.objects.active_fds) == MapGetKeys(ws.objects.active_fds) + dev_fds) &&
            (MapGetKeys(last_ws.objects.active_dos) == MapGetKeys(ws.objects.active_dos) + dev_dos) &&
            (last_ws.objects.inactive_non_hcoded_tds == ws.objects.inactive_non_hcoded_tds - dev_non_hcoded_td_ids) &&
            (last_ws.objects.inactive_fds == ws.objects.inactive_fds - dev_fds) &&
            (last_ws.objects.inactive_dos == ws.objects.inactive_dos - dev_dos) &&
            MapGetKeys(last_ws.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds)
        // Property 1 used in Lemma_WSD_DevActivate_Multi_ProveProperty11
    ensures var dev_ids_set := SeqToSet(dev_ids);
            var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
            var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
            P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
                ==> P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1(ws, last_ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    var next_dev_ids := dev_ids[1..];
    var next_dev_ids_set := SeqToSet(next_dev_ids);

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Apply(ws', last_ws, next_dev_ids_set, pid);
    var next_dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws', next_dev_ids_set);
    var next_dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws', next_dev_ids_set);
    var next_dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws', next_dev_ids_set);
    var next_dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws', next_dev_ids_set);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert next_dev_tds == WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    assert next_dev_fds == WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    assert next_dev_dos == WSD_DOsOwnedByDevs(ws, next_dev_ids_set);
    assert next_dev_hcoded_td_ids == WSD_HCodedTDsOwnedByDevs(ws, next_dev_ids_set); 

    var next_dev_non_hcoded_td_ids := next_dev_tds - next_dev_hcoded_td_ids;
    assert MapGetKeys(last_ws.objects.active_non_hcoded_tds) == MapGetKeys(ws'.objects.active_non_hcoded_tds) + next_dev_non_hcoded_td_ids;
    assert MapGetKeys(last_ws.objects.hcoded_tds) == MapGetKeys(ws'.objects.hcoded_tds);

    // Prove properties of <dev0_id>
    var dev0_id := dev_ids[0];
    var dev0_tds := ws.subjects.devs[dev0_id].td_ids;
    var dev0_hcoded_td_ids := {ws.subjects.devs[dev0_id].hcoded_td_id};
    var dev0_non_hcoded_td_ids := dev0_tds - dev0_hcoded_td_ids;

    Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws, dev0_id);
    assert dev0_tds == WSD_TDsOwnedByDevs(ws, {dev0_id});
    assert dev0_hcoded_td_ids == WSD_HCodedTDsOwnedByDevs(ws, {dev0_id});

    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
    Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_TDIDs(ws, ws', dev0_id, pid);
    assert MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds) + dev0_non_hcoded_td_ids;

    // Prove objects of <dev_ids> == objects of <dev0_id> + objects of <next_dev_ids>
    var dev_ids_set := SeqToSet(dev_ids);
    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
    var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;

    Lemma_WSD_ObjsOwnedByDevs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev0_id);
    assert dev_tds == next_dev_tds + dev0_tds;
    assert dev_hcoded_td_ids == next_dev_hcoded_td_ids + dev0_hcoded_td_ids;

    //assume next_dev_tds * dev0_tds == {};
    //assume next_dev_tds * dev0_hcoded_td_ids == {};
    //assume next_dev_hcoded_td_ids * dev0_tds == {};
    //Lemma_DevActivate_Multi_SetPlus_Property(
    //    dev_non_hcoded_td_ids, dev_tds, dev_hcoded_td_ids, next_dev_tds, dev0_tds, next_dev_hcoded_td_ids, dev0_hcoded_td_ids);
    //assert dev_non_hcoded_td_ids == next_dev_non_hcoded_td_ids + dev0_non_hcoded_td_ids;


    assume (MapGetKeys(last_ws.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds) + dev_non_hcoded_td_ids)  &&
            (MapGetKeys(last_ws.objects.active_fds) == MapGetKeys(ws.objects.active_fds) + dev_fds) &&
            (MapGetKeys(last_ws.objects.active_dos) == MapGetKeys(ws.objects.active_dos) + dev_dos) &&
            (last_ws.objects.inactive_non_hcoded_tds == ws.objects.inactive_non_hcoded_tds - dev_non_hcoded_td_ids) &&
            (last_ws.objects.inactive_fds == ws.objects.inactive_fds - dev_fds) &&
            (last_ws.objects.inactive_dos == ws.objects.inactive_dos - dev_dos) &&
            MapGetKeys(last_ws.objects.hcoded_tds) == MapGetKeys(ws.objects.hcoded_tds);

    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1();
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    requires var dev_ids_set := SeqToSet(dev_ids);
            var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
            var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
            P_WSD_DevActivate_Multi_SubjObjModifications_Objs_PreConditions(ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid) &&
            P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1(ws, last_ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)

    ensures var dev_ids_set := SeqToSet(dev_ids);
            var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
            var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;
            P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part2(ws, last_ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid)
{
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner(ws, ws', last_ws, dev_ids, pid);

    var dev_ids_set := SeqToSet(dev_ids);
    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids_set);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids_set);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids_set);
    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
    var dev_non_hcoded_td_ids := dev_tds - dev_hcoded_td_ids;

    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part1();
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Objs_Part2_Prove(ws, last_ws, dev_tds, dev_fds, dev_dos, dev_hcoded_td_ids, pid);
}

lemma Lemma_WSD_DevActivate_Multi_DevIDsLargerThan1_ProvePreConditionsForNextRun(
    ws:DM_State, ws':DM_State, pid:Partition_ID, 
    dev_ids:seq<Dev_ID>, next_dev_ids:seq<Dev_ID>
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)

    requires |dev_ids| > 0
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    requires forall i, j :: 0 <= i < |dev_ids| && 0 <= j < |dev_ids|
                ==> (i == j <==> dev_ids[i] == dev_ids[j])
        // Requirement: No duplicate device ID in <dev_ids>
    requires next_dev_ids == dev_ids[1..]
 
    requires pid != NULL

    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    ensures forall id :: id in next_dev_ids ==> id in ws.subjects.devs
    ensures forall id :: id in next_dev_ids 
                ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)
    ensures forall i, j :: 0 <= i < |next_dev_ids| && 0 <= j < |next_dev_ids|
                ==> (i == j <==> next_dev_ids[i] == next_dev_ids[j]);
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
    forall id | id in next_dev_ids 
        ensures DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)
    {
        assert DM_SubjPID(ws'.subjects, id.sid) == ws'.subjects.devs[id].pid;
        assert DM_SubjPID(ws.subjects, id.sid) == ws.subjects.devs[id].pid;
        assert ws.subjects.devs[id] == ws'.subjects.devs[id];
    }
}

lemma Lemma_WSD_DevActivate_Multi_DevIDsLargerThan1_ProveP_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(
    ws:DM_State, ws':DM_State, pid:Partition_ID, 
    dev_ids:seq<Dev_ID>, next_dev_ids:seq<Dev_ID>
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)

    requires |dev_ids| > 0
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    requires forall i, j :: 0 <= i < |dev_ids| && 0 <= j < |dev_ids|
                ==> (i == j <==> dev_ids[i] == dev_ids[j])
        // Requirement: No duplicate device ID in <dev_ids>
    requires next_dev_ids == dev_ids[1..]
 
    requires pid != NULL

    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires var k := DMStateToState(ws);
             k.subjects.devs[dev_ids[0]].hcoded_td_id in k.objects.hcoded_tds
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    ensures P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
}




//******** Private Lemmas of <Lemma_WSD_DevActivate_Multi_ProveProperty11> ********//
lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
         
    ensures forall id :: id in WSD_TDsOwnedByDevs(ws, SeqToSet(dev_ids)) &&
                    id !in WSD_HCodedTDsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> (id.oid in DM_AllObjsIDs(last_ws.objects) &&
                     id in last_ws.objects.active_non_hcoded_tds &&
                     DM_ObjPID(last_ws.objects, id.oid) == pid &&
                     DM_IsTDClearVal(last_ws.objects, id))
    ensures forall id :: id in WSD_TDsOwnedByDevs(ws, SeqToSet(dev_ids)) &&
                    id in WSD_HCodedTDsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> (id.oid in DM_AllObjsIDs(last_ws.objects) &&
                     id in last_ws.objects.hcoded_tds &&
                     DM_ObjPID(last_ws.objects, id.oid) == pid &&
                     last_ws.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val)
    ensures forall id :: id in WSD_FDsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> (id in last_ws.objects.active_fds &&
                     DM_ObjPID(last_ws.objects, id.oid) == pid &&
                     DM_IsFDClearVal(last_ws.objects, id))
    ensures forall id :: id in WSD_DOsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> (id in last_ws.objects.active_dos &&
                     DM_ObjPID(last_ws.objects, id.oid) == pid &&
                     DM_IsDOClearVal(last_ws.objects, id))
        // Property 2 used in Lemma_WSD_DevActivate_Multi_ProveProperty11
{
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner_TDs(ws, ws', last_ws, dev_ids, pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner_HCodedTDs(ws, ws', last_ws, dev_ids, pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner_FDs(ws, ws', last_ws, dev_ids, pid);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner_DOs(ws, ws', last_ws, dev_ids, pid);
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner_TDs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    //requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
         
    ensures forall id :: id in WSD_TDsOwnedByDevs(ws, SeqToSet(dev_ids)) &&
                    id !in WSD_HCodedTDsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> (id.oid in DM_AllObjsIDs(last_ws.objects) &&
                     id in last_ws.objects.active_non_hcoded_tds &&
                     DM_ObjPID(last_ws.objects, id.oid) == pid &&
                     DM_IsTDClearVal(last_ws.objects, id))
        // Property 2 used in Lemma_WSD_DevActivate_Multi_ProveProperty11
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    var ws_devs_tds := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_tds := WSD_TDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_fds := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_fds := WSD_FDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_dos := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_dos := WSD_DOsOwnedByDevs(ws', next_dev_ids_set);
    
    Lemma_WSD_ObjsOwnedByDevs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert ws_devs_tds == ws'_devs_tds;
    assert ws_devs_fds == ws'_devs_fds;
    assert ws_devs_dos == ws'_devs_dos;

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    assert P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, next_dev_ids_set, pid);
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();

    forall id | id in WSD_TDsOwnedByDevs(ws, dev_ids_set) &&
            id !in WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set)
        ensures id.oid in DM_AllObjsIDs(last_ws.objects)
        ensures id in last_ws.objects.active_non_hcoded_tds
        ensures DM_ObjPID(last_ws.objects, id.oid) == pid
        ensures DM_IsTDClearVal(last_ws.objects, id)
    {
        assert id in ws_devs_tds || id in ws.subjects.devs[dev_ids[0]].td_ids;
        
        if(id in ws_devs_tds)
        {
            assert id in ws'_devs_tds;
            Lemma_WSD_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs_TDs(ws', last_ws, dev_ids, pid, id);
            assert id.oid in DM_AllObjsIDs(last_ws.objects);
            assert id in last_ws.objects.active_non_hcoded_tds;
            assert DM_ObjPID(last_ws.objects, id.oid) == pid;
            assert DM_IsTDClearVal(last_ws.objects, id);
        }
        else
        {
            Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_TDs(ws, ws', last_ws, dev_ids, id, pid);
        }
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner_HCodedTDs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    //requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
         
    ensures forall id :: id in WSD_TDsOwnedByDevs(ws, SeqToSet(dev_ids)) &&
                    id in WSD_HCodedTDsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> (id.oid in DM_AllObjsIDs(last_ws.objects) &&
                     id in last_ws.objects.hcoded_tds &&
                     DM_ObjPID(last_ws.objects, id.oid) == pid &&
                     last_ws.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val)
        // Property 2 used in Lemma_WSD_DevActivate_Multi_ProveProperty11
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    var ws_devs_tds := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_tds := WSD_TDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_fds := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_fds := WSD_FDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_dos := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_dos := WSD_DOsOwnedByDevs(ws', next_dev_ids_set);
    
    Lemma_WSD_ObjsOwnedByDevs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert ws_devs_tds == ws'_devs_tds;
    assert ws_devs_fds == ws'_devs_fds;
    assert ws_devs_dos == ws'_devs_dos;

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    assert P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, next_dev_ids_set, pid);
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();

    forall id | id in WSD_TDsOwnedByDevs(ws, dev_ids_set) &&
            id in WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set)
        ensures id.oid in DM_AllObjsIDs(last_ws.objects)
        ensures id in last_ws.objects.hcoded_tds
        ensures DM_ObjPID(last_ws.objects, id.oid) == pid
        ensures last_ws.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val
    {
        assert id in ws_devs_tds || id in ws.subjects.devs[dev_ids[0]].td_ids;
        
        if(id in ws_devs_tds)
        {
            assert id in ws'_devs_tds;
            Lemma_WSD_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs_TDs(ws', last_ws, dev_ids, pid, id);
            assert DM_ObjPID(last_ws.objects, id.oid) == pid;
            assert last_ws.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val;
        }
        else
        {
            Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_HCodedTDs(ws, ws', last_ws, dev_ids, pid);
        }
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner_FDs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
         
    ensures forall id :: id in WSD_FDsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> (id in last_ws.objects.active_fds &&
                     DM_ObjPID(last_ws.objects, id.oid) == pid &&
                     DM_IsFDClearVal(last_ws.objects, id))
        // Property 2 used in Lemma_WSD_DevActivate_Multi_ProveProperty11
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    var ws_devs_tds := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_tds := WSD_TDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_fds := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_fds := WSD_FDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_dos := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_dos := WSD_DOsOwnedByDevs(ws', next_dev_ids_set);
    
    Lemma_WSD_ObjsOwnedByDevs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert ws_devs_tds == ws'_devs_tds;
    assert ws_devs_fds == ws'_devs_fds;
    assert ws_devs_dos == ws'_devs_dos;

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    assert P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, next_dev_ids_set, pid);
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();

    forall id | id in WSD_FDsOwnedByDevs(ws, dev_ids_set) 
        ensures id in last_ws.objects.active_fds
        ensures DM_ObjPID(last_ws.objects, id.oid) == pid
        ensures DM_IsFDClearVal(last_ws.objects, id)
    {
        assert id in ws_devs_fds || id in ws.subjects.devs[dev_ids[0]].fd_ids;
        
        if(id in ws_devs_fds)
        {
            assert id in ws'_devs_fds;
            Lemma_WSD_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs_FDs(ws', last_ws, dev_ids, pid, id);
            assert DM_ObjPID(last_ws.objects, id.oid) == pid;
            assert DM_IsFDClearVal(last_ws.objects, id);
        }
        else
        {
            Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_FDs(ws, ws', last_ws, dev_ids, pid);
        }
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Inner_DOs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
         
    ensures forall id :: id in WSD_DOsOwnedByDevs(ws, SeqToSet(dev_ids))
                ==> (id in last_ws.objects.active_dos &&
                     DM_ObjPID(last_ws.objects, id.oid) == pid &&
                     DM_IsDOClearVal(last_ws.objects, id))
        // Property 2 used in Lemma_WSD_DevActivate_Multi_ProveProperty11
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    var ws_devs_tds := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_tds := WSD_TDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_fds := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_fds := WSD_FDsOwnedByDevs(ws', next_dev_ids_set);
    var ws_devs_dos := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);
    var ws'_devs_dos := WSD_DOsOwnedByDevs(ws', next_dev_ids_set);
    
    Lemma_WSD_ObjsOwnedByDevs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_WSD_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert ws_devs_tds == ws'_devs_tds;
    assert ws_devs_fds == ws'_devs_fds;
    assert ws_devs_dos == ws'_devs_dos;

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    assert P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, next_dev_ids_set, pid);
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
    reveal P_WSD_DevActivate_Multi_SubjObjModifications_Objs();

    forall id | id in WSD_DOsOwnedByDevs(ws, dev_ids_set) 
        ensures id in last_ws.objects.active_dos
        ensures DM_ObjPID(last_ws.objects, id.oid) == pid
        ensures DM_IsDOClearVal(last_ws.objects, id)
    {
        assert id in ws_devs_dos || id in ws.subjects.devs[dev_ids[0]].do_ids;
        
        if(id in ws_devs_dos)
        {
            assert id in ws'_devs_dos;
            Lemma_WSD_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs_DOs(ws', last_ws, dev_ids, pid, id);
            assert DM_ObjPID(last_ws.objects, id.oid) == pid;
            assert DM_IsDOClearVal(last_ws.objects, id);
        }
        else
        {
            Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_DOs(ws, ws', last_ws, dev_ids, pid);
        }
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_TDs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, td_id:TD_ID,
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    requires var dev0_id := dev_ids[0];
             var dev_ids_set := SeqToSet(dev_ids);
             td_id in ws.subjects.devs[dev0_id].td_ids &&
             td_id !in WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set)

    ensures var dev0_id := dev_ids[0];
            (td_id.oid in DM_AllObjsIDs(last_ws.objects)) &&
            (td_id in last_ws.objects.active_non_hcoded_tds) &&
            (DM_ObjPID(last_ws.objects, td_id.oid) == pid) &&
            (DM_IsTDClearVal(last_ws.objects, td_id))
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_TDs_Inner(ws, ws', last_ws, dev_ids, pid);
}

// [NOTE] Needs 70s to verify
lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_TDs_Inner(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].td_ids &&
                    id !in DM_AllHCodedTDIDs(ws.subjects)
                ==> id.oid in DM_AllObjsIDs(last_ws.objects) &&
                    id in last_ws.objects.active_non_hcoded_tds
    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].td_ids &&
                    id !in DM_AllHCodedTDIDs(ws.subjects)
                ==> DM_ObjPID(last_ws.objects, id.oid) == pid &&
                    DM_IsTDClearVal(last_ws.objects, id)
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);

    var dev0_id := dev_ids[0];
    var dev_tds := ws.subjects.devs[dev0_id].td_ids;
    var dev_hcoded_td_ids := {ws.subjects.devs[dev0_id].hcoded_td_id};

    // Prove dev_tds == WSD_TDsOwnedByDevs(ws', {dev0_id}) and dev_hcoded_td_ids == WSD_HCodedTDsOwnedByDevs(ws', {dev0_id})
    assert dev_tds == ws'.subjects.devs[dev0_id].td_ids;
    Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws', dev0_id);
    assert dev_tds == WSD_TDsOwnedByDevs(ws', {dev0_id});
    assert dev_hcoded_td_ids == WSD_HCodedTDsOwnedByDevs(ws', {dev0_id});

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Apply(ws', last_ws, next_dev_ids_set, pid);

    forall id | id in ws.subjects.devs[dev_ids[0]].td_ids &&
                id !in DM_AllHCodedTDIDs(ws.subjects)
        ensures id.oid in DM_AllObjsIDs(last_ws.objects)
        ensures id in last_ws.objects.active_non_hcoded_tds
        ensures DM_ObjPID(last_ws.objects, id.oid) == pid
        ensures DM_IsTDClearVal(last_ws.objects, id)
    {
        assert id in dev_tds;
        assert id !in dev_hcoded_td_ids;

        Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_TDs(ws, ws', dev_ids[0], id, pid);
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_HCodedTDs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].td_ids &&
                    id in DM_AllHCodedTDIDs(ws.subjects)
                ==> id.oid in DM_AllObjsIDs(last_ws.objects) &&
                    id in last_ws.objects.hcoded_tds
    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].td_ids &&
                    id in DM_AllHCodedTDIDs(ws.subjects)
                ==> DM_ObjPID(last_ws.objects, id.oid) == pid &&
                    last_ws.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_HCodedTDs_Inner(ws, ws', last_ws, dev_ids, pid);
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_HCodedTDs_Inner(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].td_ids &&
                    id in DM_AllHCodedTDIDs(ws.subjects)
                ==> id.oid in DM_AllObjsIDs(last_ws.objects) &&
                    id in last_ws.objects.hcoded_tds
    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].td_ids &&
                    id in DM_AllHCodedTDIDs(ws.subjects)
                ==> DM_ObjPID(last_ws.objects, id.oid) == pid &&
                    last_ws.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);

    var dev0_id := dev_ids[0];
    var dev_tds := ws.subjects.devs[dev0_id].td_ids;
    var dev_hcoded_td_ids := {ws.subjects.devs[dev0_id].hcoded_td_id};

    // Prove dev_tds == WSD_TDsOwnedByDevs(ws', {dev0_id}) and dev_hcoded_td_ids == WSD_HCodedTDsOwnedByDevs(ws', {dev0_id})
    assert dev_tds == ws'.subjects.devs[dev0_id].td_ids;
    Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws', dev0_id);
    assert dev_tds == WSD_TDsOwnedByDevs(ws', {dev0_id});
    assert dev_hcoded_td_ids == WSD_HCodedTDsOwnedByDevs(ws', {dev0_id});

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Apply(ws', last_ws, next_dev_ids_set, pid);

    forall id | id in ws.subjects.devs[dev_ids[0]].td_ids &&
                id in DM_AllHCodedTDIDs(ws.subjects)
        ensures id.oid in DM_AllObjsIDs(last_ws.objects)
        ensures id in last_ws.objects.hcoded_tds
        ensures DM_ObjPID(last_ws.objects, id.oid) == pid
        ensures last_ws.objects.hcoded_tds[id].val == ws.objects.hcoded_tds[id].val
    {
        assert id in dev_tds;
        assert id in dev_hcoded_td_ids;

        Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_HCodedTDs(ws, ws', dev_ids[0], id, pid);
    }
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_FDs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].fd_ids
                ==> id.oid in DM_AllObjsIDs(last_ws.objects) &&
                    id in last_ws.objects.active_fds
    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].fd_ids
                ==> DM_ObjPID(last_ws.objects, id.oid) == pid &&
                    DM_IsFDClearVal(last_ws.objects, id)
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_FDs_Inner(ws, ws', last_ws, dev_ids, pid);
}

lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_DOs(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', dev_ids[0], pid)
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].do_ids
                ==> id.oid in DM_AllObjsIDs(last_ws.objects) &&
                    id in last_ws.objects.active_dos
    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].do_ids
                ==> DM_ObjPID(last_ws.objects, id.oid) == pid &&
                    DM_IsDOClearVal(last_ws.objects, id)
{
    reveal P_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0();
    Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_DOs_Inner(ws, ws', last_ws, dev_ids, pid);
}

// [NOTE] Needs 50s to verify
lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_FDs_Inner(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].fd_ids
                ==> id.oid in DM_AllObjsIDs(last_ws.objects) &&
                    id in last_ws.objects.active_fds
    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].fd_ids
                ==> DM_ObjPID(last_ws.objects, id.oid) == pid &&
                    DM_IsFDClearVal(last_ws.objects, id)
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);

    var dev0_id := dev_ids[0];
    var dev_fds := ws.subjects.devs[dev0_id].fd_ids;

    // Prove dev_fds == WSD_FDsOwnedByDevs(ws', {dev0_id})
    assert dev_fds == ws'.subjects.devs[dev0_id].fd_ids;
    Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws', dev0_id);
    assert dev_fds == WSD_FDsOwnedByDevs(ws', {dev0_id});

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Apply(ws', last_ws, next_dev_ids_set, pid);

    forall id | id in ws.subjects.devs[dev_ids[0]].fd_ids
        ensures id.oid in DM_AllObjsIDs(last_ws.objects)
        ensures id in last_ws.objects.active_fds
        ensures DM_ObjPID(last_ws.objects, id.oid) == pid
        ensures DM_IsFDClearVal(last_ws.objects, id)
    {
        assert id in dev_fds;

        Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_FDs(ws, ws', dev_ids[0], id, pid);
    }
}

// [NOTE] Needs 50s to verify
lemma Lemma_WSD_DevActivate_Multi_ProveProperty11_Property2_Dev0_DOs_Inner(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires DM_IsValidState_Objects(ws')
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= AllDOIDs(DMStateToState(ws).objects)

    requires DM_IsSecureOps(ws, ws')
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].td_ids && 
                    id != k.subjects.devs[dev_ids[0]].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].fd_ids ==> id in k.objects.inactive_fds
    requires var k := DMStateToState(ws);
             forall id :: id in k.subjects.devs[dev_ids[0]].do_ids ==> id in k.objects.inactive_dos
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion

    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].do_ids
                ==> id.oid in DM_AllObjsIDs(last_ws.objects) &&
                    id in last_ws.objects.active_dos
    ensures var dev0_id := dev_ids[0];
            forall id :: id in ws.subjects.devs[dev_ids[0]].do_ids
                ==> DM_ObjPID(last_ws.objects, id.oid) == pid &&
                    DM_IsDOClearVal(last_ws.objects, id)
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);

    var dev0_id := dev_ids[0];
    var dev_dos := ws.subjects.devs[dev0_id].do_ids;

    // Prove dev_dos == WSD_FDsOwnedByDevs(ws', {dev0_id})
    assert dev_dos == ws'.subjects.devs[dev0_id].do_ids;
    Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws', dev0_id);
    assert dev_dos == WSD_DOsOwnedByDevs(ws', {dev0_id});

    // Use P_WSD_DevActivate_Multi_SubjObjModifications
    Lemma_P_WSD_DevActivate_Multi_SubjObjModifications_Apply(ws', last_ws, next_dev_ids_set, pid);

    forall id | id in ws.subjects.devs[dev_ids[0]].do_ids
        ensures id.oid in DM_AllObjsIDs(last_ws.objects)
        ensures id in last_ws.objects.active_dos
        ensures DM_ObjPID(last_ws.objects, id.oid) == pid
        ensures DM_IsDOClearVal(last_ws.objects, id)
    {
        assert id in dev_dos;

        Lemma_WSD_DevActivate_Multi_ApplyP_DevActivate_ModificationToState_DOs(ws, ws', dev_ids[0], id, pid);
    }
}

lemma Lemma_DevActivate_Multi_SetPlus_Property<T>(a:set<T>, b:set<T>, c:set<T>, b1:set<T>, b2:set<T>, c1:set<T>, c2:set<T>)
    requires a == b - c
    requires b == b1 + b2
    requires c == c1 + c2

    requires b1 * b2 == {} 
    requires b1 * c2 == {} 
    requires c1 * b2 == {}

    ensures var d := b1 - c1;
            var e := b2 - c2;
            a == d + e
{
    var d := b1 - c1;
    var e := b2 - c2;

    assert a == b - c;
    assert a == (b1 + b2) - (c1 + c2);

    assert a == b1 + b2 - c1 - c2;
    //assert c <= b;

    Lemma_SetMinusProperty2(b1, b2, c1);
    assert a == b1 - c1 + b2 - c2;
    Lemma_SetMinusProperty3(d, b2, c2);
    assert a == d + (b2 - c2);
    assert a == d + e;
}