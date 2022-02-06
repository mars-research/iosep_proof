include "DevActivate_Multi.dfy"

//******** Axioms ********//
// Axiom: In <WSD_DevActivate_Multi>, prove Property 12 holds for the next iteration
lemma {:axiom} Lemma_WSD_DevActivate_Multi_NextWSD_DevActivate_Multi(
    ws:DM_State,
    dev_ids:seq<Dev_ID>, // ID of the devices to be deactivated
    pid:Partition_ID, // ID of the target partition,
    ws':DM_State
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsValidState(ws')
    requires pid != NULL

    requires forall id :: id in dev_ids 
                ==> DM_IsDevID(ws.subjects, id)
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs

    requires (ws', true) == DM_DevActivate_InnerFunc(ws, dev_ids[0].sid, pid)

    requires P_WSD_DevActivate_Multi_ConditionForReturnTrue(ws, SeqToSet(dev_ids), pid)
         
    ensures var next_dev_ids := dev_ids[1..];
            P_WSD_DevActivate_Multi_ConditionForReturnTrue(ws', SeqToSet(next_dev_ids), pid)
        // Property 12 holds in the next iteration




//******** Functions ********//
// We need to put this method in a standalone file, or Dafny v2.3 fails to verify it
// [NOTE] Needs 200s to verify
// [TODO] Fix this issue
method {:timeLimitMultiplier 20} WSD_DevActivate_Multi(
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

    ensures P_WSD_DevActivate_Multi_ConditionForReturnTrue(ws, SeqToSet(dev_ids), pid) ==> d
        // Property 12
        // [TODO] Prove it

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

        if(P_WSD_DevActivate_Multi_ConditionForReturnTrue(ws, SeqToSet(dev_ids), pid))
        {
            Lemma_WSD_DevActivate_Multi_Current(ws, dev_ids, pid, ws');
            assert ws_d;
        }

        if(!ws_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}

        reveal P_WSD_DevActivate_Multi_SubjObjModifications_Subjs();
        var next_dev_ids := dev_ids[1..];
        Lemma_WSD_DevActivate_Multi_DevIDsLargerThan1_ProveP_WSD_DevActivate_Multi_P_DevActivate_ModificationToState_ForDev0(ws, ws', pid, dev_ids, next_dev_ids);
        Lemma_WSD_DevActivate_Multi_DevIDsLargerThan1_ProvePreConditionsForNextRun(ws, ws', pid, dev_ids, next_dev_ids);
        var next_t, detailed_next_t, next_last_ws, next_d := WSD_DevActivate_Multi(ws', next_dev_ids, pid);

        if(P_WSD_DevActivate_Multi_ConditionForReturnTrue(ws, SeqToSet(dev_ids), pid))
        {
            Lemma_WSD_DevActivate_Multi_NextWSD_DevActivate_Multi(ws, dev_ids, pid, ws');
            assert next_d; // [TODO] Prove it
        }

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
            Lemma_WSD_DevActivate_Multi_ProveProperty3_Summary(ws, dev_ids, next_dev_ids, pid, t, next_t);

            // Prove property 4
            ghost var result := ConvertTraceToDetailedTrace(next_t);
            assert detailed_next_t == result.0;
            ghost var status := result.1;

            assert status == true;

            t_detailed := DM_Trace_Detailed([ws] + detailed_next_t.states, [op] + detailed_next_t.ops);

            assert DM_CalcNewState(ws, op) == (ws', ws_d);
            Lemma_ValidDetailedTraceInsertValidStateAndChainedAtFirst(detailed_next_t, ws, op, t_detailed);
            assert DM_DetailedTrace_IsValidTrace(t_detailed);

            Lemma_WSD_DevActivate_Multi_ProveProperty4_Summary(ws, op, t, t_detailed, next_t, detailed_next_t, dev_id, pid);
            assert t == ConvertDetailedTraceToTrace(t_detailed);
            assert DM_IsValidTrace(t);

            // Prove property 5
            ghost var t_calc_new_states := DM_CalcNewStates(t);
            assert t_calc_new_states == t_detailed.states;
            Lemma_Seq_LastElemIsUnchanged_IfInsertElemAtFirst(t_detailed.states, detailed_next_t.states, ws);
            assert SeqLastElem(t_detailed.states) == SeqLastElem(detailed_next_t.states);
            assert next_last_ws == SeqLastElem(detailed_next_t.states);
            assert SeqLastElem(t_detailed.states) == last_ws;
            assert SeqLastElem(t_calc_new_states) == last_ws;

            Lemma_WSD_DevActivate_Multi_ProveProperty5_Summary(t, t_calc_new_states, t_detailed, last_ws);
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
}

predicate {:opaque} P_WSD_DevActivate_Multi_ConditionForReturnTrue(
    ws:DM_State,
    dev_ids:set<Dev_ID>, // ID of the devices to be deactivated
    pid:Partition_ID // ID of the target partition
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_DevsActivateCond(ws)
    requires forall id :: id in dev_ids 
                ==> DM_IsDevID(ws.subjects, id)
{
    (pid in ws.pids) &&
    (forall id :: id in dev_ids
        ==> DM_SubjPID(ws.subjects, id.sid) == NULL
    ) &&
    (pid == ws.red_pid 
        ==> (forall id :: id in dev_ids
                ==> TryActivateDevInRed(ws, id)) 
    ) &&
    (pid != ws.red_pid 
        ==> (forall id :: id in dev_ids
                ==> TryActivateDevInGreen(ws, id)) 
    ) &&
    (forall dev_id, hcoded_td_id, td_id :: dev_id in dev_ids &&
            hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id &&
            td_id in ws.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
        ==> W !in ws.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds[td_id].amodes
    ) &&

    (true)
}

lemma Lemma_P_WSD_DevActivate_Multi_ConditionForReturnTrue_Prove(
    ws:DM_State,
    dev_ids:set<Dev_ID>, // ID of the devices to be deactivated
    pid:Partition_ID // ID of the target partition
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_DevsActivateCond(ws)
    requires forall id :: id in dev_ids 
                ==> DM_IsDevID(ws.subjects, id)

    requires pid == ws.red_pid
    requires pid in ws.pids

    requires forall id :: id in dev_ids
                ==> DM_SubjPID(ws.subjects, id.sid) == NULL
    requires (pid == ws.red_pid 
                ==> (forall id :: id in dev_ids
                        ==> TryActivateDevInRed(ws, id)) 
            ) &&
            (pid != ws.red_pid 
                ==> (forall id :: id in dev_ids
                        ==> TryActivateDevInGreen(ws, id)) 
            )

    requires forall dev_id, hcoded_td_id, td_id :: dev_id in dev_ids &&
                    hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id &&
                    td_id in ws.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
                ==> W !in ws.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds[td_id].amodes
    
    ensures P_WSD_DevActivate_Multi_ConditionForReturnTrue(ws, dev_ids, pid)
{
    reveal P_WSD_DevActivate_Multi_ConditionForReturnTrue();
}

lemma Lemma_WSD_DevActivate_Multi_Current(
    ws:DM_State,
    dev_ids:seq<Dev_ID>, // ID of the devices to be deactivated
    pid:Partition_ID, // ID of the target partition,
    ws':DM_State
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsValidState(ws')
    requires pid != NULL

    requires forall id :: id in dev_ids 
                ==> DM_IsDevID(ws.subjects, id)
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs

    requires DM_DevActivate_InnerFunc(ws, dev_ids[0].sid, pid).0 == ws'

    requires P_WSD_DevActivate_Multi_ConditionForReturnTrue(ws, SeqToSet(dev_ids), pid)
         
    ensures DM_DevActivate_InnerFunc(ws, dev_ids[0].sid, pid).1 == true
        // Property 12 holds in the next iteration
{
    reveal P_WSD_DevActivate_Multi_ConditionForReturnTrue();
}