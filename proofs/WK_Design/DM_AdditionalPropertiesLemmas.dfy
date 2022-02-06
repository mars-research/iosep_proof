include "../DetailedModel/SecurityProperties.dfy"

datatype DM_Trace_Detailed = DM_Trace_Detailed(states:seq<DM_State>, ops:seq<DM_Op>)

predicate DM_DetailedTrace_IsValidTrace(t:DM_Trace_Detailed)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties
{
    (|t.states| == |t.ops| + 1) &&
    
    // First state must be a secure state
    (DM_IsValidState(t.states[0]) && DM_IsSecureState(t.states[0])) &&

    // Each state and op fulfills preconditions
    (forall i :: 0 <= i < |t.ops|
        ==> P_DM_OpsFulfillPreConditions(t.states[i], t.ops[i])) &&
    
    // States are chained together
    (forall i :: 0 <= i < |t.ops|
        ==> DM_CalcNewState(t.states[i], t.ops[i]).0 == t.states[i+1]) &&

    (forall i :: 0 <= i < |t.states|
        ==> DM_IsValidState(t.states[i]) && DM_IsSecureState(t.states[i])) &&
    (forall i :: 0 <= i < |t.ops|
        ==> DM_IsSecureOps(t.states[i], t.states[i+1])) &&

    (true)
}

function method ValidDMTrace_Concat(
    t1:DM_Trace, t2:DM_Trace
) : (t:DM_Trace)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(t1.ws0) && DM_IsSecureState(t1.ws0)
    requires DM_IsValidState(t2.ws0) && DM_IsSecureState(t2.ws0)
        // Requirement: The trace <t> starts from a secure state
    
    requires DM_IsValidTrace(t1)
    requires DM_IsValidTrace(t2)
    requires t2.ws0 == SeqLastElem(DM_CalcNewStates(t1))

    ensures t == DM_Trace(t1.ws0, t1.ops + t2.ops)
    ensures t.ops == t1.ops + t2.ops
    ensures DM_IsValidTrace(t)
    ensures DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
{
    var result := DM_Trace(t1.ws0, t1.ops + t2.ops);
    ghost var conv_result := ConvertTraceToDetailedTrace(t1);
    ghost var t1_detailed := conv_result.0;
    ghost var s := conv_result.1;
    assert s;
    
    ghost var conv_result2 := ConvertTraceToDetailedTrace(t2);
    ghost var t2_detailed := conv_result2.0;
    ghost var s2 := conv_result2.1;
    assert s2;

    assert t2_detailed.states[0] == SeqLastElem(t1_detailed.states);

    ghost var t_detailed := DM_Trace_Detailed(t1_detailed.states[..|t1_detailed.states|-1] + t2_detailed.states, t1_detailed.ops + t2_detailed.ops);
    Lemma_ValidDMTrace_Concat_ProveResultDetailedTraceIsValid(t1_detailed, t2_detailed, t_detailed);
    assert DM_DetailedTrace_IsValidTrace(t_detailed);

    assert ConvertDetailedTraceToTrace(t_detailed) == result;

    result
}

lemma Lemma_DMTraceConcat_IsConcatOfDMOps(
    t1_t2:DM_Trace, t1:DM_Trace, t2:DM_Trace, seq1:seq<DM_Op>, seq2:seq<DM_Op>
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(t1.ws0) && DM_IsSecureState(t1.ws0)
    requires DM_IsValidState(t2.ws0) && DM_IsSecureState(t2.ws0)
        // Requirement: The trace <t> starts from a secure state
    
    requires DM_IsValidTrace(t1)
    requires DM_IsValidTrace(t2)
    requires t2.ws0 == SeqLastElem(DM_CalcNewStates(t1))
    
    requires t1_t2 == ValidDMTrace_Concat(t1, t2)
    
    requires t1.ops == seq1
    requires t2.ops == seq2
    
    ensures t1_t2.ops == seq1 + seq2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ConcatFourOpSeq(
    t1_t2:DM_Trace, t3_t4:DM_Trace, t:DM_Trace,
    seq1:seq<DM_Op>, seq2:seq<DM_Op>, seq3:seq<DM_Op>, seq4:seq<DM_Op>
)
    requires t1_t2.ops == seq1 + seq2
    requires t3_t4.ops == seq3 + seq4

    requires t.ops == t1_t2.ops + t3_t4.ops

    ensures t.ops == seq1 + seq2 + seq3 + seq4
{
    // Dafny can automatically prove this lemma
}

function ConvertDetailedTraceToTrace(t:DM_Trace_Detailed) : (t2:DM_Trace)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires DM_DetailedTrace_IsValidTrace(t)

    ensures t2 == DM_Trace(t.states[0], t.ops)
    ensures DM_IsValidState(t2.ws0) && DM_IsSecureState(t2.ws0)
    ensures DM_IsValidTrace(t2)

    decreases |t.ops|
{
    if(|t.ops| == 0) then
        var ret := DM_Trace(t.states[0], []);
        assert DM_IsValidTrace(ret);
        ret
    else
        var ws := t.states[0];
        var op := t.ops[0];
        var step_t := DM_Trace_Detailed(t.states[1..], t.ops[1..]);
        var step_t2 := ConvertDetailedTraceToTrace(step_t);

        assert step_t2.ws0 == DM_CalcNewState(ws, op).0;

        var ret := DM_Trace(ws, t.ops);
        ret
}

// (needs 50s to verify)
function ConvertTraceToDetailedTrace(t:DM_Trace) : (result:(DM_Trace_Detailed, bool))
    requires |t.ops| >= 0
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties

    ensures DM_IsValidTrace(t) <==> result.1
        // Property: <result.1> is DM_IsValidTrace(t)

    ensures result.1 ==> result.0.ops == t.ops
    ensures result.1 ==> |result.0.states| == |result.0.ops| + 1
    ensures result.1 ==> result.0.states[0] == t.ws0
        
    ensures result.1 ==>
                (forall i :: 0 <= i < |result.0.states| - 1
                    ==> P_DM_OpsFulfillPreConditions(result.0.states[i], t.ops[i]))
    ensures result.1 ==>
                (forall i :: 0 <= i < |result.0.states| - 1
                    ==> result.0.states[i+1] == DM_CalcNewState(result.0.states[i], t.ops[i]).0)
        // Property: Properties needed by the following property
    ensures result.1 ==> DM_CalcNewStates(t) == result.0.states
        // Property: When ConvertTraceToDetailedTrace returns true,  
        // <result.0.states> equals to DM_CalcNewStates(t)
     
    ensures result.1 <==> DM_DetailedTrace_IsValidTrace(result.0)
        // Property: A detailed trace is valid, iff the corresponding
        // trace is valid 

    decreases |t.ops| 
{
    if(|t.ops| == 0) then
        var ret := (DM_Trace_Detailed([t.ws0], t.ops), true);
        assert DM_DetailedTrace_IsValidTrace(ret.0);
        ret
    else
        var b1 := P_DM_OpsFulfillPreConditions(t.ws0, t.ops[0]);
        if(!b1) then 
            (DM_Trace_Detailed([], []), false)
        else
            var ws1 := DM_CalcNewState(t.ws0, t.ops[0]).0; // Eval t.ops[0]
            var step_result := ConvertTraceToDetailedTrace(DM_Trace(ws1, t.ops[1..]));
            var result_1 := b1 && step_result.1;
            var result_0 := DM_Trace_Detailed([t.ws0] + step_result.0.states, [t.ops[0]] + step_result.0.ops);
            var ret := (result_0, result_1);
            
            if(ret.1) then
                Lemma_ConvertTraceToDetailedTrace_ProveDM_CalcNewStates(t, ret.0.states);
                assert DM_DetailedTrace_IsValidTrace(ret.0);
                ret
            else
                assert !DM_DetailedTrace_IsValidTrace(step_result.0);
                Lemma_DetailedTraceIsInvalid_IfDetailedSubTraceIsInvalid(step_result.0, ret.0);
                assert !DM_DetailedTrace_IsValidTrace(ret.0);
                (DM_Trace_Detailed([], []), false)
}

lemma Lemma_ValidDetailedTraceInsertValidStateAndChainedAtFirst(
    sub_trace:DM_Trace_Detailed, ws:DM_State, op:DM_Op, trace:DM_Trace_Detailed
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires trace == DM_Trace_Detailed([ws] + sub_trace.states, [op] + sub_trace.ops)
    requires DM_DetailedTrace_IsValidTrace(sub_trace)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires P_DM_OpsFulfillPreConditions(ws, op)
    requires DM_CalcNewState(ws, op).0 == sub_trace.states[0]
    requires DM_CalcNewState(ws, op).1 == true

    ensures DM_DetailedTrace_IsValidTrace(trace)
{
    forall i | 0 <= i < |trace.ops|
        ensures DM_CalcNewState(trace.states[i], trace.ops[i]).0 == trace.states[i+1]
    {
        if(i == 0)
        {
            assert trace.states[i] == ws;
            assert DM_CalcNewState(trace.states[i], trace.ops[i]).0 == trace.states[i+1];
        }
        else
        {
            assert trace.states[i] == sub_trace.states[i-1];
            assert trace.ops[i] == sub_trace.ops[i-1];
            
            assert DM_DetailedTrace_IsValidTrace(sub_trace);
            assert 0 <= i-1 < |sub_trace.ops|;
            assert P_DM_OpsFulfillPreConditions(sub_trace.states[i-1], sub_trace.ops[i-1]);

            assert P_DM_OpsFulfillPreConditions(trace.states[i], trace.ops[i]);
            assert DM_CalcNewState(trace.states[i], trace.ops[i]).0 == trace.states[i+1];
        }
    }
}

lemma Lemma_DM_ActiveObjsMustBeInActiveSet_FDs(dm:DM_State, fd_ids:set<FD_ID>)
    requires P_DMObjectsHasUniqueIDs(dm.objects)
    requires fd_ids <= DM_AllFDIDs(dm.objects)
    requires forall id :: id in fd_ids
                ==> DM_ObjPID(dm.objects, id.oid) != NULL

    ensures forall id :: id in fd_ids
                ==> id in dm.objects.active_fds
{
    reveal IsValidState_Objects_UniqueObjIDs();
}

lemma Lemma_DM_ActiveObjsMustBeInActiveSet_DOs(dm:DM_State, do_ids:set<DO_ID>)
    requires P_DMObjectsHasUniqueIDs(dm.objects)
    requires do_ids <= DM_AllDOIDs(dm.objects)
    requires forall id :: id in do_ids
                ==> DM_ObjPID(dm.objects, id.oid) != NULL

    ensures forall id :: id in do_ids
                ==> id in dm.objects.active_dos
{
    reveal IsValidState_Objects_UniqueObjIDs();
}




//******** Unchanged State Vars and Fields Between States ********//
predicate P_DMState_UnchangedStateVarsAndFields(s1:DM_State, s2:DM_State)
{
    (MapGetKeys(s1.subjects.drvs) == MapGetKeys(s2.subjects.drvs)) &&
    (MapGetKeys(s1.subjects.devs) == MapGetKeys(s2.subjects.devs)) &&
    (DM_AllTDIDs(s1.objects) == DM_AllTDIDs(s2.objects)) &&
    (DM_AllFDIDs(s1.objects) == DM_AllFDIDs(s2.objects)) &&
    (DM_AllDOIDs(s1.objects) == DM_AllDOIDs(s2.objects)) &&
    (s1.red_pid == s2.red_pid) &&

    (forall drv_id :: 
        drv_id in s2.subjects.drvs
        ==>
        (s2.subjects.drvs[drv_id].td_ids == s1.subjects.drvs[drv_id].td_ids) &&
        (s2.subjects.drvs[drv_id].fd_ids == s1.subjects.drvs[drv_id].fd_ids) &&
        (s2.subjects.drvs[drv_id].do_ids == s1.subjects.drvs[drv_id].do_ids)) &&

    (forall dev_id :: 
        dev_id in s2.subjects.devs
        ==>
        (s2.subjects.devs[dev_id].hcoded_td_id == s1.subjects.devs[dev_id].hcoded_td_id) &&
        (s2.subjects.devs[dev_id].td_ids == s1.subjects.devs[dev_id].td_ids) &&
        (s2.subjects.devs[dev_id].fd_ids == s1.subjects.devs[dev_id].fd_ids) &&
        (s2.subjects.devs[dev_id].do_ids == s1.subjects.devs[dev_id].do_ids)) &&

    (true)
}

lemma Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(s1:DM_State, s2:DM_State, s3:DM_State)
    requires P_DMState_UnchangedStateVarsAndFields(s1, s2)
    requires P_DMState_UnchangedStateVarsAndFields(s2, s3)
    
    ensures P_DMState_UnchangedStateVarsAndFields(s1, s3)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(states:seq<DM_State>, s1:DM_State, s2:DM_State)
    requires |states| > 0
    requires states[0] == s1
    requires SeqLastElem(states) == s2
    //requires states[|states|-1] == s2

    requires forall i :: 0 <= i < |states| ==> DM_IsValidState(states[i]) && DM_IsSecureState(states[i])
    requires forall i :: 0 <= i < |states| - 1 ==> DM_IsSecureOps(states[i], states[i+1])

    ensures P_DMState_UnchangedStateVarsAndFields(s1, s2)

    decreases |states|
{
    if(|states| == 1)
    {
        // Dafny can automatically prove this branch
    }
    else
    {
        var next_s2 := states[|states|-2];
        Lemma_WSD_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(states[..|states|-1], s1, next_s2);

        assert DM_IsSecureOps(next_s2, s2);
        Lemma_MapSameKeys(next_s2.subjects.drvs, s2.subjects.drvs);

        assert next_s2.red_pid == s2.red_pid;
    }
}

lemma Lemma_DM_TwoSubjectsCannotOwnSameObj(ws:DM_State)
    requires DM_IsValidState(ws)
    ensures forall o_id, s_id1, s_id2 :: 
                    s_id1 in DM_AllSubjsIDs(ws.subjects) && s_id2 in DM_AllSubjsIDs(ws.subjects) && 
                    DM_DoOwnObj(ws.subjects, s_id1, o_id) && DM_DoOwnObj(ws.subjects, s_id2, o_id)
                    ==> s_id1 == s_id2
{
    var k := DMStateToState(ws);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    forall o_id, s_id1, s_id2 | 
                s_id1 in DM_AllSubjsIDs(ws.subjects) && s_id2 in DM_AllSubjsIDs(ws.subjects) && 
                DM_DoOwnObj(ws.subjects, s_id1, o_id) && DM_DoOwnObj(ws.subjects, s_id2, o_id)
        ensures s_id1 == s_id2
    {
        assert s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id);
    }
}




//******** For Specific Operations ********//
lemma Lemma_ExternalObjsActivateDeactivate_ProvePreConditions(
    ws1:DM_State, ws2:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires td_ids <= DM_AllTDIDs(ws1.objects)
    requires fd_ids <= DM_AllFDIDs(ws1.objects)
    requires do_ids <= DM_AllDOIDs(ws1.objects)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws1.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws1.subjects, s_id, o_id)

    requires P_DMState_UnchangedStateVarsAndFields(ws1, ws2)

    ensures td_ids <= DM_AllTDIDs(ws2.objects)
    ensures fd_ids <= DM_AllFDIDs(ws2.objects)
    ensures do_ids <= DM_AllDOIDs(ws2.objects)
    ensures forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws2.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws2.subjects, s_id, o_id)
{
    forall s_id, o_id | s_id in DM_AllSubjsIDs(ws2.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
        ensures !DM_DoOwnObj(ws2.subjects, s_id, o_id)
    {
        assert !DM_DoOwnObj(ws1.subjects, s_id, o_id);
    }
}

lemma Lemma_WSD_DevDeactivate_FromRed_Multi_ProveProperty9(t:DM_Trace, t_detailed:DM_Trace_Detailed, last_ws:DM_State)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties

    requires DM_IsValidTrace(t)

    requires last_ws == SeqLastElem(DM_CalcNewStates(t))
    requires DM_CalcNewStates(t) == t_detailed.states

    ensures last_ws == t_detailed.states[|t_detailed.states|-1]
{
    // Dafny can automatically prove this lemma
}




//******** Private Lemmas ********//
lemma Lemma_ConvertTraceToDetailedTrace_ProveDM_CalcNewStates(t:DM_Trace, result_states:seq<DM_State>)
    requires |t.ops| >= 0
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties

    requires DM_IsValidTrace(t)

    requires |result_states| == |t.ops| + 1
    requires result_states[0] == t.ws0
    requires (forall i :: 0 <= i < |result_states| - 1
                    ==> P_DM_OpsFulfillPreConditions(result_states[i], t.ops[i]))
    requires (forall i :: 0 <= i < |result_states| - 1
                    ==> result_states[i+1] == DM_CalcNewState(result_states[i], t.ops[i]).0)
        // Requirement: Properties of <result_states>
        
    ensures DM_CalcNewStates(t) == result_states
{
    var states := DM_CalcNewStates(t);

    assert |states| == |result_states|;
    
    var i := 0;
    
    while (i < |states|)
        invariant 0 <= i <= |states|
        
        invariant forall j :: 0 <= j < i ==> states[j] == result_states[j]
    {
        if(i > 0)
        {
            assert states[i] == DM_CalcNewState(states[i-1], t.ops[i-1]).0;
            assert result_states[i] == DM_CalcNewState(result_states[i-1], t.ops[i-1]).0;
        }
        i := i + 1;
    }
    
    assert states == result_states;
}

lemma Lemma_DetailedTraceIsInvalid_IfDetailedSubTraceIsInvalid(sub_trace:DM_Trace_Detailed, trace:DM_Trace_Detailed)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires |trace.states| == |sub_trace.states| + 1
    requires |trace.ops| == |sub_trace.ops| + 1
    requires trace.states[1..] == sub_trace.states
    requires trace.ops[1..] == sub_trace.ops

    requires DM_IsValidState(trace.states[0]) && DM_IsSecureState(trace.states[0])

    requires !DM_DetailedTrace_IsValidTrace(sub_trace)
    
    ensures !DM_DetailedTrace_IsValidTrace(trace)
{
    //Dafny can automatically prove this lemma
}

// (needs 30s to verify)
lemma Lemma_ValidDMTrace_Concat_ProveResultDetailedTraceIsValid(
    t1_detailed:DM_Trace_Detailed, t2_detailed:DM_Trace_Detailed, t_detailed:DM_Trace_Detailed
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties
        
    requires DM_DetailedTrace_IsValidTrace(t1_detailed)
    requires DM_DetailedTrace_IsValidTrace(t2_detailed)

    requires t2_detailed.states[0] == SeqLastElem(t1_detailed.states)
    requires t_detailed == DM_Trace_Detailed(t1_detailed.states[..|t1_detailed.states|-1] + t2_detailed.states, t1_detailed.ops + t2_detailed.ops)

    ensures DM_DetailedTrace_IsValidTrace(t_detailed)
{
    forall i | 0 <= i < |t_detailed.ops|
        ensures P_DM_OpsFulfillPreConditions(t_detailed.states[i], t_detailed.ops[i])
        ensures DM_CalcNewState(t_detailed.states[i], t_detailed.ops[i]).0 == t_detailed.states[i+1]
    {
        if(0<=i<|t1_detailed.ops|)
        {
            assert P_DM_OpsFulfillPreConditions(t_detailed.states[i], t_detailed.ops[i]);
            assert DM_CalcNewState(t_detailed.states[i], t_detailed.ops[i]).0 == t_detailed.states[i+1];
        }
        else
        {
            assert |t1_detailed.ops| <= i < |t_detailed.ops|;
            assert P_DM_OpsFulfillPreConditions(t_detailed.states[i], t_detailed.ops[i]);

            assert t_detailed.ops[i] == t2_detailed.ops[i-|t1_detailed.ops|];
            assert t_detailed.states[i] == t2_detailed.states[i-|t1_detailed.ops|];
            assert DM_CalcNewState(t_detailed.states[i], t_detailed.ops[i]).0 == t_detailed.states[i+1];
        }
    }
}