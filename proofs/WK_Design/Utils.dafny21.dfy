include "../DetailedModel/Model.dfy"
include "DM_AdditionalPropertiesLemmas.dfy"

// [NOTE] Dafny-v2.1 can verify this file alone, but report errors if verifying the entire project. 
// Future Dafny releases may solve the issue.

lemma Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_Private(
    ws:DM_State, ws1:DM_State, ws2:DM_State, t1:DM_Trace, t2:DM_Trace, t:DM_Trace,
    t1_detailed:DM_Trace_Detailed, t2_detailed:DM_Trace_Detailed, t_detailed:DM_Trace_Detailed
) returns (i:int)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires t1.ws0 == ws
    requires DM_IsValidTrace(t1)
    requires ws1 == SeqLastElem(DM_CalcNewStates(t1))
    requires DM_IsValidState(ws1) && DM_IsSecureState(ws1)
    
    requires t2.ws0 == ws1
    requires DM_IsValidTrace(t2)
    requires ws2 == SeqLastElem(DM_CalcNewStates(t2))

    requires t1_detailed == ConvertTraceToDetailedTrace(t1).0
    requires t2_detailed == ConvertTraceToDetailedTrace(t2).0
    requires t == ValidDMTrace_Concat(t1, t2);
    requires t_detailed == ConvertTraceToDetailedTrace(t).0

    ensures i == |t_detailed.states|-1
    ensures 0 <= i < |t1_detailed.states| ==> t_detailed.states[i] == t1_detailed.states[i]
    ensures |t1_detailed.states| <= i < |t_detailed.states| ==> t_detailed.states[i] == t2_detailed.states[i+1-|t1_detailed.states|]
{
    assert DM_IsValidTrace(t);

    assert ConvertTraceToDetailedTrace(t1).1;
    assert ConvertTraceToDetailedTrace(t2).1;
    assert ConvertTraceToDetailedTrace(t).1;

    assert t_detailed.ops == t1_detailed.ops + t2_detailed.ops;

    i := 0;

    assert t1_detailed.states[|t1_detailed.states|-1] == ws1;
    assert t2_detailed.states[0] == ws1;
    assert |t_detailed.states| >= |t1_detailed.states|;

    while (i < |t_detailed.states|-1)
        invariant 0 <= i <= |t_detailed.states|-1

        invariant 0 <= i < |t1_detailed.ops| ==> t_detailed.ops[i] == t1_detailed.ops[i]
        invariant 0 <= i < |t1_detailed.states| ==> t_detailed.states[i] == t1_detailed.states[i]

        invariant |t1_detailed.ops| <= i < |t_detailed.ops| ==> t_detailed.ops[i] == t2_detailed.ops[i-|t1_detailed.ops|]
        invariant |t1_detailed.states| <= i < |t_detailed.states| ==> t_detailed.states[i] == t2_detailed.states[i+1-|t1_detailed.states|]
    {
        if (|t1_detailed.states| <= i < |t_detailed.states| && 
            |t1_detailed.states| <= i+1 < |t_detailed.states|)
        {
            var from_t2_detailed_state := t2_detailed.states[i+1-|t1_detailed.states|];
            var to_t2_detailed_state := t2_detailed.states[i+2-|t1_detailed.states|];
            
            assert t_detailed.states[i] == from_t2_detailed_state;
            
            assert t_detailed.states[i+1] == DM_CalcNewState(t_detailed.states[i], t_detailed.ops[i]).0;
            
            assert to_t2_detailed_state == DM_CalcNewState(from_t2_detailed_state, t2_detailed.ops[i+1-|t1_detailed.states|]).0;
            assert |t1_detailed.states| == |t1_detailed.ops|+1;
            assert i+1-|t1_detailed.states| == i-|t1_detailed.ops|;
            Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_Private_ForT2Detailed(t1_detailed, t2_detailed, i);
            assert t2_detailed.ops[i+1-|t1_detailed.states|] == t2_detailed.ops[i-|t1_detailed.ops|];
            assert to_t2_detailed_state == DM_CalcNewState(from_t2_detailed_state, t2_detailed.ops[i-|t1_detailed.ops|]).0;
            
            // Prove same op in <t_detailed> and <t2_detailed>
            assert |t1_detailed.ops| <= i < |t_detailed.ops|;
            assert t_detailed.ops[i] == t2_detailed.ops[i-|t1_detailed.ops|];
            
            assert to_t2_detailed_state == DM_CalcNewState(from_t2_detailed_state, t_detailed.ops[i]).0;
            assert t_detailed.states[i+1] == to_t2_detailed_state;
        }

        i := i + 1;
    }

    assert 0 <= i < |t1_detailed.states| ==> t_detailed.states[i] == t1_detailed.states[i];
    assert |t1_detailed.states| <= i < |t_detailed.states| ==> t_detailed.states[i] == t2_detailed.states[i+1-|t1_detailed.states|];
}

lemma Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_Private_ForT2Detailed(
    t1_detailed:DM_Trace_Detailed, t2_detailed:DM_Trace_Detailed, i:int
)
    requires i+1-|t1_detailed.states| == i-|t1_detailed.ops|
    requires 0 <= i-|t1_detailed.ops| < |t2_detailed.ops|

    ensures t2_detailed.ops[i+1-|t1_detailed.states|] == t2_detailed.ops[i-|t1_detailed.ops|]
{
    // Dafny can automatically prove this lemma
}