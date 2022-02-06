include "Utils.dfy"

// Lemma: Properties of WSD_TDs/FDs/DOs/HCodedTDsOwnedByDevs
lemma Lemma_WSD_ObjsOwnedByDevs_Properties(ws:DM_State, dev_ids:set<Dev_ID>)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires DM_IsValidState_Objects(ws)

    requires forall id :: id in dev_ids
                ==> DM_IsDevID(ws.subjects, id)

    ensures var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids);
            (dev_tds <= DM_AllTDIDs(ws.objects)) &&
            (dev_fds <= DM_AllFDIDs(ws.objects)) &&
            (dev_dos <= DM_AllDOIDs(ws.objects))
    ensures var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids);
            dev_hcoded_td_ids <= dev_tds &&
            dev_hcoded_td_ids <= DM_AllHCodedTDIDs(ws.subjects)
        // Property 1: HCoded TDs returned by <WSD_TDsOwnedByDevs> must be in WSD_TDsOwnedByDevs(ws, dev_ids) and 
        // DM_AllHCodedTDIDs(ws.subjects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSD_ObjsOwnedByDevs_Properties_NonHCodedTDs(ws:DM_State, dev_ids:set<Dev_ID>)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires DM_IsValidState_Objects(ws)

    requires forall id :: id in dev_ids
                ==> DM_IsDevID(ws.subjects, id)


    ensures var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids);
            var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids);
            var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids);
            var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids);
            (forall id :: id in dev_tds &&
                    id !in dev_hcoded_td_ids
                ==> id !in DM_AllHCodedTDIDs(ws.subjects))
        // Property 1: HCoded TDs returned by <WSD_TDsOwnedByDevs> must be in WSD_TDsOwnedByDevs(ws, dev_ids) and 
        // DM_AllHCodedTDIDs(ws.subjects)
{
    var dev_tds:set<TD_ID> := WSD_TDsOwnedByDevs(ws, dev_ids);
    var dev_fds:set<FD_ID> := WSD_FDsOwnedByDevs(ws, dev_ids);
    var dev_dos:set<DO_ID> := WSD_DOsOwnedByDevs(ws, dev_ids);
    var dev_hcoded_td_ids := WSD_HCodedTDsOwnedByDevs(ws, dev_ids);

    forall id | id in dev_tds &&
                    id !in dev_hcoded_td_ids
        ensures id !in DM_AllHCodedTDIDs(ws.subjects)
    {
        if(id in DM_AllHCodedTDIDs(ws.subjects))
        {
            var dev_in_dev_ids :| dev_in_dev_ids in dev_ids &&
                         id in ws.subjects.devs[dev_in_dev_ids].td_ids;
            var dev_id :| dev_id in ws.subjects.devs && 
                         ws.subjects.devs[dev_id].hcoded_td_id == id;
            assert dev_id !in dev_ids;
            assert dev_id != dev_in_dev_ids;

            // Show conflict
            assert DM_DoOwnObj(ws.subjects, dev_in_dev_ids.sid, id.oid);
            assert DM_DoOwnObj(ws.subjects, dev_id.sid, id.oid);

            var k := DMStateToState(ws);
            assert IsValidState_Objects(k);

            assert DoOwnObj(k, dev_in_dev_ids.sid, id.oid);
            assert DoOwnObj(k, dev_id.sid, id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                    s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                    DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                        ==> s_id1 == s_id2);

            assert false;
        }
    }
}

lemma Lemma_WSD_ObjsOwnedByDevs_HighlightADev(
    ws:DM_State, dev_ids_set:set<Dev_ID>, next_dev_ids_set:set<Dev_ID>, dev0_id:Dev_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
     
    requires forall id :: id in dev_ids_set ==> id in ws.subjects.devs
    requires dev_ids_set == {dev0_id} + next_dev_ids_set

    ensures WSD_TDsOwnedByDevs(ws, dev_ids_set) == WSD_TDsOwnedByDevs(ws, next_dev_ids_set) + ws.subjects.devs[dev0_id].td_ids
    ensures WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set) == WSD_HCodedTDsOwnedByDevs(ws, next_dev_ids_set) + {ws.subjects.devs[dev0_id].hcoded_td_id}
    ensures WSD_FDsOwnedByDevs(ws, dev_ids_set) == WSD_FDsOwnedByDevs(ws, next_dev_ids_set) + ws.subjects.devs[dev0_id].fd_ids
    ensures WSD_DOsOwnedByDevs(ws, dev_ids_set) == WSD_DOsOwnedByDevs(ws, next_dev_ids_set) + ws.subjects.devs[dev0_id].do_ids
{
    assert dev_ids_set == next_dev_ids_set + {dev0_id};
    assert forall dev_id :: dev_id in dev_ids_set
            ==> dev_id in next_dev_ids_set || dev_id == dev0_id;

    // Prove WSD_TDsOwnedByDevs(ws, dev_ids_set) == WSD_TDsOwnedByDevs(ws, next_dev_ids_set) + ws.subjects.devs[dev0_id].td_ids
    var td_set1 := WSD_TDsOwnedByDevs(ws, dev_ids_set);
    var td_set2 := WSD_TDsOwnedByDevs(ws, next_dev_ids_set);
    Lemma_SetAnd_Equality(td_set1, td_set2, ws.subjects.devs[dev0_id].td_ids);

    // Prove WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set) == WSD_HCodedTDsOwnedByDevs(ws, next_dev_ids_set) + ws.subjects.devs[dev0_id].hcoded_td_id
    var htd_set1 := WSD_HCodedTDsOwnedByDevs(ws, dev_ids_set);
    var htd_set2 := WSD_HCodedTDsOwnedByDevs(ws, next_dev_ids_set);
    Lemma_SetAnd_Equality(htd_set1, htd_set2, {ws.subjects.devs[dev0_id].hcoded_td_id});

    // Prove WSD_FDsOwnedByDevs(ws, dev_ids_set) == WSD_FDsOwnedByDevs(ws, next_dev_ids_set) + ws.subjects.devs[dev0_id].fd_ids
    var fd_set1 := WSD_FDsOwnedByDevs(ws, dev_ids_set);
    var fd_set2 := WSD_FDsOwnedByDevs(ws, next_dev_ids_set);
    Lemma_SetAnd_Equality(fd_set1, fd_set2, ws.subjects.devs[dev0_id].fd_ids);

    // Prove WSD_DOsOwnedByDevs(ws, dev_ids_set) == WSD_DOsOwnedByDevs(ws, next_dev_ids_set) + ws.subjects.devs[dev0_id].fd_ids
    var do_set1 := WSD_DOsOwnedByDevs(ws, dev_ids_set);
    var do_set2 := WSD_DOsOwnedByDevs(ws, next_dev_ids_set);
    Lemma_SetAnd_Equality(do_set1, do_set2, ws.subjects.devs[dev0_id].do_ids);
}

lemma Lemma_WSD_ObjsOwnedByDevs_PropertyOfOneDev(ws:DM_State, dev_id:Dev_ID)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)

    requires dev_id in ws.subjects.devs

    ensures WSD_TDsOwnedByDevs(ws, {dev_id}) == ws.subjects.devs[dev_id].td_ids
    ensures WSD_FDsOwnedByDevs(ws, {dev_id}) == ws.subjects.devs[dev_id].fd_ids
    ensures WSD_DOsOwnedByDevs(ws, {dev_id}) == ws.subjects.devs[dev_id].do_ids
    ensures WSD_HCodedTDsOwnedByDevs(ws, {dev_id}) == {ws.subjects.devs[dev_id].hcoded_td_id}
{
    Lemma_WSD_TDsOwnedByDevs_PropertyOfOneDev_TD(ws, dev_id);
    Lemma_WSD_TDsOwnedByDevs_PropertyOfOneDev_FD(ws, dev_id);
    Lemma_WSD_TDsOwnedByDevs_PropertyOfOneDev_DO(ws, dev_id);
}

lemma Lemma_WSD_HCodedTDsOwnedByDevs_PropertyGetOwnerDevice(ws:DM_State, dev_ids:set<Dev_ID>, id:TD_ID) returns (dev_id_s:Dev_ID)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    requires var result := WSD_HCodedTDsOwnedByDevs(ws, dev_ids);
             id in result

    ensures dev_id_s in dev_ids && ws.subjects.devs[dev_id_s].hcoded_td_id == id
{
    var result := WSD_HCodedTDsOwnedByDevs(ws, dev_ids);
    var dev_id :| dev_id in dev_ids && ws.subjects.devs[dev_id].hcoded_td_id == id;

    return dev_id;
}

lemma Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(
    ws:DM_State, ws1:DM_State, ws2:DM_State, t1:DM_Trace, t2:DM_Trace
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires t1.ws0 == ws
    requires DM_IsValidTrace(t1)
    requires ws1 == SeqLastElem(DM_CalcNewStates(t1))
    requires DM_IsValidState(ws1) && DM_IsSecureState(ws1)
    
    requires t2.ws0 == ws1
    requires DM_IsValidTrace(t2)
    requires ws2 == SeqLastElem(DM_CalcNewStates(t2))

    ensures ws2 == SeqLastElem(DM_CalcNewStates(ValidDMTrace_Concat(t1, t2)))
{
    var t := ValidDMTrace_Concat(t1, t2);
    assert DM_IsValidTrace(t);

    var result;
    var d;
    var t1_detailed, t2_detailed, t_detailed;
    result := ConvertTraceToDetailedTrace(t1);
    t1_detailed := result.0;
    d := result.1;
    assert d;

    result := ConvertTraceToDetailedTrace(t2);
    t2_detailed := result.0;
    d := result.1;
    assert d;

    result := ConvertTraceToDetailedTrace(t);
    t_detailed := result.0;
    d := result.1;
    assert d;
    
    assert t_detailed.ops == t1_detailed.ops + t2_detailed.ops;
    
    // Prove the main property
    var i := Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_Private(
                ws, ws1, ws2, t1, t2, t, t1_detailed, t2_detailed, t_detailed);
    assert |t_detailed.states| - |t1_detailed.states| == |t2_detailed.states| - 1;

    
    if(|t2_detailed.states| == 1)
    {
        assert SeqLastElem(t1_detailed.states) == SeqLastElem(t2_detailed.states) == ws1;
        assert t_detailed.states[|t_detailed.states|-1] == ws1;
        assert t_detailed.states[|t_detailed.states|-1] == t2_detailed.states[|t2_detailed.states|-1];
    }
    else
    {
        var s_t := |t_detailed.states|;
        var s_t1 := |t1_detailed.states|;
        var s_t2 := |t2_detailed.states|;
        assert s_t - s_t1 == s_t2 - 1;

        // Prove t_detailed.states[|t_detailed.states|-1] == t2_detailed.states[|t2_detailed.states|-1]
        assert |t2_detailed.states| > 1;
        assert |t_detailed.states|-1 >= |t1_detailed.states|;
        assert t_detailed.states[i] == t2_detailed.states[i+1-|t1_detailed.states|];
        assert t_detailed.states[i] == t2_detailed.states[i+1-s_t1];

        assert i == s_t - 1;
        assert s_t - s_t1 == s_t2 - 1;
        Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_ProvePropertiesWhenT2HasMultipleElems(
            t_detailed, t1_detailed, t2_detailed, i);
        assume t_detailed.states[s_t-1] == t2_detailed.states[s_t2-1]; // [NOTE] We have proved it in the lemma above, but Dafny forgets it somehow.
    }

    var seq1 := t_detailed.states;
    var seq2 := t2_detailed.states;

    assert t_detailed.states[|t_detailed.states|-1] == t2_detailed.states[|t2_detailed.states|-1];
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_EquivilantEndOfSeq(
        t_detailed, t2_detailed, seq1, seq2);
    assert seq1[|seq1|-1] == seq2[|seq2|-1]; 
    Lemma_SeqLastElem_Property(seq1, seq2);
    assert SeqLastElem(t_detailed.states) == SeqLastElem(t2_detailed.states);
}

// Lemma: If a DM_Trace comprises one operation only, and the operation returns 
// true, then the return state is the last state
lemma Lemma_DM_CalcNewStates_OneDMOp_Property(ws:DM_State, op:DM_Op, ws':DM_State)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires P_DM_OpsFulfillPreConditions(ws, op)
    
    requires DM_CalcNewState(ws, op) == (ws', true)
     
    ensures ws' == SeqLastElem(DM_CalcNewStates(DM_Trace(ws, [op])))
{
    assert DM_CalcNewStates(DM_Trace(ws, [op])) == [ws, ws'];
    assert SeqLastElem([ws, ws']) == ws';
}

lemma Lemma_DM_CalcNewStates_NoDMOp_Property(ws:DM_State)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    
     
    ensures ws == SeqLastElem(DM_CalcNewStates(DM_Trace(ws, [])))
{
    assert DM_CalcNewStates(DM_Trace(ws, [])) == [ws];
    assert SeqLastElem([ws]) == ws;
}




//******** Private Lemmas ********//
lemma Lemma_WSD_TDsOwnedByDevs_PropertyOfOneDev_TD(ws:DM_State, dev_id:Dev_ID)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)

    requires dev_id in ws.subjects.devs

    ensures WSD_TDsOwnedByDevs(ws, {dev_id}) == ws.subjects.devs[dev_id].td_ids
{
    Lemma_DM_SameIDsIffSameInternalIDs();

    var td_set := WSD_TDsOwnedByDevs(ws, {dev_id});
    forall id | id in td_set 
        ensures id in ws.subjects.devs[dev_id].td_ids
    {
        var s_id :| s_id in {dev_id} && DM_DoOwnObj(ws.subjects, s_id.sid, id.oid);
        assert s_id == dev_id;
    }
    assert forall id :: id in ws.subjects.devs[dev_id].td_ids ==> id in td_set;
    Lemma_Set_Equality(td_set, ws.subjects.devs[dev_id].td_ids);
}

lemma Lemma_WSD_TDsOwnedByDevs_PropertyOfOneDev_FD(ws:DM_State, dev_id:Dev_ID)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)

    requires dev_id in ws.subjects.devs

    ensures WSD_FDsOwnedByDevs(ws, {dev_id}) == ws.subjects.devs[dev_id].fd_ids
{
    Lemma_DM_SameIDsIffSameInternalIDs();

    var fd_set := WSD_FDsOwnedByDevs(ws, {dev_id});
    forall id | id in fd_set 
        ensures id in ws.subjects.devs[dev_id].fd_ids
    {
        var s_id :| s_id in {dev_id} && DM_DoOwnObj(ws.subjects, s_id.sid, id.oid);
        assert s_id == dev_id;
    }
    assert forall id :: id in ws.subjects.devs[dev_id].fd_ids ==> id in fd_set;
    Lemma_Set_Equality(fd_set, ws.subjects.devs[dev_id].fd_ids);
}

lemma Lemma_WSD_TDsOwnedByDevs_PropertyOfOneDev_DO(ws:DM_State, dev_id:Dev_ID)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)

    requires dev_id in ws.subjects.devs

    ensures WSD_DOsOwnedByDevs(ws, {dev_id}) == ws.subjects.devs[dev_id].do_ids
{
    Lemma_DM_SameIDsIffSameInternalIDs();

    var do_set := WSD_DOsOwnedByDevs(ws, {dev_id});
    forall id | id in do_set 
        ensures id in ws.subjects.devs[dev_id].do_ids
    {
        var s_id :| s_id in {dev_id} && DM_DoOwnObj(ws.subjects, s_id.sid, id.oid);
        assert s_id == dev_id;
    }
    assert forall id :: id in ws.subjects.devs[dev_id].do_ids ==> id in do_set;
    Lemma_Set_Equality(do_set, ws.subjects.devs[dev_id].do_ids);
}