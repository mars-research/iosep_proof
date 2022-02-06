include "../Abstract/Model.dfy"
include "Mappings_ValidState_SecureState.dfy"

//******** SubjRead ********//
// Property: If a subject read objects (and/or copy to destination objects),  
// then the subject and all accessed objects must be in the same partition 
predicate P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(
    ws:DM_State, s_id:Subject_ID,
    read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>
)
    requires DM_IsValidState_Subjects(ws) && DM_IsValidState_Objects(ws)
    requires s_id in DM_AllSubjsIDs(ws.subjects)

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
{
    (forall o_id :: o_id in read_objs
                    ==> o_id in DM_AllObjsIDs(ws.objects) &&
                        DM_ObjPID(ws.objects, o_id) == DM_SubjPID(ws.subjects, s_id)) &&
        // Objects in parameters must be in the same partition with the driver
    (forall td_id :: td_id in tds_dst_src
                    ==> DM_ObjPID(ws.objects, td_id.oid) == DM_SubjPID(ws.subjects, s_id)) &&
    (forall fd_id :: fd_id in fds_dst_src
                    ==> DM_ObjPID(ws.objects, fd_id.oid) == DM_SubjPID(ws.subjects, s_id)) &&
    (forall do_id :: do_id in dos_dst_src
                    ==> DM_ObjPID(ws.objects, do_id.oid) == DM_SubjPID(ws.subjects, s_id)) &&
        // All objects that store read results must be in the same partition
        // with the subject

    (true)
}

predicate DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(
    ws:DM_State, 
    
    tds_dst_src:map<TD_ID, TD_ID>,
    fds_dst_src:map<FD_ID, FD_ID>,
    dos_dst_src:map<DO_ID, DO_ID> 
)
{
    (forall td_id :: td_id in tds_dst_src
                ==> td_id in ws.objects.active_non_hcoded_tds && tds_dst_src[td_id] in ws.objects.active_non_hcoded_tds) &&
    (forall fd_id :: fd_id in fds_dst_src
                ==> fd_id in ws.objects.active_fds && fds_dst_src[fd_id] in ws.objects.active_fds) &&
    (forall do_id :: do_id in dos_dst_src
                ==> do_id in ws.objects.active_dos && dos_dst_src[do_id] in ws.objects.active_dos) &&
        
    (true)
}

predicate DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(
    ws:DM_State,
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is active

    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    (forall td_id2 :: td_id2 in tds_dst_src
                ==> DevWrite_WriteTDWithValMustBeInATransfer(k, dev_sid, td_id2, DevRead_GetReadObjVal_AnyTD(ws.objects, tds_dst_src[td_id2])))&&
    (forall fd_id2 :: fd_id2 in fds_dst_src
                ==> DevWrite_WriteFDWithValMustBeInATransfer(k, dev_sid, fd_id2, DevRead_GetReadObjVal_AnyFD(ws.objects, fds_dst_src[fd_id2])))&&
    (forall do_id2 :: do_id2 in dos_dst_src
                ==> DevWrite_WriteDOWithValMustBeInATransfer(k, dev_sid, do_id2, DevRead_GetReadObjVal_AnyDO(ws.objects, dos_dst_src[do_id2])))&&
        // Requirement: Writing destination TDs/FDs/DOs with values of source 
        // objects must be in tranfers

    (true)
}

predicate DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(
    ws:DM_State, dev_sid:Subject_ID, read_objs:set<Object_ID>
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    
    (forall o_id :: o_id in read_objs
            ==> R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id)) &&
        // Requirement: The device (<Dev_ID(dev_sid)>) must have transfers to
        // the objects (<read_objs>)
        
    (true)
}



//******** DrvWrite ********//
function method DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
) : bool
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(ws.objects))
        // Requirement: Driver only write existing objects
{
    (forall id :: id in td_id_val_map
        ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, id.oid)) &&
    (forall id :: id in fd_id_val_map
        ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, id.oid)) &&
    (forall id :: id in do_id_val_map
        ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, id.oid))
}

function method DM_GreenDrvWrite_ChkNewValsOfTDs(
    ws:DM_State, 
    td_id_val_map:map<TD_ID, TD_Val>
) : bool
    requires DM_IsValidState_Subjects(ws) && DM_IsValidState_Objects(ws)
    
    requires forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.active_non_hcoded_tds
        // Requirement: Driver only write existing objects
    requires forall id :: id in td_id_val_map
                ==> DM_ObjPID(ws.objects, id.oid) != NULL
        // Requirement: TDs in <td_id_val_map> are active
{
    //reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var k := DMStateToState(ws);
    var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);

    // Prove IsValidState_Objects_UniqueObjIDs(t_objs1)
    assert IsValidState_Objects(k);
    assert IsValidState_Objects_UniqueObjIDs(k.objects);
    Lemma_K_SameObjIDs_ProveIsValidState_Objects_UniqueObjIDs(k.objects, t_objs1);
    assert IsValidState_Objects_UniqueObjIDs(t_objs1);

    Lemma_WriteActiveNonHCodedTDsVals_ProveIsValidState_Objects_UniqueObjIDs(k.objects, td_id_val_map);
    assert AllActiveTDs_SlimState(t_objs1) == AllActiveTDs_SlimState(ws.objects);

    forall id :: id in td_id_val_map
        ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState_SlimState(t_objs1), id)
}




//******** DevWrite ********//
predicate DM_DevWrite_WriteTDWithValMustBeInATransfer(
    ws:DM_State, dev_sid:Subject_ID, target_td_id:TD_ID, write_val:TD_Val
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    DevWrite_WriteTDWithValMustBeInATransfer(k, dev_sid, target_td_id, write_val)
}

predicate DM_DevWrite_WriteFDWithValMustBeInATransfer(
    ws:DM_State, dev_sid:Subject_ID, target_fd_id:FD_ID, write_val:FD_Val
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    DevWrite_WriteFDWithValMustBeInATransfer(k, dev_sid, target_fd_id, write_val)
}

predicate DM_DevWrite_WriteDOWithValMustBeInATransfer(
    ws:DM_State, dev_sid:Subject_ID, target_do_id:DO_ID, write_val:DO_Val
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    DevWrite_WriteDOWithValMustBeInATransfer(k, dev_sid, target_do_id, write_val)
}

// Property: If a subject write objects, then the subject and the objects must 
// be in the same partition 
predicate P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(
    ws:DM_State, 
    s_id:Subject_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires DM_IsValidState_ObjIDs(ws) 
    requires s_id in DM_AllSubjsIDs(ws.subjects)

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(ws.objects))
        // Requirement: Device only write existing objects
{
    forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
                    // Forall o_id that is an internal ID of any TD/FD/DO in *_id_val_map
        ==> o_id in DM_AllObjsIDs(ws.objects) &&
            DM_ObjPID(ws.objects, o_id) == DM_SubjPID(ws.subjects, s_id) &&

    (true)
}




//******** Deactivate ********//
function method DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(
    ws:DM_State, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>, green_pid:Partition_ID
) : bool
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids
                ==> id in DM_AllDOIDs(ws.objects)
                
    requires green_pid != NULL
    requires green_pid != ws.red_pid
{
    var k := DMStateToState(ws);
    var k_tds_state := ActiveTDsState(k);

    forall td_id :: td_id in (DM_TDIDsInGreen(ws) - todeactivate_td_ids) &&
                    DM_ObjPID(ws.objects, td_id.oid) == green_pid
                        // For all other green TDs in the partition <green_pid>
                ==> (forall id :: id in todeactivate_td_ids 
                            ==> (id !in k_tds_state[td_id].trans_params_tds || k_tds_state[td_id].trans_params_tds[id].amodes == {})) &&
                    (forall id :: id in todeactivate_fd_ids 
                            ==> (id !in k_tds_state[td_id].trans_params_fds || k_tds_state[td_id].trans_params_fds[id].amodes == {})) &&
                    (forall id :: id in todeactivate_do_ids 
                            ==> (id !in k_tds_state[td_id].trans_params_dos || k_tds_state[td_id].trans_params_dos[id].amodes == {}))
                        // They do not ref any objects to be deactivated
}

predicate P_RedDevsHaveNoTransferToGivenRedObjsAtAnyTime(ws:DM_State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires DM_IsValidState_SubjsObjsPIDs(ws)

    requires td_ids <= AllTDIDs(ws.objects)
    requires fd_ids <= AllFDIDs(ws.objects)
    requires do_ids <= AllDOIDs(ws.objects)

    requires forall id :: id in td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == ws.red_pid
    requires forall id :: id in fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == ws.red_pid
    requires forall id :: id in do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == ws.red_pid
{
    var objs := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);

    var k := DMStateToState(ws);
    var k_params := KToKParams(k);
    var k_tds_state := ActiveTDsState_SlimState(k.objects);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k.objects) &&
            (k_tds_state == tds_state2 || 
                (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                        DM_DevsInRed(ws), k_tds_state, tds_state2) &&
                    IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        DM_DevsInRed(ws), k_tds_state, tds_state2)))
                            // Forall tds_state2, k_tds_state -->* tds_state2
        ==> (forall o_id, dev_id2 :: 
                    o_id in objs &&
                    dev_id2 in DM_DevsInRed(ws)
                            // For each device (<dev_id2>) in red 
                ==> DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id) == {}))
                            // The device has no transfer to any objects in <objs>
}

predicate P_RedDevsHaveNoTransferToGivenRedDrvAtAnyTime(ws:DM_State, drv_id:Drv_ID)
    requires DM_IsValidState_SubjsObjsPIDs(ws)

    requires drv_id in DM_AllDrvIDs(ws.subjects)
    requires DM_SubjPID(ws.subjects, drv_id.sid) == ws.red_pid
{
    var objs := DM_OwnedObjs(ws.subjects, drv_id.sid);

    var k := DMStateToState(ws);
    var k_params := KToKParams(k);
    var k_tds_state := ActiveTDsState_SlimState(k.objects);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k.objects) &&
            (k_tds_state == tds_state2 || 
                (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                        DM_DevsInRed(ws), k_tds_state, tds_state2) &&
                    IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        DM_DevsInRed(ws), k_tds_state, tds_state2)))
                            // Forall tds_state2, k_tds_state -->* tds_state2
        ==> (forall o_id, dev_id2 :: 
                    o_id in objs &&
                    dev_id2 in DM_DevsInRed(ws)
                            // For each device (<dev_id2>) in red
                ==> DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id) == {}))
                            // The device has no transfer to any objects of the driver <drv_id>
}




//******** DevDeactivate ********//
predicate P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws:DM_State, dev_id:Dev_ID)
    requires DM_IsValidState_SubjsObjsPIDs(ws)

    requires dev_id in DM_AllDevIDs(ws.subjects)
    requires DM_SubjPID(ws.subjects, dev_id.sid) == ws.red_pid
{
    var objs := DM_OwnedObjs(ws.subjects, dev_id.sid);

    var k := DMStateToState(ws);
    var k_params := KToKParams(k);
    var k_tds_state := ActiveTDsState_SlimState(k.objects);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k.objects) &&
            (k_tds_state == tds_state2 || 
                (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                        DM_DevsInRed(ws), k_tds_state, tds_state2) &&
                    IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        DM_DevsInRed(ws), k_tds_state, tds_state2)))
                            // Forall tds_state2, k_tds_state -->* tds_state2
        ==> (forall o_id, dev_id2 :: 
                    o_id in objs &&
                    dev_id2 in DM_DevsInRed(ws) - {dev_id}
                            // For each device (<dev_id2>) in red different from the device (<dev_id>)
                ==> DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id) == {}))
                            // The device has no transfer to any objects of the device <dev_id>
}

// [NOTE] Needs 250s to verify
method DM_Chk_DevDeactivate_OtherDevsInRedPartitonHaveNoTransferToGivenRedDevAtAnyTime(
    ws:DM_State, k:State, dev_id:Dev_ID
) returns (d:bool)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k) && IsSecureState(k)

    requires dev_id in DM_DevsInRed(ws)

    ensures d ==> P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, dev_id)
{
    // Calculate reachable snapshots of active TDs in K
    var k_tds_states := ValidSecureState_ReachableStatesOfActiveTDs(k);

    // Build CAS for K
    var k_cas := BuildCAS(k, KToKParams(k), k_tds_states);

    Lemma_K_P_ObjsInSubjsAreAlsoInState_Prove(k);

    d := (forall o_id, dev_id2 :: 
            (o_id in OwnObjIDs(k, dev_id.sid)) && 
            (dev_id2 in DM_DevsInRed(ws) - {dev_id})
            ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {});

    // Prove P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime
    if(d)
    {
        var objs := DM_OwnedObjs(ws.subjects, dev_id.sid);
        var k_params := KToKParams(k);
        var k_tds_state := ActiveTDsState_SlimState(k.objects);

        forall tds_state2 | TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k.objects) &&
                (k_tds_state == tds_state2 || 
                    (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            DM_DevsInRed(ws), k_tds_state, tds_state2) &&
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            DM_DevsInRed(ws), k_tds_state, tds_state2)))
            ensures (forall o_id, dev_id2 :: 
                    o_id in objs &&
                    dev_id2 in DM_DevsInRed(ws) - {dev_id}
                            // For each device (<dev_id2>) in red different from the device (<dev_id>)
                ==> DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id) == {})
        {
            // Prove tds_state2 in AllReachableActiveTDsStates(k);
            if(k_tds_state == tds_state2)
            {
                assert tds_state2 in AllReachableActiveTDsStates(k);
            }
            else
            {
                Lemma_DM_DevsInRed_IsSubsetOfAllActiveDevs(ws, k);
                Lemma_K_IfTDsStateCanBeReachedViaSmallSetOfActiveDevs_ThenCanBeReachedViaLargeSetToo(
                    k_params, DM_DevsInRed(ws), AllActiveDevs(k), k_tds_state, tds_state2);
                assert tds_state2 in AllReachableActiveTDsStates(k);
            }
            assert tds_state2 in AllReachableActiveTDsStates(k);

            Lemma_DMOwnedObjsEqualsOwnObjIDs(ws, k);
            forall o_id, dev_id2 | o_id in objs &&
                        dev_id2 in DM_DevsInRed(ws) - {dev_id}
                            // For each device (<dev_id2>) in red different from the device (<dev_id>)
                ensures DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id) == {}
            {
                Lemma_DM_ObjsOwnedByActiveSubjs_AreActive(ws, k, dev_id.sid, o_id);
                assert dev_id2 in AllActiveDevs(k);
                assert o_id in AllActiveObjs(k);

                assert IsInCAS(k_cas, dev_id2, o_id);
                var amodes := CASGetAModes(k_cas, dev_id2, o_id);
                assert amodes == {};
                Lemma_EmptyAModesIsNoRAndNoW(amodes);

                var amodes2 := DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id);
                if(R in amodes2)
                {
                    assert tds_state2 in k_tds_states;
                    assert R in DevAModesToObj(k, tds_state2, dev_id2, o_id);

                    assert R in amodes;
                    assert false;
                }
                if(W in amodes2)
                {
                    assert tds_state2 in k_tds_states;
                    assert W in DevAModesToObj(k, tds_state2, dev_id2, o_id);

                    assert W in amodes;
                    assert false;
                }

                Lemma_EmptyAModesIsNoRAndNoW(amodes2);
                assert amodes2 == {};
            }
        }
    }
}




//******** For Proof of Commutative Diagrams ********//
function DrvDevWrite_Func(
    k:State,
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in k.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in k.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in k.objects.active_dos
{
    // Construct k'.objects
    var t_objs1 := WriteActiveNonHCodedTDsVals(k.objects, td_id_val_map);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
    var new_objects := t_objs3;

    State(k.subjects, new_objects, k.pids, k.tds_to_all_states)
}

function EmptyPartitionCreate_Func(k:State, new_pid:Partition_ID) : (k':State)
{
    var pids' := k.pids + {new_pid};

    State(k.subjects, k.objects, pids', k.tds_to_all_states)
}

function EmptyPartitionDestroy_Func(k:State, pid:Partition_ID) : (k':State)
{
    var pids' := k.pids - {pid};

    State(k.subjects, k.objects, pids', k.tds_to_all_states)
}

function DrvActivate_Func(k:State, drv_sid:Subject_ID, pid:Partition_ID) : (k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires pid != NULL

    requires forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.inactive_non_hcoded_tds
    requires forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.inactive_fds
    requires forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.inactive_dos
{
    var drv_id := Drv_ID(drv_sid);
    var drv_state := IDToDrv(k, drv_id);
    var new_drv_state := Drv_State(pid, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
    var new_drvs := k.subjects.drvs[drv_id := new_drv_state];
    var new_subjects := Subjects(new_drvs, k.subjects.devs);

    // Construct k'.objects
    var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;

    //// Modify the PID of these objects (i.e., SetObjsPIDs)
    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, tds_owned_by_drv, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_drv, pid);
    var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_drv, pid);

    State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

function DevActivate_Func(k:State, dev_sid:Subject_ID, pid:Partition_ID) : (k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires pid != NULL

    requires forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].td_ids && 
                    id != k.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id 
                 ==> id in k.objects.inactive_non_hcoded_tds
    requires forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].fd_ids ==> id in k.objects.inactive_fds
    requires forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].do_ids ==> id in k.objects.inactive_dos
    requires k.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id in k.objects.hcoded_tds
{
    var dev_id := Dev_ID(dev_sid);
    var dev_state := IDToDev(k, dev_id);
    var new_dev_state := Dev_State(pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
    var new_devs := k.subjects.devs[dev_id := new_dev_state];
    var new_subjects := Subjects(k.subjects.drvs, new_devs);

    // Construct k'.objects
    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    //// Clear the objects being activated
    var toactive_hcoded_td_id := dev_state.hcoded_td_id;
    var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};

    //// Modify the PID of these objects (i.e., SetObjsPIDs)
    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, toclear_td_ids, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
    var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);
    var new_objects := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid);

    State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

function ExternalObjsActivate_Func(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, pid:Partition_ID
) : (k':State)
    requires IsValidState(k)

    requires td_ids <= k.objects.inactive_non_hcoded_tds
    requires fd_ids <= k.objects.inactive_fds
    requires do_ids <= k.objects.inactive_dos
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
        // Requirement: no subject owns these external objects

    requires pid != NULL

    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> AllTDIDs(k'.objects) == AllTDIDs(k.objects)
    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> AllFDIDs(k'.objects) == AllFDIDs(k.objects)
    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> AllDOIDs(k'.objects) == AllDOIDs(k.objects)

    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> (forall td_id :: td_id in AllTDIDs(k.objects)
                            ==> (td_id in td_ids ==> td_id in k'.objects.active_non_hcoded_tds &&
                                    k'.objects.active_non_hcoded_tds[td_id] == TD_State(pid, TD_Val(map[], map[], map[]))) &&
                                (td_id !in td_ids ==> ObjStateUnchanged_TD(k.objects, k'.objects, td_id)))
    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> (forall fd_id :: fd_id in AllFDIDs(k.objects)
                            ==> (fd_id in fd_ids ==> fd_id in k'.objects.active_fds &&
                                    k'.objects.active_fds[fd_id] == FD_State(pid, FD_Val(""))) &&
                                (fd_id !in fd_ids ==> ObjStateUnchanged_FD(k.objects, k'.objects, fd_id)))
    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> (forall do_id :: do_id in AllDOIDs(k.objects)
                            ==> (do_id in do_ids ==> do_id in k'.objects.active_dos && 
                                    k'.objects.active_dos[do_id] == DO_State(pid, DO_Val(""))) &&
                                (do_id !in do_ids ==> ObjStateUnchanged_DO(k.objects, k'.objects, do_id)))
{
    // Modify the PID of these objects (i.e., SetObjsPIDs) and clear the objects
    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, td_ids, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fd_ids, pid);
    var k'_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, do_ids, pid);

    State(k.subjects, k'_objects, k.pids, k.tds_to_all_states)
}

function DrvDeactivate_Func(k:State, drv_sid:Subject_ID) : (k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires Drv_ID(drv_sid) in k.subjects.drvs

    requires forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.active_non_hcoded_tds
    requires forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.active_fds
    requires forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.active_dos
{
    var drv_id := Drv_ID(drv_sid);
    var drv_state := IDToDrv(k, drv_id);
    var new_drv_state := Drv_State(NULL, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
    var new_drvs := k.subjects.drvs[drv_id := new_drv_state];

    // Construct k'.subjects
    var new_subjects := Subjects(new_drvs, k.subjects.devs);

    // Construct k'.objects
    var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
    
    //// Modify the PID of these objects
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, tds_owned_by_drv);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_drv);
    var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_drv);

    State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

function DevDeactivate_Func(k:State, dev_sid:Subject_ID) : (k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires Dev_ID(dev_sid) in k.subjects.devs

    requires forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].td_ids && 
                    id != k.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id 
                 ==> id in k.objects.active_non_hcoded_tds
    requires forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].fd_ids ==> id in k.objects.active_fds
    requires forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].do_ids ==> id in k.objects.active_dos
    requires k.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id in k.objects.hcoded_tds
{
    var dev_id := Dev_ID(dev_sid);
    var dev_state := IDToDev(k, dev_id);
    var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
    var new_devs := k.subjects.devs[dev_id := new_dev_state];
    var new_subjects := Subjects(k.subjects.drvs, new_devs);

    // Construct k'.objects
    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    //// Modify the PID of these objects
    var todeactive_hcoded_td_id := dev_state.hcoded_td_id;
    var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
    var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
    var new_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);

    State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

function ExternalObjsDeactivate_Func(
    k:State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
) : (k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires forall id :: id in td_ids ==> id in k.objects.active_non_hcoded_tds
    requires forall id :: id in fd_ids ==> id in k.objects.active_fds
    requires forall id :: id in do_ids ==> id in k.objects.active_dos
{
    // Construct k'.objects
    //// Modify the PID of these objects
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fd_ids);
    var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, do_ids);

    State(k.subjects, new_objects, k.pids, k.tds_to_all_states)
}