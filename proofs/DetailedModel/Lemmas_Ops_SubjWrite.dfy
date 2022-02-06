include "Model_Ops_Predicates.dfy"


lemma Lemma_DM_DevWrite_AllWrittenObjsMustBeInSamePartitionWithDev(
    ws:DM_State, k:State,
    dev_sid:Subject_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(ws.objects))

    requires forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                    FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                    DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
                        // Forall o_id that is an internal ID of any TD/FD/DO in *_id_val_map
            ==> o_id in AllObjsIDs(k.objects) &&
                ObjPID(k, o_id) == SubjPID(k, dev_sid)
        // Property from DevWrite: All written objects are in the same partition with the device

    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_GreenDevWrite_TDsAreUnmodified(
    ws:DM_State, k:State, dev_id:Dev_ID,
    td_id_val_map:map<TD_ID, TD_Val>
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires k == DMStateToState(ws)
    
    requires dev_id in DM_DevsInGreen(ws)
    requires dev_id in AllActiveDevs(k)
    requires dev_id in ws.subjects.devs
        // Requirement: <dev_id> is the ID of an active device in green partition
        
    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_id.sid, td_id2, td_id_val_map[td_id2])
                    
    ensures td_id_val_map == map[]
{
    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    
    var k_params := KToKParams(k);
    var tds_state := ActiveTDsState(k);
    
    if(td_id_val_map != map[])
    {
        Lemma_Map_IfNotEmpty_ThenExistKey(td_id_val_map);
        var id :| id in td_id_val_map;
        var target_td_id := id;
        var write_val := td_id_val_map[id];
        
        var tdx_id := Lemma_K_DevWrite_WriteTDWithValMustBeInATransfer_Apply(k, dev_id.sid, target_td_id, write_val);

        Lemma_K_SecureState_IfDevHasTransferToTD_ThenTheyAreInSamePartition(k, k_params, AllActiveDevs(k), tds_state, dev_id, tdx_id);
        assert SubjPID_DevID(k, dev_id) == ObjPID(k, tdx_id.oid);
        assert tdx_id in DM_TDIDsInGreen(ws);

        // Show conflicts
        //// Apply DM_IsSecureState_SI2
        assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, tds_state, tdx_id);
        assert W !in tds_state[tdx_id].trans_params_tds[target_td_id].amodes;
        assert false;
    }
}

lemma Lemma_GreenDevWrite_TDsInDMObjectsAreSame(
    ws:DM_State, ws':DM_State, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires DM_IsValidState_ObjIDs(ws)
    
    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos
                
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))
    
    requires td_id_val_map == map[]

    ensures forall td_id :: td_id in AllTDIDs(ws.objects)
                ==> ObjStateUnchanged_TD(ws.objects, ws'.objects, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDevWrite_Func_Prove(
    k:State, k':State,
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in k.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in k.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in k.objects.active_dos
                
    requires P_DrvDevWrite_ModificationToState(k, td_id_val_map, fd_id_val_map, do_id_val_map, k')

    ensures k' == DrvDevWrite_Func(k, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_DrvDevWrite_ProveNewDM_FulfillSI2_IfGreenTDsAreUnchanged_PreConditions(
    ws:DM_State, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>, k'_objs:Objects
)
    requires IsValidState_Objects_UniqueObjIDs(ws.objects)
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.active_non_hcoded_tds) &&
            (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.active_fds) &&
            (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.active_dos)

    requires var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            k'_objs == WriteActiveDOsVals(t_objs2, do_id_val_map)

    ensures IsValidState_Objects_UniqueObjIDs(k'_objs) &&
            AllObjsIDs(ws.objects) == AllObjsIDs(k'_objs)
    ensures (forall fd_id :: fd_id in DM_FDIDsInGreen(ws)
                        ==> ObjPID_KObjects(k'_objs, fd_id.oid) == ObjPID_KObjects(ws.objects, fd_id.oid)) &&
            (forall do_id :: do_id in DM_DOIDsInGreen(ws)
                        ==> ObjPID_KObjects(k'_objs, do_id.oid) == ObjPID_KObjects(ws.objects, do_id.oid))
{
    var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var k'_objs := WriteActiveDOsVals(t_objs2, do_id_val_map);
    
    reveal IsValidState_Objects_UniqueObjIDs();

    assert (forall id :: id in AllTDIDs(t_objs1)
                ==> ObjPID_KObjects(t_objs1, id.oid) == ObjPID_KObjects(ws.objects, id.oid)) &&
            (forall id :: id in AllFDIDs(t_objs1)
                ==> ObjPID_KObjects(t_objs1, id.oid) == ObjPID_KObjects(ws.objects, id.oid)) &&
            (forall id :: id in AllDOIDs(t_objs1)
                ==> ObjPID_KObjects(t_objs1, id.oid) == ObjPID_KObjects(ws.objects, id.oid));

    forall id | id in AllTDIDs(k'_objs)
        ensures ObjPID_KObjects(k'_objs, id.oid) == ObjPID_KObjects(ws.objects, id.oid)
    {
        // Dafny can automatically prove it
    }
}

lemma Lemma_DM_DrvDevWrite_ProveP_DMAndNewDM_SameSubjObjPID(
    ws:DM_State, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>, 
    ws':DM_State
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
        // Requirement: Objects have different internal IDs

    requires P_AllHCodedTDsAreObjs(ws)
    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires IsValidState_Objects_UniqueObjIDs(ws.objects)
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.active_non_hcoded_tds) &&
            (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.active_fds) &&
            (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.active_dos)

    requires ws'.subjects == ws.subjects
    requires var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            ws'.objects == WriteActiveDOsVals(t_objs2, do_id_val_map)

    ensures P_DMAndNewDM_SameSubjObjPID(ws, ws')
{
    var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var k'_objs := WriteActiveDOsVals(t_objs2, do_id_val_map);
    
    reveal IsValidState_Objects_UniqueObjIDs();
}




//******** Lemmas for DM_RedDrvWrite ********//
lemma Lemma_NewDM_RedDrvWrite_SameDMAllActiveGreenUSBTDs(
    ws:DM_State, temp_ws':DM_State, ws':DM_State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos

    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))
    requires DM_SubjPID(ws.subjects, s_id) == ws.red_pid
    requires ws'.red_pid == ws.red_pid
    requires temp_ws'.red_pid == ws.red_pid
        // Requirement: PID of red partition is unchanged

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires P_DMObjectsHasUniqueIDs(temp_ws'.objects)
    requires P_AllHCodedTDsAreObjs(temp_ws')
    
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(temp_ws'))
        // Requirement: Proposed driver write 
    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(temp_ws', ws')
        // Requirement: Actual driver write, due to underlying HW functions
    requires DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, s_id, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Requirement: Drivers write objects in the same partition

    ensures DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)
    ensures forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> ObjStateUnchanged_TD(ws.objects, ws'.objects, td_id)
{
    assert forall id :: id in AllTDIDs(ws'.objects)
            ==> DM_ObjPID(ws'.objects, id.oid) == DM_ObjPID(ws.objects, id.oid);
    assert temp_ws'.red_pid == ws.red_pid;

    forall id | id in DM_TDIDsInGreen(ws)
        ensures ObjStateUnchanged_TD(ws.objects, ws'.objects, id)
    {
        assert id in AllTDIDs(ws.objects) &&
                     DM_ObjPID(ws.objects, id.oid) != NULL &&
                     DM_ObjPID(ws.objects, id.oid) != ws.red_pid;

        assert ObjStateUnchanged_TD(ws.objects, temp_ws'.objects, id);
        assert P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(temp_ws', ws');
        assert id in AllTDIDs(temp_ws'.objects);
        assert ObjPID_KObjects(temp_ws'.objects, id.oid) != temp_ws'.red_pid;
        assert ObjStateUnchanged_TD(temp_ws'.objects, ws'.objects, id);
    }
}

lemma Lemma_RedDrvWrite_CommonValidityPropertiesOfNewDM_AndUnchangedPIDsOfGreenFDsDOs(
    ws:DM_State, temp_ws':DM_State, ws':DM_State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos

    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))
    requires DM_SubjPID(ws.subjects, s_id) == ws.red_pid
    requires ws'.red_pid == ws.red_pid
        // Requirement: PID of red partition is unchanged

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(temp_ws'))
        // Requirement: Proposed driver write
    requires DM_IsValidState_SubjsObjsPIDs(temp_ws')
    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_SubjsPIDsRedPID(temp_ws', ws')
    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(temp_ws', ws')
    requires DevHWProt_ReturnGoodSnapshotOfRedTDs(temp_ws', ws')
        // Requirement: Actual driver write, due to underlying HW functions
        
    requires P_DMAndNewDM_SameObjectID(ws, temp_ws')

    ensures P_DMAndNewDM_SameObjectID(ws, ws')
    ensures P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')
    ensures (forall id :: id in AllFDIDs(ws'.objects)
                ==> id in AllFDIDs(ws.objects) &&
                    ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid))
    ensures (forall id :: id in AllDOIDs(ws'.objects)
                ==> id in AllDOIDs(ws.objects) &&
                    ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid))
{
    // Prove DM_IsValidState_SubjsObjsPIDs(out_ws)
    Lemma_NewDM_AlwaysFulfillMostValidityProperties(temp_ws', ws');

    Lemma_NewDM_SameSubjObjIDs(temp_ws', ws');
    Lemma_NewDM_SameSubjObjOwnership(temp_ws', ws');
    Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(temp_ws', ws');
    
    assert P_DMAndNewDM_SameObjectID(ws, temp_ws');
    assert P_DMAndNewDM_SameObjectID(temp_ws', ws');

    // Prove the Property 3 and 4
    forall id | id in AllFDIDs(ws'.objects)
        ensures id in AllFDIDs(ws.objects)
        ensures ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid)
    {
        assert ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(temp_ws'.objects, id.oid);
        assert ObjPID_KObjects(temp_ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid);
    }

    forall id | id in AllDOIDs(ws'.objects)
        ensures id in AllDOIDs(ws.objects)
        ensures ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid)
    {
        assert ObjPID_KObjects(ws'.objects, id.oid) == ObjPID_KObjects(temp_ws'.objects, id.oid);
        assert ObjPID_KObjects(temp_ws'.objects, id.oid) == ObjPID_KObjects(ws.objects, id.oid);
    }
}

lemma Lemma_DrvWrite_NewDM_FulfillSI3(ws:DM_State, ws':DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires (forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects) && DM_SubjPID(ws.subjects, s_id) != NULL
                ==> DM_SubjPID(ws.subjects, s_id) in ws.pids) &&
            (forall o_id :: o_id in DM_AllObjsIDs(ws.objects) && DM_ObjPID(ws.objects, o_id) != NULL
                ==> DM_ObjPID(ws.objects, o_id) in ws.pids)

    requires ws.pids == ws'.pids

    requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    requires DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_SubjPID(ws'.subjects, s_id) == DM_SubjPID(ws.subjects, s_id)
    requires forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id)

    ensures (forall s_id :: s_id in DM_AllSubjsIDs(ws'.subjects) && DM_SubjPID(ws'.subjects, s_id) != NULL
                ==> DM_SubjPID(ws'.subjects, s_id) in ws'.pids) &&
            (forall o_id :: o_id in DM_AllObjsIDs(ws'.objects) && DM_ObjPID(ws'.objects, o_id) != NULL
                ==> DM_ObjPID(ws'.objects, o_id) in ws'.pids)
    ensures DM_IsSecureState_SI3(ws')
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_RedDrvWrite_SameDMAllObjsIDsAndObjPIDs(
    ws:DM_State, temp_ws':DM_State, ws':DM_State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos

    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))
    requires DM_SubjPID(ws.subjects, s_id) == ws.red_pid
    requires ws'.red_pid == ws.red_pid
        // Requirement: PID of red partition is unchanged

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires P_DMObjectsHasUniqueIDs(temp_ws'.objects)
    requires P_AllHCodedTDsAreObjs(temp_ws')
    
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(temp_ws'))
        // Requirement: Proposed driver write 
    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(temp_ws', ws')
        // Requirement: Actual driver write, due to underlying HW functions
    requires DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, s_id, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Requirement: Drivers write objects in the same partition

    ensures DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    ensures forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_RedDrvWrite_MappedStateOfNewDMIsProposedWriteResultOfMappedStateOfDM(
    ws:DM_State, temp_ws':DM_State, ws':DM_State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos

    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))
    requires DM_SubjPID(ws.subjects, s_id) == ws.red_pid
    requires ws'.red_pid == ws.red_pid
        // Requirement: PID of red partition is unchanged

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires P_DMObjectsHasUniqueIDs(temp_ws'.objects)
    requires P_AllHCodedTDsAreObjs(temp_ws')
    
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(temp_ws'))
        // Requirement: Proposed driver write
    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_SubjsPIDsRedPID(temp_ws', ws')
    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(temp_ws', ws')
        // Requirement: Actual driver write, due to underlying HW functions
    requires DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, s_id, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Requirement: Drivers write objects in the same partition

    ensures MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds)
        // Properties needed by the following property
    ensures DMStateToState(ws') == DrvWrite_ProposedNewState(DMStateToState(ws), 
                                        TDsStateDiff(TDStateToTDVal(ws'.objects.active_non_hcoded_tds), TDStateToTDVal(ws.objects.active_non_hcoded_tds)),
                                        fd_id_val_map, do_id_val_map)
        // Property: The result state is the combination of the write
    ensures ws'.objects.hcoded_tds == ws.objects.hcoded_tds
        // Property: Nice to have
{
    var k := DMStateToState(ws);
    var ws_k' := DMStateToState(ws');

    // Prove MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds)
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    assert MapGetKeys(temp_ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds);
    assert MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(temp_ws'.objects.active_non_hcoded_tds);

    var td_id_val_map2 := TDsStateDiff(TDStateToTDVal(ws'.objects.active_non_hcoded_tds), TDStateToTDVal(ws.objects.active_non_hcoded_tds));

    // Prove ws_k' == DrvWrite_ProposedNewState(k, td_id_val_map2, fd_id_val_map, do_id_val_map)
    assert ws_k'.subjects == k.subjects;
    assert ws_k'.pids == k.pids;
    assert ws_k'.tds_to_all_states == k.tds_to_all_states;

    assert ws_k' == DrvWrite_ProposedNewState(k, td_id_val_map2, fd_id_val_map, do_id_val_map);
}

lemma Lemma_RedDrvWrite_ProveP_DrvWrite_ReturnTrue_Def(
    k:State, proposed_k':State, drv_sid:Subject_ID,
    td_id_val_map2:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires IsValidState(k)
    requires IsValidState(proposed_k') && IsSecureState(proposed_k')
    
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires forall td_id2 :: td_id2 in td_id_val_map2
                ==> td_id2 in k.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in k.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in k.objects.active_dos

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map2
        // Requirement: The driver does not write any hardcoded TDs
        
    requires (forall fd_id :: fd_id in fd_id_val_map ==>
                SubjPID(k, drv_sid) == ObjPID(k, fd_id.oid))
    requires (forall do_id :: do_id in do_id_val_map ==>
                SubjPID(k, drv_sid) == ObjPID(k, do_id.oid))
    requires (forall td_id :: td_id in td_id_val_map2 ==>
                SubjPID(k, drv_sid) == ObjPID(k, td_id.oid))

    requires proposed_k' == DrvWrite_ProposedNewState(k, td_id_val_map2, fd_id_val_map, do_id_val_map)

    ensures P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map2, fd_id_val_map, do_id_val_map)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_RedDrvWrite_PIDsOfAllTDsInTDDValMap2AreUnmodified(
    ws:DM_State, k:State, temp_ws':DM_State, ws':DM_State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    td_id_val_map2:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires k == DMStateToState(ws)

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos

    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))
    requires DM_SubjPID(ws.subjects, s_id) == ws.red_pid
    requires ws'.red_pid == ws.red_pid
        // Requirement: PID of red partition is unchanged

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires P_DMObjectsHasUniqueIDs(temp_ws'.objects)
    requires P_AllHCodedTDsAreObjs(temp_ws')
    
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(temp_ws'))
        // Requirement: Proposed driver write
    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_SubjsPIDsRedPID(temp_ws', ws')
    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(temp_ws', ws')
        // Requirement: Actual driver write, due to underlying HW functions
    requires DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, s_id, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Requirement: Drivers write objects in the same partition

    requires td_id_val_map2 == TDsStateDiff(TDStateToTDVal(ws'.objects.active_non_hcoded_tds), TDStateToTDVal(ws.objects.active_non_hcoded_tds))
    
    ensures (forall td_id :: td_id in td_id_val_map2 ==>
                SubjPID(k, s_id) == ObjPID(k, td_id.oid))
{
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);

    forall td_id | td_id in td_id_val_map2
        ensures DM_SubjPID(ws.subjects, s_id) == DM_ObjPID(ws.objects, td_id.oid)
        ensures SubjPID(k, s_id) == ObjPID(k, td_id.oid)
    {
        if(DM_SubjPID(ws.subjects, s_id) != DM_ObjPID(ws.objects, td_id.oid))
        {
            assert td_id !in DM_TDIDsInRed(ws);
            assert td_id !in DM_TDIDsInRed(temp_ws');
            assert ObjStateUnchanged_TD(temp_ws'.objects, ws'.objects, td_id);

            // Show conflict
            assert td_id in td_id_val_map;
            //// Apply P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(temp_ws'))
            assert DM_SubjPID(ws.subjects, s_id) == DM_ObjPID(ws.objects, td_id.oid);
        }
    }
}




//******** Lemmas for DM_GreenDrvWrite ********//
lemma Lemma_NewDM_GreenDrvWrite_SameDMAllObjsIDsAndObjPIDs(
    ws:DM_State, ws':DM_State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos

    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))
        // Requirement: Proposed driver write 
    requires DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, s_id, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Requirement: Drivers write objects in the same partition

    ensures DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    ensures forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_GreenDrvWrite_SameDMRedTDs(
    ws:DM_State, ws':DM_State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos

    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))
    requires DM_SubjPID(ws.subjects, s_id) != ws'.red_pid
    requires ws'.red_pid == ws.red_pid

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))
        // Requirement: Proposed driver write 
    requires DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, s_id, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Requirement: Drivers write objects in the same partition

    ensures forall td_id :: td_id in DM_TDIDsInRed(ws')
                ==> DM_IsSameTD(ws'.objects, ws.objects, td_id)
        // Property: TDs in red are unmodified
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_GreenDrvWrite_SameDMAllActiveGreenTDIDs(
    ws:DM_State, ws':DM_State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos

    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))
    requires ws'.red_pid == ws.red_pid

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))
        // Requirement: Proposed driver write 
    requires DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, s_id, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Requirement: Drivers write objects in the same partition

    ensures DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)
{
    // Dafny can automatically prove this lemma
}

// [NOTE] Needs 50s to verify
lemma Lemma_DM_GreenDrvWrite_FulfillSI2(
    ws:DM_State, k:State, ws':DM_State, k':State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires DM_IsValidState_Subjects(ws) && DM_IsValidState_Objects(ws)
    
    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos
                
    requires forall td_id :: td_id in td_id_val_map
                ==> td_id !in DM_AllHCodedTDIDs(ws.subjects)
        // Property from DevWrite: Hardcoded TDs are not modified
    requires forall id :: id in td_id_val_map
                ==> DM_ObjPID(ws.objects, id.oid) != NULL
        // Requirement: TDs in <td_id_val_map> are active

    requires ws'.subjects == ws.subjects
    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires ws'.red_pid == ws.red_pid

    requires k' == DMStateToState(ws')
    requires k == DMStateToState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))
                
    requires forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id)
        // Requirement: Objects' PIDs are not changed
            
    requires forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id)
        // Requirement: <ws> fulfills SI2

    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))
        // Requirement: Proposed driver write 
    requires DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, s_id, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Requirement: Drivers write objects in the same partition
    requires DM_GreenDrvWrite_ChkNewValsOfTDs(ws, td_id_val_map)

    ensures KToKParams(k') == KToKParams(k)
    ensures forall td_id :: td_id in DM_TDIDsInGreen(ws')
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k'), ActiveTDsState(k'), td_id)
{
    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');

    // Prove KToKParams(k) == KToKParams(k')
    Lemma_DrvDevWrite_NewKParams_SameWithKParams(k, k'.subjects, k'.objects, k'_params);
    assert k_params == k'_params;
    
    // Prove DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)
    Lemma_NewDM_GreenDrvWrite_SameDMAllActiveGreenTDIDs(ws, ws', s_id, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws);

    forall td_id | td_id in DM_TDIDsInGreen(ws')
        ensures DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, ActiveTDsState(k'), td_id)
    {
        if(td_id in td_id_val_map)
        {
            assert DM_GreenDrvWrite_ChkNewValsOfTDs(ws, td_id_val_map);
            var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
            assert t_objs1.active_non_hcoded_tds == k'.objects.active_non_hcoded_tds;

            Lemma_K_SameObjIDs_ProveIsValidState_Objects_UniqueObjIDs(ws.objects, t_objs1);
            assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, ActiveTDsState_SlimState(t_objs1), td_id);
        }
        else
        {
            assert ActiveTDsState(k)[td_id] == ActiveTDsState(k')[td_id];
            Lemma_TwoTDStatesUnchangedTD_ProveDoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, ActiveTDsState(k), ActiveTDsState(k'), td_id);
            assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, ActiveTDsState(k'), td_id);
        }
    }
}

lemma Lemma_NewDM_GreenDrvWrite_SameTDsInRed(
    ws:DM_State, ws':DM_State, s_id:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in ws.objects.active_non_hcoded_tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in ws.objects.active_fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in ws.objects.active_dos

    requires DM_IsDrvID(ws.subjects, Drv_ID(s_id))
    requires DM_SubjPID(ws.subjects, s_id) != NULL
    requires DM_SubjPID(ws.subjects, s_id) != ws.red_pid
    requires ws'.red_pid == ws.red_pid

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    
    requires P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))
        // Requirement: Proposed driver write 
    requires DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, s_id, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Requirement: Drivers write objects in the same partition

    requires DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    requires DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects)
    requires forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id)

    ensures forall td_id :: td_id in DM_TDIDsInRed(ws')
                ==> DM_IsSameTD(ws'.objects, ws.objects, td_id)
{
    Lemma_DM_AllObjsIDs_Property();

    forall td_id | td_id in DM_TDIDsInRed(ws')
        ensures DM_IsSameTD(ws'.objects, ws.objects, td_id)
    {
        assert td_id in DM_TDIDsInRed(ws);
    }
}