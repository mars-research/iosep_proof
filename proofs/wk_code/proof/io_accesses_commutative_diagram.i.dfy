include "utils_wimp_accesses.s.dfy"
include "utils_os_accesses.i.dfy"
include "io_accesses_ops_lemmas.i.dfy"
include "../state_properties_OpsSaneStateSubset.i.dfy"

lemma Lemma_OSDrvRead_ProveCommutativeDiagram(
    s:state, dm:DM_State, drv_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires OpsSaneState(s)

    requires dm == WSM_MapSecureState(s)
    requires P_OSDrvAccess_AccessActiveObjsOnly(s, read_tds, read_fds, read_dos)
    requires forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==> id !in read_tds
        // Requirement: Written objects are not hardcoded TDs

    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    ensures var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            DM_RedDrvRead_PreConditions(dm, drv_sid, read_objs, map[], map[], map[])
    ensures var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            DM_RedDrvRead_InnerFunc(dm, drv_sid, read_objs, map[], map[], map[]) == (dm, true)
{
    var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, read_tds, read_fds, read_dos);
    assert read_objs <= WSM_AllObjIDs(s.objects);

    // Prove DM_RedDrvRead_PreConditions
    Lemma_DrvDevRead_HCodedTDsAreNotInParams(s, read_tds, read_fds, read_dos);
    assert DM_RedDrvRead_PreConditions(dm, drv_sid, read_objs, map[], map[], map[]);

    // Prove DM_RedDrvRead_InnerFunc
    Lemma_OSDrvRead_ProveSubjsObjsInSamePartition(s, dm, drv_sid, read_tds, read_fds, read_dos);
    
    //// Apply DM_RedDrvWrite_InnerFunc
    var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, map[]);
    var t_objs2 := WriteActiveFDsVals(t_objs1, map[]);
    var t_objs3 := WriteActiveDOsVals(t_objs2, map[]);
    Lemma_WriteActiveNonHCodedTDsVals_Property_EmptyWriteList(dm.objects);
    Lemma_WriteActiveFDsVals_Property_EmptyWriteList(dm.objects);
    Lemma_WriteActiveDOsVals_Property_EmptyWriteList(dm.objects);
    assert t_objs3 == dm.objects;

    // Prove drvread_result == (dm, true)
    Lemma_DM_DrvDevRead_ReplaceSrcTDWithVal_Property_EmptyWriteList(dm);
    Lemma_DM_DrvDevRead_ReplaceSrcFDWithVal_Property_EmptyWriteList(dm);
    Lemma_DM_DrvDevRead_ReplaceSrcDOWithVal_Property_EmptyWriteList(dm);
    assert DM_RedDrvWrite_InnerFunc(dm, drv_sid, map[], map[], map[]).1 == dm;
    
    var drvread_result := DM_RedDrvRead_InnerFunc(dm, drv_sid, read_objs, map[], map[], map[]);
    Lemma_DM_RedDrvRead_InnerFunc_Properties(dm, drv_sid, read_objs, map[], map[], map[], drvread_result);
    assert drvread_result.1 == true;
    assert drvread_result.0 == DM_RedDrvWrite_InnerFunc(dm, drv_sid, map[], map[], map[]).1;
    assert drvread_result.0 == dm;
    assert drvread_result == (dm, true);
}

lemma Lemma_DevRead_ProveCommutativeDiagram(
    s:state, dm:DM_State, dev_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    //requires WSM_IsUSBPDevID(s.subjects, Dev_ID(dev_sid))  
    requires WSM_IsDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: The device must be active

    requires WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)
        // Requirement: If the device reads a set of TDs/FDs/DOs, then the device must be able to read the 
        // corresponding objects in the WK design model

    requires (forall td_id :: td_id in read_tds ==> td_id in AllTDIDs(dm.objects)) &&
             (forall fd_id :: fd_id in read_fds ==> fd_id in AllFDIDs(dm.objects)) &&
             (forall do_id :: do_id in read_dos ==> do_id in AllDOIDs(dm.objects)) 
    requires DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, read_tds, read_fds, read_dos)
        // Requirement: Device and written objects are in the same partition
    requires forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==> id !in read_tds
        // Requirement: Written objects are not hardcoded TDs

    ensures var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            DM_DevRead_PreConditions(dm, dev_sid, read_objs, map[], map[], map[])
    ensures var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            DM_DevRead_InnerFunc(dm, dev_sid, read_objs, map[], map[], map[]) == (dm, true)
{
    var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, read_tds, read_fds, read_dos);
    assert read_objs <= WSM_AllObjIDs(s.objects);

    // Prove DM_DevRead_PreConditions
    Lemma_DrvDevRead_HCodedTDsAreNotInParams(s, read_tds, read_fds, read_dos);
    Lemma_WSM_DevRead_TransfersMustBeDefinedInWSDesignModel_ImpliesDM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(
        s, dm, dev_sid, read_tds, read_fds, read_dos);
    assert DM_DevRead_PreConditions(dm, dev_sid, read_objs, map[], map[], map[]);

    // Prove DM_RedDrvRead_InnerFunc
    Lemma_DevRead_ProveSubjsObjsInSamePartition(s, dm, dev_sid, read_tds, read_fds, read_dos);
    
    //// Apply DM_RedDrvWrite_InnerFunc
    var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, map[]);
    var t_objs2 := WriteActiveFDsVals(t_objs1, map[]);
    var t_objs3 := WriteActiveDOsVals(t_objs2, map[]);
    Lemma_WriteActiveNonHCodedTDsVals_Property_EmptyWriteList(dm.objects);
    Lemma_WriteActiveFDsVals_Property_EmptyWriteList(dm.objects);
    Lemma_WriteActiveDOsVals_Property_EmptyWriteList(dm.objects);
    assert t_objs3 == dm.objects;

    // Prove devread_result == (dm, true)
    Lemma_DM_DrvDevRead_ReplaceSrcTDWithVal_Property_EmptyWriteList(dm);
    Lemma_DM_DrvDevRead_ReplaceSrcFDWithVal_Property_EmptyWriteList(dm);
    Lemma_DM_DrvDevRead_ReplaceSrcDOWithVal_Property_EmptyWriteList(dm);
    //assert DM_RedDevWrite_InnerFunc(dm, dev_sid, map[], map[], map[]).0 == dm;
    
    var devread_result := DM_DevRead_InnerFunc(dm, dev_sid, read_objs, map[], map[], map[]);
    assert devread_result.1 == true;
    assert devread_result.0 == dm;
    assert devread_result == (dm, true);
}

lemma Lemma_OSDrvWrite_ProveCommutativeDiagram(
    s:state, dm:DM_State, drv_sid:Subject_ID, 
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    ts':state, s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires P_OSDrvAccess_AccessActiveObjsOnly(s, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
    requires td_id_val_map == OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map) &&
             fd_id_val_map == wsm_fd_id_val_map &&
             do_id_val_map == wsm_do_id_val_map
    requires forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==>id !in wsm_td_id_val_map
        // Requirement: The objects written by the driver must be active in the OS partition, and cannot be hardcoded TDs

    requires forall id :: id in wsm_td_id_val_map ==> id in s.objects.os_tds
    requires forall id :: id in wsm_fd_id_val_map ==> id in s.objects.os_fds
    requires forall id :: id in wsm_do_id_val_map ==> id in s.objects.os_dos
    requires var os_tds' := WSM_WriteOSTDsVals(s.objects.os_tds, wsm_td_id_val_map);
             var os_fds' := WSM_WriteOSFDsVals(s.objects.os_fds, wsm_fd_id_val_map);
             var os_dos' := WSM_WriteOSDOsVals(s.objects.os_dos, wsm_do_id_val_map);
             var ts'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
             ts' == s.(objects := ts'_objs)
    requires OpsSaneStateSubset(ts')
        // Requirement: Relationship between s and ts'

    requires OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(ts')
    requires P_WimpObjs_HaveNoPIOAddr(ts')
    requires OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(ts')
    requires P_PEHCIsObjs_HaveNoPIOAddr(ts')
    requires s' == IOMMU_DevHWProt(ts')
        // Requirement: Relationship between ts' and s'
    
    ensures DM_RedDrvWrite_PreConditions(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures DM_RedDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == WSM_MapState(s')
    ensures DM_RedDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2 == true
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures WSD_OSDrvWrite_Stub(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true)
        // Property 2
{
    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, td_ids, fd_ids, do_ids);

    // Prove DM_RedDrvRead_PreConditions
    Lemma_OSDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition(s, dm, drv_sid,
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert DM_RedDrvWrite_PreConditions(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove DM_RedDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2 == true
    assert DM_RedDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2 == true;

    // Prove DM_RedDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == dm
    var drvwrite_result := DM_RedDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var t_dm' := WSM_MapState(ts');
    Lemma_OSDrvDevWrite_ProveOperationMapping(s, ts', dm, t_dm', 
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert t_dm' == drvwrite_result.0;

    //// Apply IOMMU_DevHWProt
    var dm' := WSM_MapState(s');
    Lemma_IOMMU_DevHWProt_Refines_DevHWProt(s, ts');
    assert dm' == drvwrite_result.1;

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_OSDrvWrite_Stub(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (drvwrite_result.1, drvwrite_result.2);
}

lemma Lemma_OSDevWrite_ProveCommutativeDiagram(
    s:state, dm:DM_State, dev_sid:Subject_ID, 
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
    requires P_OSDevWrite_AccessOSObjsOnly(s, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
    requires td_id_val_map == OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map) &&
             fd_id_val_map == wsm_fd_id_val_map &&
             do_id_val_map == wsm_do_id_val_map
    requires forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==>id !in wsm_td_id_val_map
        // Requirement: The objects written by the driver must be active in the OS partition, and cannot be hardcoded TDs

    requires forall id :: id in wsm_td_id_val_map ==> id in s.objects.os_tds
    requires forall id :: id in wsm_fd_id_val_map ==> id in s.objects.os_fds
    requires forall id :: id in wsm_do_id_val_map ==> id in s.objects.os_dos
    requires var os_tds' := WSM_WriteOSTDsVals(s.objects.os_tds, wsm_td_id_val_map);
             var os_fds' := WSM_WriteOSFDsVals(s.objects.os_fds, wsm_fd_id_val_map);
             var os_dos' := WSM_WriteOSDOsVals(s.objects.os_dos, wsm_do_id_val_map);
             var s'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
             s' == s.(objects := s'_objs)
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and ts'
    
    ensures DM_RedDevWrite_PreConditions(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == WSM_MapState(s')
    ensures DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true)
        // Property 2
{
    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, td_ids, fd_ids, do_ids);

    // Prove DM_RedDrvRead_PreConditions
    assert DM_RedDevWrite_PreConditions(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
    assert DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true;

    // Prove DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == dm
    var devwrite_result := DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var dm' := WSM_MapState(s');
    Lemma_OSDrvDevWrite_ProveOperationMapping(s, s', dm, dm', 
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert dm' == devwrite_result.0;

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (devwrite_result.0, devwrite_result.1);
}

// [NOTE] Needs 50s to verify
lemma {:timeLimitMultiplier 7} Lemma_WimpDrvRead_ProveCommutativeDiagram(
    s:state, dm:DM_State, drv_id:Drv_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsWimpDrvID(s.subjects, drv_id)
    requires var globals := wkm_get_globals(s.wk_mstate);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_id.sid) 
                in pids_parse_g_wimp_pids(globals)
        // Requirement: The driver is in the green partition

    requires WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_id.sid, read_tds, read_fds, read_dos)
    requires forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==> id !in read_tds
        // Requirement: Written objects are not hardcoded TDs

    ensures var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            DM_GreenDrvRead_PreConditions(dm, drv_id.sid, read_objs, map[], map[], map[])
    ensures var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            DM_GreenDrvRead_InnerFunc(dm, drv_id.sid, read_objs, map[], map[], map[]) == (dm, true)
{
    var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, read_tds, read_fds, read_dos);
    assert read_objs <= WSM_AllObjIDs(s.objects);

    // Prove DM_RedDrvRead_PreConditions
    Lemma_DrvDevRead_HCodedTDsAreNotInParams(s, read_tds, read_fds, read_dos);
    assert DM_GreenDrvRead_PreConditions(dm, drv_id.sid, read_objs, map[], map[], map[]);

    // Prove DM_RedDrvRead_InnerFunc
    Lemma_WimpDrvRead_ProveSubjsObjsInSamePartition(s, dm, drv_id, read_tds, read_fds, read_dos);
    
    //// Apply DM_RedDrvWrite_InnerFunc
    var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, map[]);
    var t_objs2 := WriteActiveFDsVals(t_objs1, map[]);
    var t_objs3 := WriteActiveDOsVals(t_objs2, map[]);
    Lemma_WriteActiveNonHCodedTDsVals_Property_EmptyWriteList(dm.objects);
    Lemma_WriteActiveFDsVals_Property_EmptyWriteList(dm.objects);
    Lemma_WriteActiveDOsVals_Property_EmptyWriteList(dm.objects);
    assert t_objs3 == dm.objects;

    // Prove drvread_result == (dm, true)
    Lemma_DM_DrvDevRead_ReplaceSrcTDWithVal_Property_EmptyWriteList(dm);
    Lemma_DM_DrvDevRead_ReplaceSrcFDWithVal_Property_EmptyWriteList(dm);
    Lemma_DM_DrvDevRead_ReplaceSrcDOWithVal_Property_EmptyWriteList(dm);
    assert DM_GreenDrvWrite_InnerFunc(dm, drv_id.sid, map[], map[], map[]).0 == dm;

    assert DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_id.sid, map[], map[], map[]);
    assert DM_GreenDrvWrite_ChkNewValsOfTDs(dm, map[]);
    assert DM_GreenDrvWrite_InnerFunc(dm, drv_id.sid, map[], map[], map[]).1 == true;
    
    var drvread_result := DM_GreenDrvRead_InnerFunc(dm, drv_id.sid, read_objs, map[], map[], map[]);
    Lemma_DM_GreenDrvRead_InnerFunc_Properties(dm, drv_id.sid, read_objs, map[], map[], map[], drvread_result);
    assert drvread_result.1 == true;
    assert drvread_result.0 == DM_GreenDrvWrite_InnerFunc(dm, drv_id.sid, map[], map[], map[]).0;
    assert drvread_result.0 == dm;
    assert drvread_result == (dm, true);
}

lemma Lemma_WimpDrvWriteOwnDO_ProveCommutativeDiagram(
    s:state, dm:DM_State, drv_sid:Subject_ID, 
    do_id_val_map:map<DO_ID, DO_Val>,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsWimpDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) in 
                pids_parse_g_wimp_pids(wkm_get_globals(s.wk_mstate))
        // Requirement: The driver is in a green partition

    requires forall id :: id in do_id_val_map ==> id in s.objects.wimpdrv_dos
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in do_id_val_map
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid)
    requires var new_wimpdrv_dos := WSM_WriteDOsVals(s.objects.wimpdrv_dos, do_id_val_map);
             s' == s.(objects := s.objects.(wimpdrv_dos := new_wimpdrv_dos))
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and ts' 
    
    ensures DM_GreenDrvWrite_PreConditions(dm, drv_sid, map[], map[], do_id_val_map)
    ensures DM_GreenDrvWrite_InnerFunc(dm, drv_sid, map[], map[], do_id_val_map).0 == WSM_MapState(s')
    ensures DM_GreenDrvWrite_InnerFunc(dm, drv_sid, map[], map[], do_id_val_map).1 == true
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures WSD_WimpDrvWrite_Stub(dm, drv_sid, map[], map[], do_id_val_map) == (WSM_MapState(s'), true)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
{
    var td_id_val_map:map<TD_ID, TD_Val> := map[];
    var fd_id_val_map:map<FD_ID, FD_Val> := map[];

    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, td_ids, fd_ids, do_ids);

    // Prove DM_RedDrvRead_PreConditions
    assert DM_GreenDrvWrite_PreConditions(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove DM_GreenDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
    Lemma_WimpDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition(s, dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert DM_GreenDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true;

    // Prove DM_GreenDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == dm
    var drvwrite_result := DM_GreenDrvWrite_InnerFunc(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var dm' := WSM_MapState(s');
    Lemma_WimpDrvWriteOwnDO_ProveOperationMapping(s, s', dm, dm', do_id_val_map);
    assert dm' == drvwrite_result.0;

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_WimpDrvWrite_Stub(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (drvwrite_result.0, drvwrite_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_USBPDevWrite_ProveCommutativeDiagram(
    s:state, dm:DM_State, dev_sid:Subject_ID, 
    fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsUSBPDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: The device must be active

    requires WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, map[], fd_id_val_map, do_id_val_map)
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
				==> fd_id2 in s.subjects.usbpdevs[Dev_ID(dev_sid)].fd_ids
    requires forall do_id2 :: do_id2 in do_id_val_map
				==> do_id2 in s.subjects.usbpdevs[Dev_ID(dev_sid)].do_ids
        // Requirement: The USBPDev owns the objects to be accessed

    requires forall id :: id in fd_id_val_map ==> id in s.objects.usbpdev_fds
    requires forall id :: id in do_id_val_map ==> id in s.objects.usbpdev_dos
    requires var new_usbpdevs_fds := WSM_WriteFDsVals(s.objects.usbpdev_fds, fd_id_val_map);
	         var new_usbpdevs_dos := WSM_WriteDOsVals(s.objects.usbpdev_dos, do_id_val_map);
             s' == s.(objects := s.objects.(usbpdev_fds := new_usbpdevs_fds, usbpdev_dos := new_usbpdevs_dos))
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and ts'
    
    ensures DM_DevWrite_PreConditions(dm, dev_sid, map[], fd_id_val_map, do_id_val_map)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures WSD_DevWrite_Stub(dm, dev_sid, map[], fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
{
    var globals := wkm_get_globals(s.wk_mstate);

    var td_id_val_map:map<TD_ID, TD_Val> := map[];
    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, td_ids, fd_ids, do_ids);

    // Prove DM_RedDrvRead_PreConditions
    assert DM_DevWrite_PreConditions(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    Lemma_USBPDevWrite_ProveCommutativeDiagram_FDsAndDOsMustInActiveSet(s, dm, dev_sid, fd_ids, do_ids);
    var pid := DM_SubjPID(dm.subjects, dev_sid);
    assert pid != NULL;
    if(pid != dm.red_pid)
    {
        // Prove DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
        assert DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true;

        // Prove DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == dm
        var devwrite_result := DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        var dm' := WSM_MapState(s');
        Lemma_USBPDevWrite_ProveOperationMapping(s, s', dm, dm', fd_id_val_map, do_id_val_map);
        assert dm' == devwrite_result.0;

        // Prove property 2
        Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
        assert WSD_DevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (devwrite_result.0, devwrite_result.1);
    }
    else
    {
        assert pid == dm.red_pid;

        // Prove DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
        assert DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true;

        // Prove DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == dm
        var devwrite_result := DM_RedDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        var dm' := WSM_MapState(s');
        Lemma_USBPDevWrite_ProveOperationMapping(s, s', dm, dm', fd_id_val_map, do_id_val_map);
        assert dm' == devwrite_result.0;

        // Prove property 2
        Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
        assert WSD_DevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (devwrite_result.0, devwrite_result.1);
    }

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_EEHCIWriteWriteOwnDO_ProveCommutativeDiagram(
    s:state, dm:DM_State, eehci_id_word:word, eehci_slot:word,
    offset:uint32, new_val:word,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID) &&
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: the device must be in a wimp partition
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID) &&
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI

    requires offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset
        // Requirement: eEHCIs can only write this DO
        // [NOTE] Actually, eEHCIs can not write any other owned objects
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             var t_write_params := WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(s, eehci_id_word, dev_id, offset, new_val);
             WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, t_write_params.0, t_write_params.1, t_write_params.2)
        // Requirement: If the device writes a set of TDs/FDs/DOs, then the corresponding transfers must also be defined 
        // in the WK design model

    requires var old_globals := wkm_get_globals(s.wk_mstate);
             var new_globals := eehci_mem_set_status_reg(old_globals, eehci_slot, new_val);
             s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and ts'
    
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var t_write_params := WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(s, eehci_id_word, dev_id, offset, new_val);
            DM_GreenDevWrite_PreConditions(dm, dev_id.sid, t_write_params.0, t_write_params.1, t_write_params.2)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var t_write_params := WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(s, eehci_id_word, dev_id, offset, new_val);
            WSD_WimpDevWrite_Stub(dm, dev_id.sid, t_write_params.0, t_write_params.1, t_write_params.2) == (WSM_MapState(s'), true)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
{
    var globals := wkm_get_globals(s.wk_mstate);
    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    var dev_sid := dev_id.sid;

    var t_write_params := WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(s, eehci_id_word, dev_id, offset, new_val);
    var td_id_val_map:map<TD_ID, TD_Val> := t_write_params.0;
    var fd_id_val_map:map<FD_ID, FD_Val> := t_write_params.1;
    var do_id_val_map:map<DO_ID, DO_Val> := t_write_params.2;
    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, td_ids, fd_ids, do_ids);

    // Prove DM_GreenDevWrite_PreConditions
    Lemma_SaneWSMState_MapSubjGreenPID(s, dm, dev_sid);
    assert DM_GreenDevWrite_PreConditions(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    Lemma_EEHCIvWriteOwnDO_ProveCommutativeDiagram_DOsMustInActiveSet(s, dm, dev_sid, do_ids);
    var pid := DM_SubjPID(dm.subjects, dev_sid);
    assert pid != dm.red_pid;

    // Prove DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
    assert DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true;

    // Prove DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == dm
    var devwrite_result := DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var dm' := WSM_MapState(s');
    Lemma_EEHCIWriteOwnDO_ProveOperationMapping(s, s', dm, dm', eehci_id_word, eehci_slot, do_id_val_map, new_val);
    assert dm' == devwrite_result.0;

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_WimpDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (devwrite_result.0, devwrite_result.1);
    
    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_EEHCIWriteUSBPDevObjs_ProveCommutativeDiagram(
    s:state, dm:DM_State, eehci_id_word:word, eehci_slot:word,
    fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID) &&
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: the device must be in a wimp partition
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID) &&
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI

    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, map[], fd_id_val_map, do_id_val_map)
        // Requirement: If the device writes a set of TDs/FDs/DOs, then the corresponding transfers must also be defined 
        // in the WK design model
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             P_EEHCIWriteUSBPDevObjs(s, dev_id, fd_id_val_map, do_id_val_map)

    requires forall id :: id in fd_id_val_map ==> id in s.objects.usbpdev_fds
    requires forall id :: id in do_id_val_map ==> id in s.objects.usbpdev_dos
    requires var new_usbpdevs_fds := WSM_WriteFDsVals(s.objects.usbpdev_fds, fd_id_val_map);
	         var new_usbpdevs_dos := WSM_WriteDOsVals(s.objects.usbpdev_dos, do_id_val_map);
             s' == s.(objects := s.objects.(usbpdev_fds := new_usbpdevs_fds, usbpdev_dos := new_usbpdevs_dos))
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and ts'
    
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            DM_GreenDevWrite_PreConditions(dm, dev_id.sid, map[], fd_id_val_map, do_id_val_map)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            WSD_WimpDevWrite_Stub(dm, dev_id.sid, map[], fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
{
    var globals := wkm_get_globals(s.wk_mstate);
    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    var dev_sid := dev_id.sid;

    var td_id_val_map:map<TD_ID, TD_Val> := map[];
    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, td_ids, fd_ids, do_ids);

    // Prove DM_GreenDevWrite_PreConditions
    Lemma_SaneWSMState_MapSubjGreenPID(s, dm, dev_sid);
    assert DM_GreenDevWrite_PreConditions(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
    assert DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true;

    // Prove DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == dm
    var devwrite_result := DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var dm' := WSM_MapState(s');
    Lemma_USBPDevWrite_ProveOperationMapping(s, s', dm, dm', fd_id_val_map, do_id_val_map);
    assert dm' == devwrite_result.0;

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_WimpDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (devwrite_result.0, devwrite_result.1);
    
    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_EEHCIWriteWimpDrvDO_ProveCommutativeDiagram(
    s:state, dm:DM_State, eehci_id_word:word, eehci_slot:word,
    do_id_val_map:map<DO_ID, DO_Val>,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID) &&
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: the device must be in a wimp partition
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID) &&
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI

    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, map[], map[], do_id_val_map)
        // Requirement: If the device writes a set of TDs/FDs/DOs, then the corresponding transfers must also be defined 
        // in the WK design model
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             P_EEHCIWriteWimpDrvDO(s, dev_id, do_id_val_map)

    requires forall id :: id in do_id_val_map ==> id in s.objects.wimpdrv_dos
    requires var new_wimpdrv_dos := WSM_WriteDOsVals(s.objects.wimpdrv_dos, do_id_val_map);
             s' == s.(objects := s.objects.(wimpdrv_dos := new_wimpdrv_dos));
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and ts'
    
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            DM_GreenDevWrite_PreConditions(dm, dev_id.sid, map[], map[], do_id_val_map)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            WSD_WimpDevWrite_Stub(dm, dev_id.sid, map[], map[], do_id_val_map) == (WSM_MapState(s'), true)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
{
    var globals := wkm_get_globals(s.wk_mstate);
    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    var dev_sid := dev_id.sid;

    var td_id_val_map:map<TD_ID, TD_Val> := map[];
    var fd_id_val_map:map<FD_ID, FD_Val> := map[];
    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);
    Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s, td_ids, fd_ids, do_ids);

    // Prove DM_GreenDevWrite_PreConditions
    Lemma_SaneWSMState_MapSubjGreenPID(s, dm, dev_sid);
    assert DM_GreenDevWrite_PreConditions(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
    assert DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true;

    // Prove DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == dm
    var devwrite_result := DM_GreenDevWrite_InnerFunc(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var dm' := WSM_MapState(s');
    Lemma_WimpDrvWriteOwnDO_ProveOperationMapping(s, s', dm, dm', do_id_val_map);
    assert dm' == devwrite_result.0;

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_WimpDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (devwrite_result.0, devwrite_result.1);
    
    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}




/*********************** Private Lemmas ********************/
lemma Lemma_USBPDevWrite_ProveCommutativeDiagram_FDsAndDOsMustInActiveSet(
    s:state, dm:DM_State, dev_sid:Subject_ID, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsUSBPDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: The device must be active

    requires forall fd_id2 :: fd_id2 in fd_ids
				==> fd_id2 in s.subjects.usbpdevs[Dev_ID(dev_sid)].fd_ids
    requires forall do_id2 :: do_id2 in do_ids
				==> do_id2 in s.subjects.usbpdevs[Dev_ID(dev_sid)].do_ids

    ensures forall id :: id in fd_ids
                ==> id in dm.objects.active_fds
    ensures forall id :: id in do_ids
                ==> id in dm.objects.active_dos
{
    var globals := wkm_get_globals(s.wk_mstate);

    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    forall id | id in fd_ids
        ensures DM_ObjPID(dm.objects, id.oid) != NULL
    {
        var wsm_pid := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid);
        var dm_pid := DM_ObjPID(dm.objects, id.oid);

        Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, dev_sid, id.oid);
        assert wsm_pid != WS_PartitionID(PID_INVALID);

        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert WSM_MapWSParititonID_ToAbstractPartitionID(wsm_pid) == dm_pid;
    }
    
    forall id | id in do_ids
        ensures DM_ObjPID(dm.objects, id.oid) != NULL
    {
        var wsm_pid := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid);
        var dm_pid := DM_ObjPID(dm.objects, id.oid);

        Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, dev_sid, id.oid);
        assert wsm_pid != WS_PartitionID(PID_INVALID);

        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert WSM_MapWSParititonID_ToAbstractPartitionID(wsm_pid) == dm_pid;
    }

    Lemma_DM_ActiveObjsMustBeInActiveSet_FDs(dm, fd_ids);
    Lemma_DM_ActiveObjsMustBeInActiveSet_DOs(dm, do_ids);
}

lemma Lemma_EEHCIvWriteOwnDO_ProveCommutativeDiagram_DOsMustInActiveSet(
    s:state, dm:DM_State, dev_sid:Subject_ID, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsEEHCIDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: The device must be active

    requires forall do_id2 :: do_id2 in do_ids
				==> do_id2 in s.subjects.eehcis[Dev_ID(dev_sid)].do_ids

    ensures forall id :: id in do_ids
                ==> id in dm.objects.active_dos
{
    var globals := wkm_get_globals(s.wk_mstate);

    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    forall id | id in do_ids
        ensures DM_ObjPID(dm.objects, id.oid) != NULL
    {
        var wsm_pid := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid);
        var dm_pid := DM_ObjPID(dm.objects, id.oid);

        Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, dev_sid, id.oid);
        assert wsm_pid != WS_PartitionID(PID_INVALID);

        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert WSM_MapWSParititonID_ToAbstractPartitionID(wsm_pid) == dm_pid;
    }

    Lemma_DM_ActiveObjsMustBeInActiveSet_DOs(dm, do_ids);
}

lemma Lemma_OSDrvDevWrite_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)

    requires forall id :: id in wsm_td_id_val_map ==> id in s.objects.os_tds
    requires forall id :: id in wsm_fd_id_val_map ==> id in s.objects.os_fds
    requires forall id :: id in wsm_do_id_val_map ==> id in s.objects.os_dos
    requires td_id_val_map == OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map) &&
             fd_id_val_map == wsm_fd_id_val_map &&
             do_id_val_map == wsm_do_id_val_map
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in dm.objects.active_non_hcoded_tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in dm.objects.active_fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in dm.objects.active_dos)
        // Requirement: Relationship between written objects

    requires forall id :: id in wsm_td_id_val_map ==> id in s.objects.os_tds
    requires forall id :: id in wsm_fd_id_val_map ==> id in s.objects.os_fds
    requires forall id :: id in wsm_do_id_val_map ==> id in s.objects.os_dos
    requires var os_tds' := WSM_WriteOSTDsVals(s.objects.os_tds, wsm_td_id_val_map);
             var os_fds' := WSM_WriteOSFDsVals(s.objects.os_fds, wsm_fd_id_val_map);
             var os_dos' := WSM_WriteOSDOsVals(s.objects.os_dos, wsm_do_id_val_map);
             var s'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
             s' == s.(objects := s'_objs)
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    ensures var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, td_id_val_map);
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
            dm' == dm.(objects := t_objs3)
{
    var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, td_id_val_map);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);

    // [Axiom][Assumption] Writing an object in the WK code can always map to writing an abstract object in the WK design
    assume dm' == dm.(objects := t_objs3);
}

lemma Lemma_WimpDrvWriteOwnDO_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)

    requires forall id :: id in do_id_val_map ==> id in s.objects.wimpdrv_dos
    requires forall do_id :: do_id in do_id_val_map ==> do_id in dm.objects.active_dos

    requires var new_wimpdrv_dos := WSM_WriteDOsVals(s.objects.wimpdrv_dos, do_id_val_map);
             s' == s.(objects := s.objects.(wimpdrv_dos := new_wimpdrv_dos))
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    ensures var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, map[]);
            var t_objs2 := WriteActiveFDsVals(t_objs1, map[]);
            var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
            dm' == dm.(objects := t_objs3)
{
    var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, map[]);
    var t_objs2 := WriteActiveFDsVals(t_objs1, map[]);
    var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);

    Lemma_WriteActiveNonHCodedTDsVals_Property_EmptyWriteList(dm.objects);
    Lemma_WriteActiveFDsVals_Property_EmptyWriteList(dm.objects);

    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s);
    reveal WK_ValidObjs_ObjIDs();

    // [Axiom][Assumption] Writing an object in the WK code can always map to writing an abstract object in the WK design
    assume dm' == dm.(objects := t_objs3);
}

// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_USBPDevWrite_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)

    requires forall id :: id in fd_id_val_map ==> id in s.objects.usbpdev_fds
    requires forall id :: id in do_id_val_map ==> id in s.objects.usbpdev_dos
    requires (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in dm.objects.active_fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in dm.objects.active_dos)
        // Requirement: Relationship between written objects

    requires var new_usbpdevs_fds := WSM_WriteFDsVals(s.objects.usbpdev_fds, fd_id_val_map);
	         var new_usbpdevs_dos := WSM_WriteDOsVals(s.objects.usbpdev_dos, do_id_val_map);
             s' == s.(objects := s.objects.(usbpdev_fds := new_usbpdevs_fds, usbpdev_dos := new_usbpdevs_dos))
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    ensures var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, map[]);
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
            dm' == dm.(objects := t_objs3)
/*{
    var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, map[]);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);

    // [Axiom][Assumption] Writing an object in the WK code can always map to writing an abstract object in the WK design
    assume dm' == dm.(objects := t_objs3);
}*/

// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_EEHCIWriteOwnDO_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    eehci_id_word:word, eehci_slot:word, do_id_val_map:map<DO_ID, DO_Val>, new_val:word
)
    requires OpsSaneState(s)

    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word)
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI

    requires var old_globals := wkm_get_globals(s.wk_mstate);
             var new_globals := eehci_mem_set_status_reg(old_globals, eehci_slot, new_val);
             s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))
    requires OpsSaneStateSubset(s')
        // Requirement: Relationship between s and s'

    requires (forall do_id :: do_id in do_id_val_map ==> do_id in dm.objects.active_dos)
        // Requirement: Relationship between written objects

    requires var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             var do_id := EEHCI_RegOffset_ToDOID(s.subjects, s.objects, eehci_id, G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset);
             var new_do_val := DO_Val(DevWrite_WordToString(new_val));
             do_id_val_map == map[do_id := new_do_val]

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    ensures var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, map[]);
            var t_objs2 := WriteActiveFDsVals(t_objs1, map[]);
            var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
            dm' == dm.(objects := t_objs3)
/*{
    var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, map[]);
    var t_objs2 := WriteActiveFDsVals(t_objs1, map[]);
    var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);

    // [Axiom][Assumption] Writing an object in the WK code can always map to writing an abstract object in the WK design
    assume dm' == dm.(objects := t_objs3);
}*/