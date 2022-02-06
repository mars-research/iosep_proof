include "utils_os_accesses.s.dfy"
include "utils_wimp_accesses.s.dfy"
include "DM_Operations_Stubs.s.dfy"
include "DM_AdditionalPropertiesLemmas.i.dfy"
include "state_map_OpsSaneStateSubset.s.dfy"
include "../utils/model/headers_any_state.dfy"
include "../utils/model/utils_objs_secure_state.s.dfy"
include "../state_properties_validity.i.dfy"
include "../dev/usb2/usb_pdev.i.dfy"
include "../dev/usb2/usb_tds_utils.i.dfy"
include "../dev/usb2/eehci_mem.i.dfy"
include "../utils/model/utils_subjs_objs.i.dfy"
include "../ins/util/ffi.i.dfy"

/*********************** Inner Functions - OSDrvs ********************/
// Function: Return the state before IOMMU takes effect in <OSDrvWrite_ByPAddr> 
function OSDrvWrite_ByPAddr_InnerFunc_Modification1(
    s:state,
    drv_sid:Subject_ID,
    paddr:PAddrRegion,
    new_v:string
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires paddr.paddr_start <= paddr.paddr_end
        // Requirement: Valid memory address

    requires var t := OSDrvWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
             (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==>id !in wsm_td_id_val_map)
        // Requirement: The objects written by the driver must be active in the OS partition, and cannot be hardcoded TDs

    ensures var s' := result.0;
            OpsSaneStateSubset(s')
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var t := OSDrvWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
    var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
    var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
    var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;

    // Prove DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    Lemma_OSDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition(s, dm, drv_sid,
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove writing objects in system
    Lemma_OSDrvWrite_ByPAddr_ProveAccessedObjsAreOSObjects(s, paddr, new_v, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    assert MapGetKeys(wsm_td_id_val_map) <= MapGetKeys(s.objects.os_tds);
    assert MapGetKeys(wsm_fd_id_val_map) <= MapGetKeys(s.objects.os_fds);
    assert MapGetKeys(wsm_do_id_val_map) <= MapGetKeys(s.objects.os_dos);

    // Write OS objects
    var os_tds' := WSM_WriteOSTDsVals(s.objects.os_tds, wsm_td_id_val_map);
    var os_fds' := WSM_WriteOSFDsVals(s.objects.os_fds, wsm_fd_id_val_map);
    var os_dos' := WSM_WriteOSDOsVals(s.objects.os_dos, wsm_do_id_val_map);

    var s'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
    var s' := s.(objects := s'_objs);

    // Prove OpsSaneStateSubset
    Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(s, s', os_tds', os_fds', os_dos');
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsIDsAndPIDsAreUnchanged(s, s');

    (s', true)
}

// Function: Return the state before IOMMU takes effect in <OSDrvWrite_ByPIO>
function OSDrvWrite_ByPIO_InnerFunc_Modification1(
    s:state,
    drv_sid:Subject_ID,
    pio_addr:ioaddr,
    new_v:string
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires var t := OSDrvWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
             (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==>id !in wsm_td_id_val_map)
        // Requirement: The objects written by the driver must be active in the OS partition, and cannot be hardcoded TDs

    ensures var s' := result.0;
            OpsSaneStateSubset(s')
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var t := OSDrvWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
    var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
    var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
    var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;

    // Prove DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    Lemma_OSDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition(s, dm, drv_sid,
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove writing objects in system
    Lemma_OSDrvWrite_ByPIO_ProveAccessedObjsAreOSObjects(s, pio_addr, new_v, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    assert MapGetKeys(wsm_td_id_val_map) <= MapGetKeys(s.objects.os_tds);
    assert MapGetKeys(wsm_fd_id_val_map) <= MapGetKeys(s.objects.os_fds);
    assert MapGetKeys(wsm_do_id_val_map) <= MapGetKeys(s.objects.os_dos);

    // Write OS objects
    var os_tds' := WSM_WriteOSTDsVals(s.objects.os_tds, wsm_td_id_val_map);
    var os_fds' := WSM_WriteOSFDsVals(s.objects.os_fds, wsm_fd_id_val_map);
    var os_dos' := WSM_WriteOSDOsVals(s.objects.os_dos, wsm_do_id_val_map);

    var s'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
    var s' := s.(objects := s'_objs);

    // Prove OpsSaneStateSubset
    Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(s, s', os_tds', os_fds', os_dos');
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsIDsAndPIDsAreUnchanged(s, s');

    (s', true)
}

// Function: Return the state before IOMMU takes effect in <OSDrvWrite_ByObjIDs>
function OSDrvWrite_ByObjIDs_InnerFunc_Modification1(
    s:state,
    drv_sid:Subject_ID,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, // TDs to be written with their new values
    wsm_fd_id_val_map:map<FD_ID, FD_Val>, // FDs to be written with their new values
    wsm_do_id_val_map:map<DO_ID, DO_Val> // DOs to be written with their new values
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires P_OSDrvAccess_AccessActiveObjsOnly(s, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map)) &&
             (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==>id !in wsm_td_id_val_map)
        // Requirement: The objects written by the driver must be active in the OS partition, and cannot be hardcoded TDs
        // This pre-condition reflexes the late access mediation done by MMU
    requires forall id :: id in wsm_td_id_val_map
                ==> id !in s.objects.usbpdev_tds
    requires forall id :: id in wsm_fd_id_val_map
                ==> id !in s.objects.usbpdev_fds
    requires forall id :: id in wsm_do_id_val_map
                ==> id !in s.objects.usbpdev_dos
        // Requirement: OS devices (except USB peripheral devices) cannot write USB peripheral devices in the OS partition

    ensures var s' := result.0;
            OpsSaneStateSubset(s')
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    // Prove DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    Lemma_OSDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition(s, dm, drv_sid,
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove writing objects in system
    Lemma_OSDrvWrite_ByObjIDs_ProveAccessedObjsAreOSObjects(s, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    assert MapGetKeys(wsm_td_id_val_map) <= MapGetKeys(s.objects.os_tds);
    assert MapGetKeys(wsm_fd_id_val_map) <= MapGetKeys(s.objects.os_fds);
    assert MapGetKeys(wsm_do_id_val_map) <= MapGetKeys(s.objects.os_dos);

    // Write OS objects
    var os_tds' := WSM_WriteOSTDsVals(s.objects.os_tds, wsm_td_id_val_map);
    var os_fds' := WSM_WriteOSFDsVals(s.objects.os_fds, wsm_fd_id_val_map);
    var os_dos' := WSM_WriteOSDOsVals(s.objects.os_dos, wsm_do_id_val_map);

    var s'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
    var s' := s.(objects := s'_objs);

    // Prove OpsSaneStateSubset
    Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(s, s', os_tds', os_fds', os_dos');
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsIDsAndPIDsAreUnchanged(s, s');

    (s', true)
}



/*********************** Lemmas - Common ********************/
lemma Lemma_DrvDevRead_HCodedTDsAreNotInParams(s:state, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires OpsSaneState(s)
    requires forall td_id :: td_id in td_ids ==> td_id in WSM_AllTDIDs(s.objects)
    requires forall fd_id :: fd_id in fd_ids ==> fd_id in WSM_AllFDIDs(s.objects)
    requires forall do_id :: do_id in do_ids ==> do_id in WSM_AllDOIDs(s.objects)
    requires forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==> id !in td_ids

    ensures var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
            var dm := WSM_MapSecureState(s);
            forall dev_id :: dev_id in dm.subjects.devs
                ==> dm.subjects.devs[dev_id].hcoded_td_id.oid !in obj_ids
{
    reveal IsValidState_Objects_UniqueObjIDs();
}




/*********************** Lemmas - OSDrvRead ********************/
// [NOTE] Needs 50s to verify
lemma {:timeLimitMultiplier 7} Lemma_OSDrvRead_ProveSubjsObjsInSamePartition(
    s:state, dm:DM_State, drv_sid:Subject_ID, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: Driver is in OS partition
    requires P_OSDrvAccess_AccessActiveObjsOnly(s, td_ids, fd_ids, do_ids)
    requires var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
             obj_ids <= WSM_AllObjIDs(s.objects)
        // Requirement: Objects must exist in the system

    ensures var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
            forall o_id :: o_id in obj_ids 
                ==> DM_SubjPID(dm.subjects, drv_sid) == DM_ObjPID(dm.objects, o_id);
{
    var globals := wkm_get_globals(s.wk_mstate);
    var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    var drv_pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid);
    assert drv_pid == WS_PartitionID(PID_RESERVED_OS_PARTITION);
    assert DM_SubjPID(dm.subjects, drv_sid) == WSM_MapWSParititonID_ToAbstractPartitionID(drv_pid);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    forall o_id | o_id in obj_ids 
        ensures DM_SubjPID(dm.subjects, drv_sid) == DM_ObjPID(dm.objects, o_id)
    {
        assert o_id in WSM_AllObjIDs(s.objects);
        var o_pid := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, o_id);
        assert DM_ObjPID(dm.objects, o_id) == WSM_MapWSParititonID_ToAbstractPartitionID(o_pid);

        // Apply P_OSDrvAccess_AccessActiveObjsOnly(s, td_ids, fd_ids, do_ids)
        assert P_OSDrvAccess_AccessActiveObjsOnly(s, td_ids, fd_ids, do_ids);
        assert TD_ID(o_id) in td_ids || FD_ID(o_id) in fd_ids || DO_ID(o_id) in do_ids;
        assert o_pid == WS_PartitionID(PID_RESERVED_OS_PARTITION);
    }
}

lemma Lemma_OSDrvRead_ProveDM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(
    s:state, dm:DM_State, drv_sid:Subject_ID, 
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires OpsSaneState(s)
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires dm == WSM_MapState(s)
    requires P_OSDrvAccess_AccessActiveObjsOnly(s, read_tds, read_fds, read_dos)
             
    requires forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==>id !in read_tds
        // Requirement: The objects written by the driver must be active in the OS partition, and cannot be hardcoded TDs

    ensures P_DMSubjectsHasUniqueIDs(dm.subjects)
    ensures P_DMObjectsHasUniqueIDs(dm.objects)
    ensures (forall td_id :: td_id in read_tds ==> td_id in AllTDIDs(dm.objects)) &&
             (forall fd_id :: fd_id in read_fds ==> fd_id in AllFDIDs(dm.objects)) &&
             (forall do_id :: do_id in read_dos ==> do_id in AllDOIDs(dm.objects))
        // Properties needed by the properties below
    ensures WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, read_tds, read_fds, read_dos)
    ensures DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, drv_sid, read_tds, read_fds, read_dos)
{
    var globals := wkm_get_globals(s.wk_mstate);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    assert (forall td_id :: td_id in read_tds ==> td_id in WSM_AllTDIDs(s.objects)) &&
            (forall fd_id :: fd_id in read_fds ==> fd_id in WSM_AllFDIDs(s.objects)) &&
            (forall do_id :: do_id in read_dos ==> do_id in WSM_AllDOIDs(s.objects));

    assert (forall id :: id in read_tds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
            (forall id :: id in read_fds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
            (forall id :: id in read_dos
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION));

    Lemma_OSDrvAccess_ProveWS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, read_tds, read_fds, read_dos);
    assert WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, read_tds, read_fds, read_dos);
    Lemma_OSDrvRead_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition(s, dm, drv_sid, read_tds, read_fds, read_dos);

    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, drv_sid, read_tds, read_fds, read_dos);
}

lemma Lemma_OSDrvRead_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition(
    s:state, dm:DM_State, drv_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires OpsSaneStateSubset(s)

    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires (forall td_id :: td_id in read_tds ==> td_id in WSM_AllTDIDs(s.objects)) &&
            (forall fd_id :: fd_id in read_fds ==> fd_id in WSM_AllFDIDs(s.objects)) &&
            (forall do_id :: do_id in read_dos ==> do_id in WSM_AllDOIDs(s.objects))
        // Requirement: Driver only write existing objects
    requires WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, read_tds, read_fds, read_dos)

    requires dm == WSM_MapState(s)

    ensures P_DMSubjectsHasUniqueIDs(dm.subjects)
    ensures P_DMObjectsHasUniqueIDs(dm.objects)
        // Properties needed by the following property
    ensures DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, drv_sid, read_tds, read_fds, read_dos);
{
    reveal WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition();
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
}

lemma Lemma_DM_DevRead_Properties(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    read_tds:set<TD_ID>,
    read_fds:set<FD_ID>,
    read_dos:set<DO_ID> 
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active

    requires DM_DevRead_TransfersMustBeDefinedInWSDesignModel(ws, dev_sid, read_tds, read_fds, read_dos)

    ensures forall id :: id in read_tds
                ==> id in AllTDIDs(ws.objects) &&
                    ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
    ensures forall id :: id in read_fds
                ==> id in AllFDIDs(ws.objects) &&
                    ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
    ensures forall id :: id in read_dos
                ==> id in AllDOIDs(ws.objects) &&
                    ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
        // Property 1: Objects to be modified must be in the same partition with the device
    ensures forall id :: id in read_tds
                ==> id !in AllHCodedTDIDs(ws.subjects)
        // Property 2: Hardcoded TDs are unchanged
{
    Lemma_DM_DevRead_ReadObjsMustInSystemAndNotHCodedTDs(ws, dev_sid, read_tds, read_fds, read_dos);
    Lemma_DM_DevRead_DevAndReadObjsAreInSamePartition(ws, dev_sid, read_tds, read_fds, read_dos);
}




/*********************** Lemmas - OSDrv Write ********************/
lemma Lemma_OSDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition(
    s:state, dm:DM_State, drv_sid:Subject_ID,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires dm == WSM_MapState(s)
    requires P_OSDrvAccess_AccessActiveObjsOnly(s, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
    requires td_id_val_map == OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map) &&
             fd_id_val_map == wsm_fd_id_val_map &&
             do_id_val_map == wsm_do_id_val_map
             
    requires forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==>id !in wsm_td_id_val_map
        // Requirement: The objects written by the driver must be active in the OS partition, and cannot be hardcoded TDs

    ensures P_DMSubjectsHasUniqueIDs(dm.subjects)
    ensures P_DMObjectsHasUniqueIDs(dm.objects)
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(dm.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(dm.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(dm.objects))
        // Properties needed by the properties below
    ensures WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
    ensures DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    var globals := wkm_get_globals(s.wk_mstate);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    assert (forall td_id :: td_id in wsm_td_id_val_map ==> td_id in WSM_AllTDIDs(s.objects)) &&
            (forall fd_id :: fd_id in wsm_fd_id_val_map ==> fd_id in WSM_AllFDIDs(s.objects)) &&
            (forall do_id :: do_id in wsm_do_id_val_map ==> do_id in WSM_AllDOIDs(s.objects));

    assert (forall id :: id in wsm_td_id_val_map
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
            (forall id :: id in wsm_fd_id_val_map
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
            (forall id :: id in wsm_do_id_val_map
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION));

    Lemma_OSDrvAccess_ProveWS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map));
    assert WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map));
    Lemma_OSDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition_Inner(s, dm, drv_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
}

lemma Lemma_OSDrvAccess_ProveWS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(
    s:state, drv_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires OpsSaneStateSubset(s)

    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires (forall td_id :: td_id in read_tds ==> td_id in WSM_AllTDIDs(s.objects)) &&
            (forall fd_id :: fd_id in read_fds ==> fd_id in WSM_AllFDIDs(s.objects)) &&
            (forall do_id :: do_id in read_dos ==> do_id in WSM_AllDOIDs(s.objects))
    requires var globals := wkm_get_globals(s.wk_mstate);
            (forall id :: id in read_tds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
            (forall id :: id in read_fds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
            (forall id :: id in read_dos
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION))
        // Requirement: Properties from <OSDrvWrite_By*_GetWriteObjsValsPairs>
    
    ensures WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, read_tds, read_fds, read_dos)
{
    reveal WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition();
}

lemma Lemma_OSDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition_Inner(
    s:state, dm:DM_State, drv_sid:Subject_ID,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneStateSubset(s)

    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires (forall td_id :: td_id in wsm_td_id_val_map ==> td_id in WSM_AllTDIDs(s.objects)) &&
            (forall fd_id :: fd_id in wsm_fd_id_val_map ==> fd_id in WSM_AllFDIDs(s.objects)) &&
            (forall do_id :: do_id in wsm_do_id_val_map ==> do_id in WSM_AllDOIDs(s.objects))
        // Requirement: Driver only write existing objects
    requires WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))

    requires dm == WSM_MapState(s)

    ensures P_DMSubjectsHasUniqueIDs(dm.subjects)
    ensures P_DMObjectsHasUniqueIDs(dm.objects)
        // Properties needed by the following property
    ensures var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
            var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
            var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
            DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
{
    reveal WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition();
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
}

lemma Lemma_OSDrvWrite_ByPAddr_ProveAccessedObjsAreOSObjects(
    s:state, paddr:PAddrRegion, new_v:string,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneStateSubset(s)

    requires paddr.paddr_start <= paddr.paddr_end

    requires var t := OSDrvWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
             wsm_td_id_val_map == t.0 &&
             wsm_fd_id_val_map == t.1 &&
             wsm_do_id_val_map == t.2
        // Requirement: The objects to be modified must be overlapped with the paddr memory regin <paddr>

    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_td_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_fd_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_do_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: Only objects in the OS partition is modified

    ensures MapGetKeys(wsm_td_id_val_map) <= MapGetKeys(s.objects.os_tds)
    ensures MapGetKeys(wsm_fd_id_val_map) <= MapGetKeys(s.objects.os_fds)
    ensures MapGetKeys(wsm_do_id_val_map) <= MapGetKeys(s.objects.os_dos)
{
    Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate));
    reveal WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition();
    reveal WK_ValidObjsAddrs();
}

lemma Lemma_OSDrvWrite_ByPIO_ProveAccessedObjsAreOSObjects(
    s:state, pio_addr:ioaddr, new_v:string,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneStateSubset(s)

    requires var t := OSDrvWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
             wsm_td_id_val_map == t.0 &&
             wsm_fd_id_val_map == t.1 &&
             wsm_do_id_val_map == t.2
        // Requirement: The objects to be modified must be located at the PIO addr <pio_addr>

    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_td_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_fd_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_do_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: Only objects in the OS partition is modified

    ensures MapGetKeys(wsm_td_id_val_map) <= MapGetKeys(s.objects.os_tds)
    ensures MapGetKeys(wsm_fd_id_val_map) <= MapGetKeys(s.objects.os_fds)
    ensures MapGetKeys(wsm_do_id_val_map) <= MapGetKeys(s.objects.os_dos)
{
    Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate));
    reveal WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition();
    reveal WK_ValidObjsAddrs();
}

lemma Lemma_OSDrvWrite_ByObjIDs_ProveAccessedObjsAreOSObjects(
    s:state, 
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneStateSubset(s)

    requires P_OSDrvAccess_AccessActiveObjsOnly(s, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
        // Requirement: The objects written by the driver must be active in the OS partition
    requires forall id :: id in wsm_td_id_val_map
                ==> id !in s.objects.usbpdev_tds
    requires forall id :: id in wsm_fd_id_val_map
                ==> id !in s.objects.usbpdev_fds
    requires forall id :: id in wsm_do_id_val_map
                ==> id !in s.objects.usbpdev_dos
        // Requirement: OS devices (except USB peripheral devices) cannot write USB peripheral devices in the OS partition

    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_td_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_fd_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_do_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: Only objects in the OS partition is modified

    ensures MapGetKeys(wsm_td_id_val_map) <= MapGetKeys(s.objects.os_tds)
    ensures MapGetKeys(wsm_fd_id_val_map) <= MapGetKeys(s.objects.os_fds)
    ensures MapGetKeys(wsm_do_id_val_map) <= MapGetKeys(s.objects.os_dos)
{
    Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate));
    reveal WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition();
    reveal WK_ValidObjsAddrs();
}

lemma Lemma_ValidState_ProveP_WimpObjs_HaveNoPIOAddr(s:state)
    requires ValidState(s)

    ensures P_WimpObjs_HaveNoPIOAddr(s)
{
    reveal WK_ValidObjsAddrs();
}

lemma Lemma_ValidState_ProveP_PEHCIsObjs_HaveNoPIOAddr(s:state)
    requires ValidState(s)

    ensures forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
    ensures P_PEHCIsObjs_HaveNoPIOAddr(s)
{
    reveal WK_ValidState_DevsActivateCond();
    reveal WK_ValidObjsAddrs_PEHCIs();
}




/*********************** Inner Functions - OSDevs ********************/
// [NOTE] Needs 80s to verify
function OSDevWrite_ByPAddr_InnerFunc(
    s:state,
    dev_sid:Subject_ID,
    paddr:PAddrRegion,
    new_v:string
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The device is in the red partition

    requires paddr.paddr_start <= paddr.paddr_end
        // Requirement: Valid memory address

    requires var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
             WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
        // Requirement: If the OS device writes to a set of TDs/FDs/DOs with some values, then the device must be able  
        // to write the corresponding objects with the corresponding values in the WK design model

    ensures var s' := result.0;
            OpsSaneStateSubset(s')
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
    var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
    var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
    var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written

    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    // Prove wsm_*_id_map must be OS TDs/FDs/DOs
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_DM_DevWrite_Property(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_OSDevWrite_WriteObjsMustInSystemAndNotHCodedTDs(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    Lemma_OSDevAccess_ObjsToBeAccessedMustBeInOSParition(s, dm, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map));

    Lemma_OSDevWrite_ByPAddr_ProveAccessedObjsAreOSObjects(s, paddr, new_v, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    assert MapGetKeys(wsm_td_id_val_map) <= MapGetKeys(s.objects.os_tds);
    assert MapGetKeys(wsm_fd_id_val_map) <= MapGetKeys(s.objects.os_fds);
    assert MapGetKeys(wsm_do_id_val_map) <= MapGetKeys(s.objects.os_dos);

    // Write OS objects
    var os_tds' := WSM_WriteOSTDsVals(s.objects.os_tds, wsm_td_id_val_map);
    var os_fds' := WSM_WriteOSFDsVals(s.objects.os_fds, wsm_fd_id_val_map);
    var os_dos' := WSM_WriteOSDOsVals(s.objects.os_dos, wsm_do_id_val_map);

    assert forall id :: id in td_id_val_map
                ==> id !in AllHCodedTDIDs(dm.subjects);
    assert forall id :: id in wsm_td_id_val_map
                ==> id !in WSM_AllHCodedTDIDs(s.subjects);
    assert forall td_id :: td_id in WSM_AllHCodedTDIDs(s.subjects) &&
                    td_id in s.objects.os_tds
                ==> s.objects.os_tds[td_id] == os_tds'[td_id];

    var s'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
    var s' := s.(objects := s'_objs);

    // Prove OpsSaneStateSubset
    Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(s, s', os_tds', os_fds', os_dos');
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsIDsAndPIDsAreUnchanged(s, s');

    (s', true)
}

// [NOTE] Needs 80s to verify
function OSDevWrite_ByPIO_InnerFunc(
    s:state,
    dev_sid:Subject_ID,
    pio_addr:ioaddr,
    new_v:string
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The device is in the red partition

    requires var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs located at the PIO addr <pio_addr>, and values to be written
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs located at the PIO addr <pio_addr>, and values to be written
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs located at the PIO addr <pio_addr>, and values to be written
             WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
        // Requirement: If the OS device writes to a set of TDs/FDs/DOs with some values, then the device must be able  
        // to write the corresponding objects with the corresponding values in the WK design model

    ensures var s' := result.0;
            OpsSaneStateSubset(s')
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
    var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
    var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
    var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;

    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    // Prove wsm_*_id_map must be OS TDs/FDs/DOs
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_DM_DevWrite_Property(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_OSDevWrite_WriteObjsMustInSystemAndNotHCodedTDs(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    Lemma_OSDevAccess_ObjsToBeAccessedMustBeInOSParition(s, dm, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map));

    Lemma_OSDevWrite_ByPIO_ProveAccessedObjsAreOSObjects(s, pio_addr, new_v, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    assert MapGetKeys(wsm_td_id_val_map) <= MapGetKeys(s.objects.os_tds);
    assert MapGetKeys(wsm_fd_id_val_map) <= MapGetKeys(s.objects.os_fds);
    assert MapGetKeys(wsm_do_id_val_map) <= MapGetKeys(s.objects.os_dos);

    // Write OS objects
    var os_tds' := WSM_WriteOSTDsVals(s.objects.os_tds, wsm_td_id_val_map);
    var os_fds' := WSM_WriteOSFDsVals(s.objects.os_fds, wsm_fd_id_val_map);
    var os_dos' := WSM_WriteOSDOsVals(s.objects.os_dos, wsm_do_id_val_map);

    assert forall id :: id in td_id_val_map
                ==> id !in AllHCodedTDIDs(dm.subjects);
    assert forall id :: id in wsm_td_id_val_map
                ==> id !in WSM_AllHCodedTDIDs(s.subjects);
    assert forall td_id :: td_id in WSM_AllHCodedTDIDs(s.subjects) &&
                    td_id in s.objects.os_tds
                ==> s.objects.os_tds[td_id] == os_tds'[td_id];

    var s'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
    var s' := s.(objects := s'_objs);

    // Prove OpsSaneStateSubset
    Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(s, s', os_tds', os_fds', os_dos');
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsIDsAndPIDsAreUnchanged(s, s');

    (s', true)
}

// [NOTE] Needs 300s to verify
function OSNonUSBPDevWrite_ByObjIDs_InnerFunc(
    s:state,
    dev_sid:Subject_ID,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, // TDs to be written with their new values
    wsm_fd_id_val_map:map<FD_ID, FD_Val>, // FDs to be written with their new values
    wsm_do_id_val_map:map<DO_ID, DO_Val> // DOs to be written with their new values
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The device is in the red partition

    requires WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
        // Requirement: If the OS device writes to a set of TDs/FDs/DOs with some values, then the device must be able  
        // to write the corresponding objects with the corresponding values in the WK design model
    requires forall id :: id in wsm_td_id_val_map
                ==> id !in s.objects.usbpdev_tds
    requires forall id :: id in wsm_fd_id_val_map
                ==> id !in s.objects.usbpdev_fds
    requires forall id :: id in wsm_do_id_val_map
                ==> id !in s.objects.usbpdev_dos
        // Requirement: OS devices (except USB peripheral devices) cannot write USB peripheral devices in the OS partition

    ensures var s' := result.0;
            OpsSaneStateSubset(s')
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    // Prove wsm_*_id_map must be active OS TDs/FDs/DOs in the OS partition
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_DM_DevWrite_Property(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_OSDevWrite_WriteObjsMustInSystemAndNotHCodedTDs(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    Lemma_OSDevAccess_ObjsToBeAccessedMustBeInOSParition(s, dm, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map));

    Lemma_OSNonUSBPDevWrite_ByObjIDs_ProveAccessedObjsAreOSObjects(s, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);

    // Write OS objects
    var os_tds' := WSM_WriteOSTDsVals(s.objects.os_tds, wsm_td_id_val_map);
    var os_fds' := WSM_WriteOSFDsVals(s.objects.os_fds, wsm_fd_id_val_map);
    var os_dos' := WSM_WriteOSDOsVals(s.objects.os_dos, wsm_do_id_val_map);

    assert forall id :: id in td_id_val_map
                ==> id !in AllHCodedTDIDs(dm.subjects);
    assert forall id :: id in wsm_td_id_val_map
                ==> id !in WSM_AllHCodedTDIDs(s.subjects);
    assert forall td_id :: td_id in WSM_AllHCodedTDIDs(s.subjects) &&
                    td_id in s.objects.os_tds
                ==> s.objects.os_tds[td_id] == os_tds'[td_id];

    var s'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
    var s' := s.(objects := s'_objs);

    // Prove OpsSaneStateSubset
    Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(s, s', os_tds', os_fds', os_dos');
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsIDsAndPIDsAreUnchanged(s, s');

    (s', true)
}




/*********************** Lemmas - WimpDrv Read ********************/
lemma Lemma_WimpDrvRead_ByPAddr_EquivilantReadObjs(do_id:DO_ID)
    ensures {do_id.oid} == TDIDsToObjIDs({}) + FDIDsToObjIDs({}) + DOIDsToObjIDs({do_id})
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvAccess_ProveWS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(
    s:state, drv_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires OpsSaneStateSubset(s)

    requires WSM_IsWimpDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) in 
                pids_parse_g_wimp_pids(wkm_get_globals(s.wk_mstate))
        // Requirement: The driver is in a green partition

    requires forall id :: id in read_tds ==> id in WSM_AllTDIDs(s.objects)
    requires forall id :: id in read_fds ==> id in WSM_AllFDIDs(s.objects)
    requires forall id :: id in read_dos ==> id in WSM_AllDOIDs(s.objects)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in read_tds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in read_fds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in read_dos
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid)
    
    ensures WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, read_tds, read_fds, read_dos)
{
    // Dafny can automatically prove this lemma
}

// [NOTE] Needs 100s to verify
lemma {:timeLimitMultiplier 10} Lemma_WimpDrvRead_ProveSubjsObjsInSamePartition(
    s:state, dm:DM_State, drv_id:Drv_ID, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsWimpDrvID(s.subjects, drv_id)
    requires var globals := wkm_get_globals(s.wk_mstate);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_id.sid) 
                in pids_parse_g_wimp_pids(globals)
        // Requirement: The driver is in the green partition

    requires WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_id.sid, td_ids, fd_ids, do_ids)
    requires var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
             obj_ids <= WSM_AllObjIDs(s.objects)
        // Requirement: Objects must exist in the system

    ensures var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
            forall o_id :: o_id in obj_ids 
                ==> DM_SubjPID(dm.subjects, drv_id.sid) == DM_ObjPID(dm.objects, o_id);
{
    var globals := wkm_get_globals(s.wk_mstate);
    var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    forall o_id | o_id in obj_ids 
        ensures DM_SubjPID(dm.subjects, drv_id.sid) == DM_ObjPID(dm.objects, o_id)
    {
        var s_pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_id.sid);
        var o_pid := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, o_id);
        assert WSM_MapWSParititonID_ToAbstractPartitionID(s_pid) == DM_SubjPID(dm.subjects, drv_id.sid);
        assert WSM_MapWSParititonID_ToAbstractPartitionID(o_pid) == DM_ObjPID(dm.objects, o_id);

        assert TD_ID(o_id) in td_ids || FD_ID(o_id) in fd_ids || DO_ID(o_id) in do_ids;

        Lemma_SameIDsIffSameInternalIDs();
        if(TD_ID(o_id) in td_ids)
        {
            assert s_pid == o_pid;
        }
        else if(FD_ID(o_id) in fd_ids)
        {
            assert s_pid == o_pid;
        }
        else
        {
            assert s_pid == o_pid;
        }
    }
}




/*********************** Lemmas - WimpDrv Write ********************/
lemma Lemma_WimpDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition(
    s:state, dm:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsWimpDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) in 
                pids_parse_g_wimp_pids(wkm_get_globals(s.wk_mstate))
        // Requirement: The driver is in a green partition

    requires forall id :: id in td_id_val_map ==> id in WSM_AllTDIDs(s.objects)
    requires forall id :: id in fd_id_val_map ==> id in WSM_AllFDIDs(s.objects)
    requires forall id :: id in do_id_val_map ==> id in WSM_AllDOIDs(s.objects)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in td_id_val_map
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in fd_id_val_map
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in do_id_val_map
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid)

    ensures P_DMSubjectsHasUniqueIDs(dm.subjects)
    ensures P_DMObjectsHasUniqueIDs(dm.objects)
    ensures WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(dm.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(dm.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(dm.objects))
        // Properties needed by the properties below
    
    ensures DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    Lemma_WimpDrvAccess_ProveWS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, 
        MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map));
    assert WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map));
    Lemma_WimpDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition_Inner(s, dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
}

lemma Lemma_WimpDrvWrite_ProveDM_DrvWrite_ChkDrvAndObjsAreInSamePartition_Inner(
    s:state, dm:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneStateSubset(s)

    requires WSM_IsWimpDrvID(s.subjects, Drv_ID(drv_sid))
    requires forall id :: id in td_id_val_map ==> id in WSM_AllTDIDs(s.objects)
    requires forall id :: id in fd_id_val_map ==> id in WSM_AllFDIDs(s.objects)
    requires forall id :: id in do_id_val_map ==> id in WSM_AllDOIDs(s.objects)
        // Requirement: Driver only write existing objects
    requires WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, drv_sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map))

    requires dm == WSM_MapState(s)

    ensures P_DMSubjectsHasUniqueIDs(dm.subjects)
    ensures P_DMObjectsHasUniqueIDs(dm.objects)
        // Properties needed by the following property
    ensures DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
}

lemma Lemma_WimpDrvWrite_ProveWimpDrvAndItsDOInSamePartition(s:state, drv_sid:Subject_ID, wimpdrv_do_oid:Object_ID)
    requires OpsSaneState(s)

    requires WSM_IsWimpDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_IsObjID(s.objects, wimpdrv_do_oid)
    requires WSM_DoOwnObj(s.subjects, drv_sid, wimpdrv_do_oid)

    ensures var globals := wkm_get_globals(s.wk_mstate);
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_do_oid) == 
            WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid)
{
    Lemma_ObjPID_SamePIDWithOwnerSubject(
        s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid, wimpdrv_do_oid);
}

lemma Lemma_EEHCIWriteUSBPDev_ProveP_EEHCIWriteUSBPDevObjs(
    s:state, dm:DM_State, eehci_id:Dev_ID,
    fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsEEHCIDevID(s.subjects, eehci_id)

    requires (forall id :: id in fd_id_val_map 
                        ==> id in s.objects.usbpdev_fds) &&
            (forall id :: id in do_id_val_map 
                        ==> id in s.objects.usbpdev_dos)

    requires forall id :: id in fd_id_val_map
                ==> id.oid in AllObjsIDs(dm.objects) &&
                    ObjPID_KObjects(dm.objects, id.oid) == SubjPID_SlimState(dm.subjects, eehci_id.sid)
    requires forall id :: id in do_id_val_map
                ==> id.oid in AllObjsIDs(dm.objects) &&
                    ObjPID_KObjects(dm.objects, id.oid) == SubjPID_SlimState(dm.subjects, eehci_id.sid)

    ensures P_EEHCIWriteUSBPDevObjs(s, eehci_id, fd_id_val_map, do_id_val_map)
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
}

lemma Lemma_EEHCIWriteWimpDrvDO_ProveP_EEHCIWriteWimpDrvDO(
    s:state, dm:DM_State, eehci_id:Dev_ID,
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsEEHCIDevID(s.subjects, eehci_id)

    requires (forall id :: id in do_id_val_map 
                        ==> id in s.objects.wimpdrv_dos)

    requires forall id :: id in do_id_val_map
                ==> id.oid in AllObjsIDs(dm.objects) &&
                    ObjPID_KObjects(dm.objects, id.oid) == SubjPID_SlimState(dm.subjects, eehci_id.sid)

    ensures P_EEHCIWriteWimpDrvDO(s, eehci_id, do_id_val_map)
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
}




/*********************** Lemmas - OSDevs ********************/
// [NOTE] Needs 300s to verify
lemma {:timeLimitMultiplier 30} Lemma_DevRead_ProveSubjsObjsInSamePartition(
    s:state, dm:DM_State, dev_sid:Subject_ID, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: The device is in the red partition

    requires (forall td_id :: td_id in td_ids ==> td_id in AllTDIDs(dm.objects)) &&
             (forall fd_id :: fd_id in fd_ids ==> fd_id in AllFDIDs(dm.objects)) &&
             (forall do_id :: do_id in do_ids ==> do_id in AllDOIDs(dm.objects)) 
    requires DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, td_ids, fd_ids, do_ids)

    requires var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
             obj_ids <= WSM_AllObjIDs(s.objects)
        // Requirement: Objects must exist in the system

    ensures var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
            forall o_id :: o_id in obj_ids 
                ==> DM_SubjPID(dm.subjects, dev_sid) == DM_ObjPID(dm.objects, o_id);
{
    var globals := wkm_get_globals(s.wk_mstate);
    var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    var drv_pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, dev_sid);
    assert DM_SubjPID(dm.subjects, dev_sid) == WSM_MapWSParititonID_ToAbstractPartitionID(drv_pid);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    forall o_id | o_id in obj_ids 
        ensures DM_SubjPID(dm.subjects, dev_sid) == DM_ObjPID(dm.objects, o_id)
    {
        assert o_id in WSM_AllObjIDs(s.objects);
        var o_pid := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, o_id);
        assert DM_ObjPID(dm.objects, o_id) == WSM_MapWSParititonID_ToAbstractPartitionID(o_pid);

        // Apply TD_ID(o_id) in td_ids || FD_ID(o_id) in fd_ids || DO_ID(o_id) in do_ids
        assert TD_ID(o_id) in td_ids || FD_ID(o_id) in fd_ids || DO_ID(o_id) in do_ids;
    }
}

lemma Lemma_OSDevWrite_ByPAddr_ProveAccessedObjsAreOSObjects(
    s:state, paddr:PAddrRegion, new_v:string,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneStateSubset(s)

    requires paddr.paddr_start <= paddr.paddr_end

    requires var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
             wsm_td_id_val_map == t.0 &&
             wsm_fd_id_val_map == t.1 &&
             wsm_do_id_val_map == t.2
        // Requirement: The objects to be modified must be overlapped with the paddr memory regin <paddr>

    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_td_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_fd_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_do_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: Only objects in the OS partition is modified

    ensures forall id :: id in wsm_td_id_val_map 
                ==> id in s.objects.os_tds
    ensures forall id :: id in wsm_fd_id_val_map 
                ==> id in s.objects.os_fds
    ensures forall id :: id in wsm_do_id_val_map 
                ==> id in s.objects.os_dos
{
    Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate));
    reveal WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition();
    reveal WK_ValidObjsAddrs();
}

lemma Lemma_OSDevWrite_ByPIO_ProveAccessedObjsAreOSObjects(
    s:state, pio_addr:ioaddr, new_v:string,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneStateSubset(s)

    requires var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
             wsm_td_id_val_map == t.0 &&
             wsm_fd_id_val_map == t.1 &&
             wsm_do_id_val_map == t.2
        // Requirement: The objects to be modified must be located at the PIO addr <pio_addr>

    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_td_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_fd_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_do_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: Only objects in the OS partition is modified

    ensures forall id :: id in wsm_td_id_val_map 
                ==> id in s.objects.os_tds
    ensures forall id :: id in wsm_fd_id_val_map 
                ==> id in s.objects.os_fds
    ensures forall id :: id in wsm_do_id_val_map 
                ==> id in s.objects.os_dos
{
    Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate));
    reveal WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition();
    reveal WK_ValidObjsAddrs();
}

lemma Lemma_OSNonUSBPDevWrite_ByObjIDs_ProveAccessedObjsAreOSObjects(
    s:state,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneStateSubset(s)

    requires forall id :: id in wsm_td_id_val_map
                ==> id !in s.objects.usbpdev_tds
    requires forall id :: id in wsm_fd_id_val_map
                ==> id !in s.objects.usbpdev_fds
    requires forall id :: id in wsm_do_id_val_map
                ==> id !in s.objects.usbpdev_dos
        // Requirement: OS devices (except USB peripheral devices) cannot write USB peripheral devices in the OS partition

    requires MapGetKeys(wsm_td_id_val_map) <= WSM_AllTDIDs(s.objects) &&
            MapGetKeys(wsm_fd_id_val_map) <= WSM_AllFDIDs(s.objects) &&
            MapGetKeys(wsm_do_id_val_map) <= WSM_AllDOIDs(s.objects)

    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_td_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_fd_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    requires var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in wsm_do_id_val_map
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: Only objects in the OS partition is modified

    ensures forall id :: id in wsm_td_id_val_map 
                ==> id in s.objects.os_tds
    ensures forall id :: id in wsm_fd_id_val_map 
                ==> id in s.objects.os_fds
    ensures forall id :: id in wsm_do_id_val_map 
                ==> id in s.objects.os_dos
{
    Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate));
    reveal WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition();
}

lemma Lemma_OSDevAccess_ObjsToBeAccessedMustBeInOSParition(
    s:state, dm:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)
    requires IsValidState_Objects_UniqueObjIDs(dm.objects)

    requires td_ids <= WSM_AllTDIDs(s.objects)
    requires fd_ids <= WSM_AllFDIDs(s.objects)
    requires do_ids <= WSM_AllDOIDs(s.objects)

    requires forall id :: id in td_ids
                ==> ObjPID_KObjects(dm.objects, id.oid) == Partition_ID(PID_RESERVED_OS_PARTITION)
    requires forall id :: id in fd_ids
                ==> ObjPID_KObjects(dm.objects, id.oid) == Partition_ID(PID_RESERVED_OS_PARTITION)
    requires forall id :: id in do_ids
                ==> ObjPID_KObjects(dm.objects, id.oid) == Partition_ID(PID_RESERVED_OS_PARTITION)

    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in td_ids
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in fd_ids
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in do_ids
                ==> WSM_IsObjID(s.objects, id.oid) &&
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)
{
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
}

// [NOTE] Needs 70s to verify
lemma Lemma_OSDevWrite_WriteObjsMustInSystemAndNotHCodedTDs(
    s:state, dev_sid:Subject_ID, 
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: the device is in the red partition

    requires WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)

    ensures MapGetKeys(wsm_td_id_val_map) <= WSM_AllTDIDs(s.objects) &&
            MapGetKeys(wsm_fd_id_val_map) <= WSM_AllFDIDs(s.objects) &&
            MapGetKeys(wsm_do_id_val_map) <= WSM_AllDOIDs(s.objects)
        // Property 1
    ensures forall id :: id in wsm_td_id_val_map
                ==> id !in WSM_AllHCodedTDIDs(s.subjects)
{
    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var k := DMStateToState(dm);
    Lemma_DMStateToState_SecureK(dm, k);
    assert IsValidState(k) && IsSecureState(k);

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

    Lemma_OSDevWrite_WriteObjsMustInSystemAndNotHCodedTDs_Property1(s, dm, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
}

lemma Lemma_OSDevWrite_WriteObjsMustInSystemAndNotHCodedTDs_Property1(
    s:state, dm:DM_State, dev_sid:Subject_ID, 
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
             var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
             var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
             (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(dm.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(dm.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(dm.objects))

    ensures MapGetKeys(wsm_td_id_val_map) <= WSM_AllTDIDs(s.objects) &&
            MapGetKeys(wsm_fd_id_val_map) <= WSM_AllFDIDs(s.objects) &&
            MapGetKeys(wsm_do_id_val_map) <= WSM_AllDOIDs(s.objects)
{
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
}

// Lemma: When writing new values into OS objects, the new state must be valid and secure 
lemma Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(
    s:state, s':state, os_tds':map<TD_ID, OS_TD_State>, os_fds':map<FD_ID, OS_FD_State>, os_dos':map<DO_ID, OS_DO_State>
)
    requires InstSaneState(s)
    requires s' == s.(objects := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos'))
    requires MapGetKeys(os_tds') == MapGetKeys(s.objects.os_tds)
    requires MapGetKeys(os_fds') == MapGetKeys(s.objects.os_fds)
    requires MapGetKeys(os_dos') == MapGetKeys(s.objects.os_dos)

    requires forall id :: id in s.objects.os_tds
                ==> s.objects.os_tds[id].pid == s'.objects.os_tds[id].pid
    requires forall id :: id in s.objects.os_fds
                ==> s.objects.os_fds[id].pid == s'.objects.os_fds[id].pid
    requires forall id :: id in s.objects.os_dos
                ==> s.objects.os_dos[id].pid == s'.objects.os_dos[id].pid
        // Requirement: PIDs of OS objects is unchanged

    requires forall td_id :: td_id in WSM_AllHCodedTDIDs(s.subjects) &&
                    td_id in s.objects.os_tds
                ==> s.objects.os_tds[td_id] == s'.objects.os_tds[td_id]
        // Requirement: OS's hardcoded TDs are unchanged

    ensures InstSaneState(s')
{
    reveal WK_ValidState_DevsActivateCond();
    reveal WK_ValidObjsAddrs_PEHCIs();

    forall id | id in s'.objects.os_tds
        ensures s.objects.os_tds[id].pid == s'.objects.os_tds[id].pid
    {
        if(id in WSM_AllHCodedTDIDs(s.subjects))
        {
            assert s.objects.os_tds[id].pid == s'.objects.os_tds[id].pid;
        }
        else
        {
            assert s.objects.os_tds[id].pid == s'.objects.os_tds[id].pid;
        }
    }
    
    Lemma_WK_ValidObjs_Properties(s.subjects, s.objects);
    
    Lemma_ValidObjs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidIDMappings_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidObjsAddrs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidObjAddrs_WimpDrv_DOPAddrs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged(s, s');
    Lemma_ValidGVarValues_ActiveUSBPDevs_OnObjectModification_IfObjIDsAndPIDsAreUnchanged(s, s');
}

lemma Lemma_OSDevWrite_ByPAddr_ProveSanityOfNewState_SI1(
    s:state, s':state, dev_sid:Subject_ID,
    paddr:PAddrRegion, new_v:string
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The device is in the red partition
    requires paddr.paddr_start <= paddr.paddr_end

    requires var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
             WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)

    requires var t1:= OSDevWrite_ByPAddr_InnerFunc(s, dev_sid, paddr, new_v);
             s' == t1.0
        // Requirement: State in the WK implementation spec is modified correctly

    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires var dm := WSM_MapState(s);
             DM_IsValidState(dm) && DM_IsSecureState(dm)
        // Pre-conditions needed by <WSD_OSDevWrite_Stub>
    requires var dm := WSM_MapState(s);
             var dm' := WSM_MapState(s');
             var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
             var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
             var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
             var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

             var result := WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
             dm' == result.0
        // Requirement: State in the WK design spec is modified correctly

    ensures WSM_OpsSaneState_Security_SI1(s')
{
    reveal WSM_OpsSaneState_Security_SI1();

    var dm := WSM_MapState(s);
    var dm' := WSM_MapState(s');
    var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
    var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
    var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
    var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    var result := WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert dm' == result.0;
    assert DM_IsValidState(dm') && DM_IsSecureState(dm');
    assert DM_IsSecureState_SI1(dm');
}

lemma Lemma_OSDevWrite_ByPIO_ProveSanityOfNewState_SI1(
    s:state, s':state, dev_sid:Subject_ID,
    pio_addr:ioaddr, new_v:string
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The device is in the red partition

    requires var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
             WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)

    requires var t1:= OSDevWrite_ByPIO_InnerFunc(s, dev_sid, pio_addr, new_v);
             s' == t1.0
        // Requirement: State in the WK implementation spec is modified correctly

    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires var dm := WSM_MapState(s);
             DM_IsValidState(dm) && DM_IsSecureState(dm)
        // Pre-conditions needed by <WSD_OSDevWrite_Stub>
    requires var dm := WSM_MapState(s);
             var dm' := WSM_MapState(s');
             var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
             var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
             var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
             var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

             var result := WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
             dm' == result.0
        // Requirement: State in the WK design spec is modified correctly

    ensures WSM_OpsSaneState_Security_SI1(s')
{
    reveal WSM_OpsSaneState_Security_SI1();

    var dm := WSM_MapState(s);
    var dm' := WSM_MapState(s');
    var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
    var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
    var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
    var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    var result := WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert dm' == result.0;
    assert DM_IsValidState(dm') && DM_IsSecureState(dm');
    assert DM_IsSecureState_SI1(dm');
}

// [NOTE] Needs 80s to verify
lemma Lemma_OSNonUSBPDevWrite_ByObjIDs_ProveSanityOfNewState_SI1(
    s:state, s':state, dev_sid:Subject_ID,
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The device is in the red partition

    requires WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
        // Requirement: If the OS device writes to a set of TDs/FDs/DOs with some values, then the device must be able  
        // to write the corresponding objects with the corresponding values in the WK design model
    requires forall id :: id in wsm_td_id_val_map
                ==> id !in s.objects.usbpdev_tds
    requires forall id :: id in wsm_fd_id_val_map
                ==> id !in s.objects.usbpdev_fds
    requires forall id :: id in wsm_do_id_val_map
                ==> id !in s.objects.usbpdev_dos
        // Requirement: OS devices (except USB peripheral devices) cannot write USB peripheral devices in the OS partition

    requires var t1:= OSNonUSBPDevWrite_ByObjIDs_InnerFunc(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
             s' == t1.0
        // Requirement: State in the WK implementation spec is modified correctly

    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires var dm := WSM_MapState(s);
             DM_IsValidState(dm) && DM_IsSecureState(dm)
        // Pre-conditions needed by <WSD_OSDevWrite_Stub>
    requires var dm := WSM_MapState(s);
             var dm' := WSM_MapState(s');
             var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
             var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
             var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

             var result := WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
             dm' == result.0
        // Requirement: State in the WK design spec is modified correctly

    ensures WSM_OpsSaneState_Security_SI1(s')
{
    reveal WSM_OpsSaneState_Security_SI1();

    var dm := WSM_MapState(s);
    var dm' := WSM_MapState(s');
    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    var result := WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert dm' == result.0;
    assert DM_IsValidState(dm') && DM_IsSecureState(dm');
    assert DM_IsSecureState_SI1(dm');
}




/*********************** Lemmas - USBPDevs ********************/
lemma Lemma_USBPDevRead_ByObjID_Summary(dm:DM_State, dev_sid:Subject_ID, read_fds:set<FD_ID>, read_dos:set<DO_ID>)
    requires var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
             DM_DevRead_PreConditions(dm, dev_sid, read_objs, map[], map[], map[]) &&
             DM_DevRead_InnerFunc(dm, dev_sid, read_objs, map[], map[], map[]) == (dm, true)

    ensures var read_objs2 := FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            DM_DevRead_PreConditions(dm, dev_sid, read_objs2, map[], map[], map[]) &&
            DM_DevRead_InnerFunc(dm, dev_sid, read_objs2, map[], map[], map[]) == (dm, true)
{
    var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
    var read_objs2 := FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);

    assert read_objs == read_objs2;
}

lemma Lemma_USBPDevAccess_ProveSubjAndItsObjsInSamePartition(
    s:state, dev_sid:Subject_ID, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)

    requires WSM_IsUSBPDevID(s.subjects, Dev_ID(dev_sid))
    requires forall fd_id2 :: fd_id2 in fd_ids
				==> fd_id2 in s.subjects.usbpdevs[Dev_ID(dev_sid)].fd_ids
    requires forall do_id2 :: do_id2 in do_ids
				==> do_id2 in s.subjects.usbpdevs[Dev_ID(dev_sid)].do_ids

    ensures forall id :: id in fd_ids
                ==> WSM_IsObjID(s.objects, id.oid)
    ensures forall id :: id in do_ids
                ==> WSM_IsObjID(s.objects, id.oid)

    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in fd_ids
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, dev_sid)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in do_ids
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, dev_sid)
{
    var globals := wkm_get_globals(s.wk_mstate);

    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    forall id | id in fd_ids
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, dev_sid)
    {
        Lemma_ObjPID_SamePIDWithOwnerSubject(
            s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid, id.oid);
    }

    forall id | id in do_ids
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, dev_sid)
    {
        Lemma_ObjPID_SamePIDWithOwnerSubject(
            s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid, id.oid);
    }
}

// Lemma: When writing new values into USBPDev's objects, the new state must be valid and secure 
lemma Lemma_USBPDevObjsUpdate_ProveSanityOfNewState(s:state, s':state, new_usbpdevs_fds:map<FD_ID, FD_Val>, new_usbpdevs_dos:map<DO_ID, DO_Val>)
    requires InstSaneState(s)
    requires s' == s.(objects := s.objects.(usbpdev_fds := new_usbpdevs_fds, usbpdev_dos := new_usbpdevs_dos))
    requires MapGetKeys(new_usbpdevs_fds) == MapGetKeys(s.objects.usbpdev_fds)
    requires MapGetKeys(new_usbpdevs_dos) == MapGetKeys(s.objects.usbpdev_dos)

    ensures InstSaneState(s')
{
    reveal WK_ValidState_DevsActivateCond();
    reveal WK_ValidObjsAddrs_PEHCIs();

    Lemma_WK_ValidObjs_Properties(s.subjects, s.objects);
    
    Lemma_ValidObjs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidIDMappings_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidObjsAddrs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidObjAddrs_WimpDrv_DOPAddrs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged(s, s');
}




/*********************** Lemmas - EEHCIs ********************/
// Lemma: When writing new values into EEHCI's status register, the new state must be valid and secure 
lemma Lemma_EEHCIWriteStatusReg_ProveSanityOfNewState(s:state, s':state, eehci_slot:word, new_val:word)
    requires InstSaneState(s)
    
    requires eehci_valid_slot_id(eehci_slot)
    requires var old_globals := wkm_get_globals(s.wk_mstate);
             var new_globals := wkm_get_globals(s'.wk_mstate);
             new_globals == eehci_mem_set_status_reg(old_globals, eehci_slot, new_val);
    requires var new_globals := wkm_get_globals(s'.wk_mstate);
             s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))

    ensures InstSaneState(s')
{
    reveal WK_ValidState_DevsActivateCond();
    reveal WK_ValidObjsAddrs_PEHCIs();

    var old_globals := wkm_get_globals(s.wk_mstate);
    var new_globals := wkm_get_globals(s'.wk_mstate);

    // Prove WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    ghost var status_reg_vaddr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset;
    Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(old_globals, new_globals);
    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(old_globals, new_globals);
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfGEEHCIMemUpdateStatus(old_globals, new_globals, eehci_slot, status_reg_vaddr, new_val);
    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteEEHCIStatus(old_globals, new_globals, eehci_slot, status_reg_vaddr, new_val);
    assert WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate));

    // Prove WSM_SubjPIDs are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s, s');
    
    Lemma_WK_ValidObjs_Properties(s.subjects, s.objects);
    
    Lemma_ValidObjs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidIDMappings_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s, s');
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s, s');
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s, s');
    Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s, s');

    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s, s');
    Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s, s');
}

lemma Lemma_EEHCIAccessOwnObjs_ProveSubjAndItsObjsInSamePartition(
    s:state, dev_sid:Subject_ID, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)

    requires WSM_IsEEHCIDevID(s.subjects, Dev_ID(dev_sid))

    requires forall do_id2 :: do_id2 in do_ids
				==> do_id2 in s.subjects.eehcis[Dev_ID(dev_sid)].do_ids

    ensures forall id :: id in do_ids
                ==> WSM_IsObjID(s.objects, id.oid)

    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in do_ids
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, dev_sid)
{
    var globals := wkm_get_globals(s.wk_mstate);

    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    forall id | id in do_ids
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, dev_sid)
    {
        Lemma_ObjPID_SamePIDWithOwnerSubject(
            s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid, id.oid);
    }
}

// Lemma: When writing new values into wimp drivers' DOs, the new state must be valid and secure 
lemma Lemma_WimpDrvDOUpdate_ProveSanityOfNewState(s:state, s':state, new_wimpdrv_dos:map<DO_ID, DO_Val>)
    requires InstSaneState(s)
    requires s' == s.(objects := s.objects.(wimpdrv_dos := new_wimpdrv_dos))
    requires MapGetKeys(new_wimpdrv_dos) == MapGetKeys(s.objects.wimpdrv_dos)

    ensures InstSaneState(s')
{
    reveal WK_ValidState_DevsActivateCond();
    reveal WK_ValidObjsAddrs_PEHCIs();
    
    Lemma_WK_ValidObjs_Properties(s.subjects, s.objects);
    
    Lemma_ValidObjs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidIDMappings_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidObjsAddrs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_ValidObjAddrs_WimpDrv_DOPAddrs_OnObjectModification_IfObjIDsAreUnchanged(s, s');
    Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged(s, s');
}

// Lemma: The objects accessed by eEHCIs by PAddrs must be WimpDrvs' DOs in the same partition with the eEHCIs
lemma Lemma_EEHCIReadWriteObjs_ByPAddr_ProveAccessWimpDrvDOsInSamePartitionOnly_ShowExistence(
    s:state, eehci_slot:word, paddr_start:paddr, paddr_end:uint
)
    requires InstSaneState(s)
    requires paddr_start < paddr_end
    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(wkm_get_globals(s.wk_mstate), eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active
    requires EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer(s, eehci_slot, paddr_start, paddr_end)
        // Requirement: The access must be defined

    ensures var globals := wkm_get_globals(s.wk_mstate); 
            exists wimpdrv_slot:word :: wimpdrv_valid_slot_id(wimpdrv_slot) &&
                wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, paddr_start, paddr_end) &&
                wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
{
    var wimpdrv_slot := Lemma_EEHCIReadWriteObjs_ByPAddr_ProveAccessWimpDrvDOsInSamePartitionOnly(s, eehci_slot, paddr_start, paddr_end);
}

// Lemma: The objects accessed by eEHCIs by PAddrs must be WimpDrvs' DOs in the same partition with the eEHCIs
lemma Lemma_EEHCIReadWriteObjs_ByPAddr_ProveAccessWimpDrvDOsInSamePartitionOnly(
    s:state, eehci_slot:word, paddr_start:paddr, paddr_end:uint
) returns (wimpdrv_slot:word)
    requires InstSaneState(s)
    requires paddr_start < paddr_end
    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(wkm_get_globals(s.wk_mstate), eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active
    requires EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer(s, eehci_slot, paddr_start, paddr_end)
        // Requirement: The access must be defined

    ensures wimpdrv_valid_slot_id(wimpdrv_slot)
    ensures wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, paddr_start, paddr_end)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
{
    var globals := wkm_get_globals(s.wk_mstate);
    assert P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals);

    // Apply EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer
    var next_target_usbtd_slot:word :| next_target_usbtd_slot != USBTD_SlotID_INVALID &&
        (
            Lemma_CanActiveEEHCIReadUSBTD_ProveProperty(globals, eehci_slot, next_target_usbtd_slot);
            CanActiveEEHCIReadUSBTD(globals, eehci_slot, next_target_usbtd_slot)
            // Exist a USB TD, and the eEHCI can read the USB TD
        ) &&
        (usbtd_map_get_type(globals, next_target_usbtd_slot) == USBTDs_TYPE_QTD32 || usbtd_map_get_type(globals, next_target_usbtd_slot) == USBTDs_TYPE_QH32) &&  
            // [TODO] Not support iTD and siTD yet
        usbtd_is_paddr_region_within_one_buffer_region(globals, next_target_usbtd_slot, paddr_start, paddr_end);
            // And [access_paddr_start, access_paddr_end) must be inside one of the multiple buffer regions defined in 
            // the USB TD

    // Prove the USB TD is secure/verfied
    assert TestBit(usbtd_map_get_flags(globals, next_target_usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit);

    assert WK_USBTD_Map_SecureGlobalVarValues(globals);
    if(usbtd_map_get_type(globals, next_target_usbtd_slot) == USBTDs_TYPE_QTD32)
    {
        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals, next_target_usbtd_slot);
        reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
        reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();

        // Return <wimpdrv_slot>
        wimpdrv_slot := usbtd_map_get_wimpdrv_slotid(globals, next_target_usbtd_slot);

        // Prove wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
        assert usbtd_map_get_pid(globals, next_target_usbtd_slot) == wimpdrv_get_pid(globals, wimpdrv_slot);
        assert P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(globals, eehci_slot);
    }
    else
    {
        assert usbtd_map_get_type(globals, next_target_usbtd_slot) == USBTDs_TYPE_QH32;
        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals, next_target_usbtd_slot);
        reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
        reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

        // Return <wimpdrv_slot>
        wimpdrv_slot := usbtd_map_get_wimpdrv_slotid(globals, next_target_usbtd_slot);

        // Prove wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
        assert usbtd_map_get_pid(globals, next_target_usbtd_slot) == wimpdrv_get_pid(globals, wimpdrv_slot);
    }
}

// Lemma: The objects accessed by WimpDrvs by PAddrs must be WimpDrvs' DOs in the same partition with the eEHCIs
lemma Lemma_WimpDrvReadWriteObjs_ByPAddr_ProveAccessOwnDO(s:state, wimpdrv_slot:word, paddr_start:paddr, paddr_end:uint)
    requires InstSaneState(s)
    requires paddr_start < paddr_end
    requires wimpdrv_valid_slot_id(wimpdrv_slot)

    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires var globals := wkm_get_globals(s.wk_mstate); 
             wimpdrv_do_get_paddr_base(globals, wimpdrv_slot) <= paddr_start < paddr_end <= wimpdrv_do_get_paddr_end(globals, wimpdrv_slot)

    ensures wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, paddr_start, paddr_end)
{
    // Dafny can automatically prove this lemma
}

// Lemma: The WimpDrv accessing objects must have the flag WimpDrv_Slot_UpdateFlag_Complete
lemma Lemma_WimpDrvReadWriteObjs_ByPAddr_ProveFlagIsCompleteAndRecordedPIDIsNotInvalid(s:state, drv_id_word:word)
    requires InstSaneState(s)
    requires drv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
             WSM_IsWimpDrvID(s.subjects, drv_id)
        // Requirement: The wimp driver must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_idword_in_record(globals, drv_id_word)

    requires var globals := wkm_get_globals(s.wk_mstate);
             var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_id.sid) in pids_parse_g_wimp_pids(globals)
        // Requirement: The given wimp driver with the ID <drv_id_word> must be in a wimp partition

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
            wimpdrv_do_get_flag(globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
            wimpdrv_get_pid(globals, drv_slot) != WS_PartitionID(PID_INVALID)

{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();

    var globals := wkm_get_globals(s.wk_mstate);
    var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
    var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);

    Lemma_WimpDrv_DrvID_ToIDWord_ProveCorrectness(s.subjects, s.objects, s.id_mappings, drv_id_word, drv_id);
    if(wimpdrv_do_get_flag(globals, drv_slot) != WimpDrv_Slot_UpdateFlag_Complete)
    {
        assert SubjPID_WimpDrv_ByIDWord(globals, drv_id_word) == WS_PartitionID(PID_INVALID);
        assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_id.sid) == WS_PartitionID(PID_INVALID);

        assert false;
    }
}




/*********************** Private Lemmas ********************/
// Lemma: On <s.object> modification, if ObjIDs are unchanged and hardcoded TDs are unchanged, then WK_ValidObjs holds
lemma Lemma_ValidObjs_OnObjectModification_IfObjIDsAreUnchanged(s:state, s':state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires s.subjects == s'.subjects
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires s.objects.eehci_hcoded_tds == s'.objects.eehci_hcoded_tds
    requires s.objects.usbpdev_tds == s'.objects.usbpdev_tds
    requires forall dev_id :: dev_id in s.subjects.os_devs
                ==> s.subjects.os_devs[dev_id].hcoded_td_id in s.objects.os_tds
    requires forall dev_id :: dev_id in s.subjects.os_devs
                ==> s.objects.os_tds[s.subjects.os_devs[dev_id].hcoded_td_id] == s'.objects.os_tds[s.subjects.os_devs[dev_id].hcoded_td_id]
        // Requirement: Hardcoded TDs are unchanged

    ensures WK_ValidObjs(s'.subjects, s'.objects)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjs_HCodedTDs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();
    reveal WK_ValidObjs_eEHCIs();

    assert WK_ValidObjs_ObjIDs(s'.objects);
    assert WK_ValidObjs_ObjInSubjsMustBeInState(s'.subjects, s'.objects);
    Lemma_ValidObjs_OnObjectModification_IfObjIDsAreSame_HCodedTDs(s, s');
    assert WK_ValidObjs_HCodedTDs(s'.subjects, s'.objects);
    assert WK_ValidObjs_InternalObjsOf_WimpSubjects(s'.subjects, s'.objects);
    assert WK_ValidObjs_eEHCIs(s'.subjects, s'.objects);
}

// Lemma: On <s.object> modification, If ObjIDs are unchanged and ObjPIDs are unchanged, then 
// WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition holds
lemma Lemma_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnObjectModification_IfObjIDsAreUnchanged(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))

    requires s.wk_mstate == s'.wk_mstate
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall o_id :: WSM_IsObjID(s.objects, o_id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), o_id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), o_id)
        // Requirement: Object PIDs are unchanged

    ensures WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition();
}

// Lemma: On <s.object> modification, If ObjIDs are unchanged, then WK_ValidObjAddrs_WimpDrv_DOPAddrs holds
lemma Lemma_ValidObjAddrs_WimpDrv_DOPAddrs_OnObjectModification_IfObjIDsAreUnchanged(s:state, s':state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s.wk_mstate))
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs_SubjIDs(s.subjects)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires (MapGetKeys(s.objs_addrs.tds_addrs) == MapGetKeys(s.objects.os_tds) + MapGetKeys(s.objects.eehci_hcoded_tds) + 
                                         s.objects.eehci_other_tds + MapGetKeys(s.objects.usbpdev_tds) + (s.objects.usbtd_tds)
            ) &&
            (MapGetKeys(s.objs_addrs.fds_addrs) == MapGetKeys(s.objects.os_fds) + 
                                                s.objects.eehci_fds + MapGetKeys(s.objects.usbpdev_fds) + (s.objects.usbtd_fds)
            ) &&
            (MapGetKeys(s.objs_addrs.dos_addrs) == MapGetKeys(s.objects.os_dos) + s.objects.eehci_dos + 
                                                MapGetKeys(s.objects.usbpdev_dos) + MapGetKeys(s.objects.wimpdrv_dos) + (s.objects.usbtd_dos)
            )

    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s'.wk_mstate))
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs_SubjIDs(s'.subjects)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires (MapGetKeys(s'.objs_addrs.tds_addrs) == MapGetKeys(s'.objects.os_tds) + MapGetKeys(s'.objects.eehci_hcoded_tds) + 
                                         s'.objects.eehci_other_tds + MapGetKeys(s'.objects.usbpdev_tds) + (s'.objects.usbtd_tds)
            ) &&
            (MapGetKeys(s'.objs_addrs.fds_addrs) == MapGetKeys(s'.objects.os_fds) + 
                                                s'.objects.eehci_fds + MapGetKeys(s'.objects.usbpdev_fds) + (s'.objects.usbtd_fds)
            ) &&
            (MapGetKeys(s'.objs_addrs.dos_addrs) == MapGetKeys(s'.objects.os_dos) + s'.objects.eehci_dos + 
                                                MapGetKeys(s'.objects.usbpdev_dos) + MapGetKeys(s'.objects.wimpdrv_dos) + (s'.objects.usbtd_dos)
            )

    requires WK_ValidObjAddrs_WimpDrv_DOPAddrs(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.wk_mstate == s'.wk_mstate
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();
    // Dafny can automatically prove this lemma
}

// Lemma: On <s.object> modification, If ObjIDs are unchanged and ObjPIDs are unchanged, then 
// WK_ValidGlobalVarValues_USBPDevs holds
lemma Lemma_ValidGVarValues_ActiveUSBPDevs_OnObjectModification_IfObjIDsAndPIDsAreUnchanged(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidGlobalVarValues_USBPDevs(s.subjects, wkm_get_globals(s.wk_mstate))

    requires s.wk_mstate == s'.wk_mstate
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall o_id :: WSM_IsObjID(s.objects, o_id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), o_id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), o_id)
        // Requirement: Object PIDs are unchanged

    ensures WK_ValidGlobalVarValues_USBPDevs(s'.subjects, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidGlobalVarValues_USBPDevs();
}

lemma Lemma_DM_DevRead_DevAndReadObjsAreInSamePartition(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    read_tds:set<TD_ID>,
    read_fds:set<FD_ID>,
    read_dos:set<DO_ID> 
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active

    requires DM_DevRead_TransfersMustBeDefinedInWSDesignModel(ws, dev_sid, read_tds, read_fds, read_dos)
    requires forall id :: id in read_tds
            ==> id in AllTDIDs(ws.objects)
    requires forall id :: id in read_fds
            ==> id in AllFDIDs(ws.objects)
    requires forall id :: id in read_dos
            ==> id in AllDOIDs(ws.objects) 

    ensures forall id :: id in read_tds
                ==> ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
    ensures forall id :: id in read_fds
                ==> ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
    ensures forall id :: id in read_dos
                ==> ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
        // Property 1: Objects to be modified must be in the same partition with the device
{
    Lemma_DM_DevRead_DevAndReadObjsAreInSamePartition_TDs(ws, dev_sid, read_tds, read_fds, read_dos);
    Lemma_DM_DevRead_DevAndReadObjsAreInSamePartition_FDs(ws, dev_sid, read_tds, read_fds, read_dos);
    Lemma_DM_DevRead_DevAndReadObjsAreInSamePartition_DOs(ws, dev_sid, read_tds, read_fds, read_dos);
}

lemma Lemma_DM_DevRead_ReadObjsMustInSystemAndNotHCodedTDs(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    read_tds:set<TD_ID>,
    read_fds:set<FD_ID>,
    read_dos:set<DO_ID> 
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is in the red partition

    requires DM_DevRead_TransfersMustBeDefinedInWSDesignModel(ws, dev_sid, read_tds, read_fds, read_dos)

    ensures forall id :: id in read_tds
            ==> id in AllTDIDs(ws.objects)
    ensures forall id :: id in read_fds
            ==> id in AllFDIDs(ws.objects)
    ensures forall id :: id in read_dos
            ==> id in AllDOIDs(ws.objects)
    ensures forall id :: id in read_tds
                ==> id !in AllHCodedTDIDs(ws.subjects)
        // Property 2: Hardcoded TDs are unchanged
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    // Prove StatePropertiesCorollary2(k)
    Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
    Lemma_StatePropertyCorollary1_ImpliesCorollary2(k);
    assert StatePropertiesCorollary2(k);

    var k_params := KToKParams(k);
    Lemma_K_DevRead_ReadObjsMustInSystemAndNotHCodedTDs(k, Dev_ID(dev_sid), read_tds, read_fds, read_dos);
}

lemma Lemma_DM_DevRead_DevAndReadObjsAreInSamePartition_TDs(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    read_tds:set<TD_ID>,
    read_fds:set<FD_ID>,
    read_dos:set<DO_ID>
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active

    requires DM_DevRead_TransfersMustBeDefinedInWSDesignModel(ws, dev_sid, read_tds, read_fds, read_dos)
    requires forall id :: id in read_tds
            ==> id in AllTDIDs(ws.objects)

    ensures forall id :: id in read_tds
                ==> ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
        // Property 1: Objects to be modified must be in the same partition with the device
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    // Prove StatePropertiesCorollary2(k)
    Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
    Lemma_StatePropertyCorollary1_ImpliesCorollary2(k);
    assert StatePropertiesCorollary2(k);

    var dev_id := Dev_ID(dev_sid);
    var k_tds_state := ActiveTDsState(k);
    var k_params := KToKParams(k);

    forall id | id in read_tds
        ensures ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
    {
        assert dev_id in AllActiveDevs(k);

        assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, k_tds_state, dev_id, id.oid);
        assert DevAModesToObj(k, k_tds_state, dev_id, id.oid) != {};
    }
}

lemma Lemma_DM_DevRead_DevAndReadObjsAreInSamePartition_FDs(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    read_tds:set<TD_ID>,
    read_fds:set<FD_ID>,
    read_dos:set<DO_ID> 
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active

    requires DM_DevRead_TransfersMustBeDefinedInWSDesignModel(ws, dev_sid, read_tds, read_fds, read_dos)
    requires forall id :: id in read_fds
            ==> id in AllFDIDs(ws.objects)

    ensures forall id :: id in read_fds
                ==> ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
        // Property 1: Objects to be modified must be in the same partition with the device
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    // Prove StatePropertiesCorollary2(k)
    Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
    Lemma_StatePropertyCorollary1_ImpliesCorollary2(k);
    assert StatePropertiesCorollary2(k);

    var dev_id := Dev_ID(dev_sid);
    var k_tds_state := ActiveTDsState(k);
    var k_params := KToKParams(k);

    forall id | id in read_fds
        ensures ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
    {
        assert dev_id in AllActiveDevs(k); 

        assert K_DevRead_ReadFDMustBeInATransfer(k, dev_sid, id);
        Lemma_K_DevRead_ReadFDMustBeInATransfer_ImpliesDevAModesToObjFromTDs_ExistR_SlimState(k, dev_sid, id);
        assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, k_tds_state, dev_id, id.oid);
        assert DevAModesToObj(k, k_tds_state, dev_id, id.oid) != {};
    }
}

lemma Lemma_DM_DevRead_DevAndReadObjsAreInSamePartition_DOs(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    read_tds:set<TD_ID>,
    read_fds:set<FD_ID>,
    read_dos:set<DO_ID> 
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active

    requires DM_DevRead_TransfersMustBeDefinedInWSDesignModel(ws, dev_sid, read_tds, read_fds, read_dos)
    requires forall id :: id in read_dos
            ==> id in AllDOIDs(ws.objects) 

    ensures forall id :: id in read_dos
                ==> ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
        // Property 1: Objects to be modified must be in the same partition with the device
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    // Prove StatePropertiesCorollary2(k)
    Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
    Lemma_StatePropertyCorollary1_ImpliesCorollary2(k);
    assert StatePropertiesCorollary2(k);

    var dev_id := Dev_ID(dev_sid);
    var k_tds_state := ActiveTDsState(k);
    var k_params := KToKParams(k);

    forall id | id in read_dos
        ensures ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
    {
        assert dev_id in AllActiveDevs(k); 

        assert K_DevRead_ReadDOMustBeInATransfer(k, dev_sid, id);
        Lemma_K_DevRead_ReadDOMustBeInATransfer_ImpliesDevAModesToObjFromTDs_ExistR_SlimState(k, dev_sid, id);
        assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, k_tds_state, dev_id, id.oid);
        assert DevAModesToObj(k, k_tds_state, dev_id, id.oid) != {};
    }
}