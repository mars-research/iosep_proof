include "DM_Operations_Stubs.s.dfy"
include "state_map_OpsSaneStateSubset.s.dfy"
include "../state_properties_OpsSaneStateSubset.s.dfy"
include "../transition_constraints.s.dfy"
include "../SecurityProperties.dfy"
include "../utils/model/headers_any_state.dfy"
include "../utils/model/utils_objs_valid_state.s.dfy"
include "../dev/usb2/usb_pdev.i.dfy"
include "../dev/usb2/eehci_mem.i.dfy"
include "../drv/drv.i.dfy"
include "io_accesses_commutative_diagram.i.dfy"
include "DM_AdditionalPropertiesLemmas.i.dfy"
include "../state_properties_OpsSaneStateSubset.i.dfy"
include "../utils/model/utils_objs_secure_state.i.dfy"

// [NOTE] Some of the commutative diagram prove ends up at DM_*_InnerFunc functions, because they EQUAL to the corresponding operations in the WK design.

/*********************** Operations - OSDrv Read ********************/
// Operation: OS drivers issue read access to target object (reference by memory address). 
// For example, configuring devices
function OSDrvRead_ByPAddr(
    s:state,
    drv_sid:Subject_ID,
    paddr:PAddrRegion
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires paddr.paddr_start <= paddr.paddr_end
        // Requirement: Valid memory address

    requires var t := OSDrvRead_ByPAddr_GetReadObjs(s, paddr);
             var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
             var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
             var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
             (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==> id !in read_tds)
        // Requirement: The objects read by the driver must be active in the OS partition, and cannot be hardcoded TDs
        // This pre-condition reflexes the late access mediation done by MMU

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var t := OSDrvRead_ByPAddr_GetReadObjs(s, paddr);
            var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
            var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
            var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, read_tds, read_fds, read_dos)
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var t := OSDrvRead_ByPAddr_GetReadObjs(s, paddr);
            var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
            var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
            var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
            var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_RedDrvRead_PreConditions(ws, drv_sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_RedDrvRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var t := OSDrvRead_ByPAddr_GetReadObjs(s, paddr);
    var read_tds := t.0;
    var read_fds := t.1;
    var read_dos := t.2;

    // Prove DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, drv_sid, read_tds, read_fds, read_dos)
    Lemma_OSDrvRead_ProveDM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(s, dm, drv_sid,
        read_tds, read_fds, read_dos);
    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, drv_sid, read_tds, read_fds, read_dos);

    // Prove commutative diagram
    Lemma_OSDrvRead_ProveCommutativeDiagram(s, dm, drv_sid, read_tds, read_fds, read_dos);

    (s, true)
}

// Operation: OS drivers issue read access to target object (reference by PIO address). 
// For example, configuring devices
function OSDrvRead_ByPIO(
    s:state,
    drv_sid:Subject_ID,
    pio_addr:ioaddr
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires var t := OSDrvRead_ByPIO_GetReadObjs(s, pio_addr);
             var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
             var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
             var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
             (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==> id !in read_tds)
        // Requirement: The objects read by the driver must be active in the OS partition, and cannot be hardcoded TDs
        // This pre-condition holds because only active "non-USB" OS objects exist in the PIO address space
        // [NOTE] In the OS partition, "non-USB" devices not plugged-in are considered to be always active. This is because 
        // clearing their objects on activation is unnecessary, as only OS drivers and devices can access these devices. 

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var t := OSDrvRead_ByPIO_GetReadObjs(s, pio_addr);
            var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
            var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
            var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, read_tds, read_fds, read_dos)
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var t := OSDrvRead_ByPIO_GetReadObjs(s, pio_addr);
            var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
            var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
            var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
            var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_RedDrvRead_PreConditions(ws, drv_sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_RedDrvRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var t := OSDrvRead_ByPIO_GetReadObjs(s, pio_addr);
    var read_tds := t.0;
    var read_fds := t.1;
    var read_dos := t.2;

    // Prove DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, drv_sid, read_tds, read_fds, read_dos)
    Lemma_OSDrvRead_ProveDM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(s, dm, drv_sid,
        read_tds, read_fds, read_dos);
    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, drv_sid, read_tds, read_fds, read_dos);

    // Prove commutative diagram
    Lemma_OSDrvRead_ProveCommutativeDiagram(s, dm, drv_sid, read_tds, read_fds, read_dos);

    (s, true)
}

// Operation: OS drivers issue read access to target object (reference by object IDs). 
// For example, receiving interrupts
function OSDrvRead_ByObjIDs(
    s:state,
    drv_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires P_OSDrvAccess_AccessActiveObjsOnly(s, read_tds, read_fds, read_dos) &&
             (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==> id !in read_tds)
        // Requirement: The objects read by the driver must be active in the OS partition, and cannot be hardcoded TDs
        // This pre-condition holds because all OS drivers and devices cannot access any objects of pEHCIs, eEHCIs,  
        // USB peripheral devices by object IDs.
        // [NOTE] In the OS partition, "non-USB" devices not plugged-in are considered to be always active. This is because 
        // clearing their objects on activation is unnecessary, as only OS drivers and devices can access these devices. 

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, read_tds, read_fds, read_dos)
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_RedDrvRead_PreConditions(ws, drv_sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_RedDrvRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    // Prove DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, drv_sid, read_tds, read_fds, read_dos)
    Lemma_OSDrvRead_ProveDM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(s, dm, drv_sid,
        read_tds, read_fds, read_dos);
    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, drv_sid, read_tds, read_fds, read_dos);

    // Prove commutative diagram
    Lemma_OSDrvRead_ProveCommutativeDiagram(s, dm, drv_sid, read_tds, read_fds, read_dos);

    (s, true)
}




/*********************** Operations - OSDev Read ********************/
// Operation: OS devices issue read access to target object (reference by memory addr). 
// For example, P2P access
// [NOTE] All device copy object operations equal to read + write
function OSDevRead_ByPAddr(
    s:state,
    dev_sid:Subject_ID,
    paddr:PAddrRegion
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The device is in the red partition

    requires paddr.paddr_start <= paddr.paddr_end
        // Requirement: Valid memory address

    requires var t := OSDevRead_ByPAddr_GetReadObjs(s, paddr);
             var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
             var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
             var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
             WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)
        // Requirement: If the OS device reads a set of TDs/FDs/DOs, then the device must be able to read the 
        // corresponding objects in the WK design model

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var t := OSDevRead_ByPAddr_GetReadObjs(s, paddr);
            var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
            var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
            var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, read_tds, read_fds, read_dos)
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var t := OSDevRead_ByPAddr_GetReadObjs(s, paddr);
            var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
            var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
            var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
            var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_DevRead_PreConditions(ws, dev_sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_DevRead_InnerFunc(ws, dev_sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_DevRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var t := OSDevRead_ByPAddr_GetReadObjs(s, paddr);
    var read_tds := t.0;
    var read_fds := t.1;
    var read_dos := t.2;

    // Prove read_* must be active OS TDs/FDs/DOs in the OS partition
    Lemma_DM_DevRead_Properties(dm, dev_sid, read_tds, read_fds, read_dos);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_OSDevAccess_ObjsToBeAccessedMustBeInOSParition(s, dm, read_tds, read_fds, read_dos);

    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, read_tds, read_fds, read_dos);

    // Prove read TDs cannot be any hardcoded TDs
    assert forall id :: id in read_tds
                ==> id !in WSM_AllHCodedTDIDs(s.subjects);

    // Prove commutative diagram
    Lemma_DevRead_ProveCommutativeDiagram(s, dm, dev_sid, read_tds, read_fds, read_dos);

    (s, true)
}

// Operation: OS devices issue read access to target object (reference by PIO addr). 
// For example, P2P access
function OSDevRead_ByPIO(
    s:state,
    dev_sid:Subject_ID,
    pio_addr:ioaddr
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The device is in the red partition

    requires var t := OSDevRead_ByPIO_GetReadObjs(s, pio_addr);
             var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
             var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
             var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
             WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)
        // Requirement: If the OS device reads a set of TDs/FDs/DOs, then the device must be able to read the 
        // corresponding objects in the WK design model

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var t := OSDevRead_ByPIO_GetReadObjs(s, pio_addr);
            var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
            var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
            var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, read_tds, read_fds, read_dos)
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var t := OSDevRead_ByPIO_GetReadObjs(s, pio_addr);
            var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
            var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
            var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
            var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_DevRead_PreConditions(ws, dev_sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_DevRead_InnerFunc(ws, dev_sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_DevRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var t := OSDevRead_ByPIO_GetReadObjs(s, pio_addr);
    var read_tds := t.0;
    var read_fds := t.1;
    var read_dos := t.2;

    // Prove read_* must be active OS TDs/FDs/DOs in the OS partition
    Lemma_DM_DevRead_Properties(dm, dev_sid, read_tds, read_fds, read_dos);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_OSDevAccess_ObjsToBeAccessedMustBeInOSParition(s, dm, read_tds, read_fds, read_dos);

    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, read_tds, read_fds, read_dos);

    // Prove read TDs cannot be any hardcoded TDs
    assert forall id :: id in read_tds
                ==> id !in WSM_AllHCodedTDIDs(s.subjects);

    // Prove commutative diagram
    Lemma_DevRead_ProveCommutativeDiagram(s, dm, dev_sid, read_tds, read_fds, read_dos);

    (s, true)
}

// Operation: OS devices issue read access to target object (reference by IDs). 
// For example, raising interrupts
function OSNonUSBPDevRead_ByObjIDs(
    s:state,
    dev_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The device is in the red partition

    requires WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)
        // Requirement: If the OS device reads a set of TDs/FDs/DOs, then the device must be able to read the 
        // corresponding objects in the WK design model

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, read_tds, read_fds, read_dos)
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_DevRead_PreConditions(ws, dev_sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_DevRead_InnerFunc(ws, dev_sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_DevRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    // Prove read_* must be active OS TDs/FDs/DOs in the OS partition
    Lemma_DM_DevRead_Properties(dm, dev_sid, read_tds, read_fds, read_dos);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_OSDevAccess_ObjsToBeAccessedMustBeInOSParition(s, dm, read_tds, read_fds, read_dos);

    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, read_tds, read_fds, read_dos);

    // Prove read TDs cannot be any hardcoded TDs
    assert forall id :: id in read_tds
                ==> id !in WSM_AllHCodedTDIDs(s.subjects);

    // Prove commutative diagram
    Lemma_DevRead_ProveCommutativeDiagram(s, dm, dev_sid, read_tds, read_fds, read_dos);

    (s, true)
}




/*********************** Operations - OSDrv Write ********************/
function OSDrvWrite_ByPAddr(
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
                ==> id !in wsm_td_id_val_map)
        // Requirement: The objects written by the driver must be active in the OS partition, and cannot be hardcoded TDs.
        // This pre-condition reflexes the late access mediation done by MMU
    
    requires var t1:= OSDrvWrite_ByPAddr_InnerFunc_Modification1(s, drv_sid, paddr, new_v);
             var t_s' := t1.0;
             OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(t_s') &&
             OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(t_s')
        // Requirement: We regard IOMMU perform early memory access mediation, even though it performs late mediation in 
        // fact.
        // Thus, before IOMMU performs mediation in OSDrvWrite, no OS TDs refs any wimp objects and pEHCIs by PIO 
        // addresses and IDs. This is because (1) pEHCIs's objects cannot be referenced by PIO addresses and object IDs, 
        // (2) they cannot reference any hardcoded TDs, (3) they cannot reference any wimp USBPDev's objects, 
        // and (4) other objects for wimp drivers can only be referenced via memory addresses
        // [NOTE] This axiom has been covered in <IOMMU_DevHWProt>

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var t := OSDrvWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
            var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
            result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var t := OSDrvWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
            var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
            var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
            var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
            var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_OSDrvWrite_Stub(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == ws' &&
                WSD_OSDrvWrite_Stub(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_OSDrvWrite in the WK design
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

    var ts'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
    var ts' := s.(objects := ts'_objs);

    // Prove pre-conditions of IOMMU_DevHWProt
    Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(s, ts', os_tds', os_fds', os_dos');
    assert OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(ts');
    Lemma_ValidState_ProveP_WimpObjs_HaveNoPIOAddr(ts');
    assert P_WimpObjs_HaveNoPIOAddr(ts');
    Lemma_ValidState_ProveP_PEHCIsObjs_HaveNoPIOAddr(ts');
    assert P_PEHCIsObjs_HaveNoPIOAddr(ts');

    // Apply IOMMU_DevHWProt
    var s' := IOMMU_DevHWProt(ts');

    // Prove the commutative diagram
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    var result := OSDrvWrite_ProveCommutativeDiagram_GetOpParamsForDesignModel(s, s', drv_sid);
    var td_id_val_map2 := result.0;
    var fd_id_val_map2 := result.1;
    var do_id_val_map2 := result.2;

    // Prove commutative diagram
    Lemma_OSDrvWrite_ProveCommutativeDiagram(s, dm, drv_sid, 
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map,
        ts', s');
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_OSDrvWrite_Stub(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true);
    assert WSM_IsSecureOps(s, s');

    (s', true)
}

function OSDrvWrite_ByPIO(
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
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs located at the PIO addr <pio_addr>, and values to be written
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs located at the PIO addr <pio_addr>, and values to be written
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs located at the PIO addr <pio_addr>, and values to be written
             (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==>id !in wsm_td_id_val_map)
        // Requirement: The objects written by the driver must be active in the OS partition, and cannot be hardcoded TDs.
        // This pre-condition reflexes the late access mediation done by MMU
    
    requires var t1:= OSDrvWrite_ByPIO_InnerFunc_Modification1(s, drv_sid, pio_addr, new_v);
             var t_s' := t1.0;
             OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(t_s') &&
             OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(t_s')
        // Requirement: We regard IOMMU perform early memory access mediation, even though it performs late mediation in 
        // fact.
        // Thus, before IOMMU performs mediation in OSDrvWrite, no OS TDs refs any wimp objects and pEHCIs by PIO 
        // addresses and IDs. This is because (1) pEHCIs's objects cannot be referenced by PIO addresses and object IDs, 
        // (2) they cannot reference any hardcoded TDs, (3) they cannot reference any wimp USBPDev's objects, 
        // and (4) other objects for wimp drivers can only be referenced via memory addresses
        // [NOTE] This axiom has been covered in <IOMMU_DevHWProt>

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var t := OSDrvWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
            var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs located at the PIO addr <pio_addr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs located at the PIO addr <pio_addr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs located at the PIO addr <pio_addr>, and values to be written
            result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var t := OSDrvWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
            var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs located at the PIO addr <pio_addr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs located at the PIO addr <pio_addr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs located at the PIO addr <pio_addr>, and values to be written
            var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
            var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
            var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_OSDrvWrite_Stub(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == ws' &&
                WSD_OSDrvWrite_Stub(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_OSDrvWrite in the WK design
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

    var ts'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
    var ts' := s.(objects := ts'_objs);

    // Prove pre-conditions of IOMMU_DevHWProt
    Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(s, ts', os_tds', os_fds', os_dos');
    assert OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(ts');
    Lemma_ValidState_ProveP_WimpObjs_HaveNoPIOAddr(ts');
    assert P_WimpObjs_HaveNoPIOAddr(ts');
    Lemma_ValidState_ProveP_PEHCIsObjs_HaveNoPIOAddr(ts');
    assert P_PEHCIsObjs_HaveNoPIOAddr(ts');

    // Apply IOMMU_DevHWProt
    var s' := IOMMU_DevHWProt(ts');

    // Prove the commutative diagram
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    var result := OSDrvWrite_ProveCommutativeDiagram_GetOpParamsForDesignModel(s, s', drv_sid);
    var td_id_val_map2 := result.0;
    var fd_id_val_map2 := result.1;
    var do_id_val_map2 := result.2;

    // Prove commutative diagram
    Lemma_OSDrvWrite_ProveCommutativeDiagram(s, dm, drv_sid, 
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map,
        ts', s');
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_OSDrvWrite_Stub(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true);
    assert WSM_IsSecureOps(s, s');

    (s', true)
}

function OSDrvWrite_ByObjIDs(
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
    
    requires var t1:= OSDrvWrite_ByObjIDs_InnerFunc_Modification1(s, drv_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
             var t_s' := t1.0;
             OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(t_s') &&
             OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(t_s')
        // Requirement: We regard IOMMU perform early memory access mediation, even though it performs late mediation in 
        // fact.
        // Thus, before IOMMU performs mediation in OSDrvWrite, no OS TDs refs any wimp objects and pEHCIs by PIO 
        // addresses and IDs. This is because (1) pEHCIs's objects cannot be referenced by PIO addresses and object IDs, 
        // (2) they cannot reference any hardcoded TDs, (3) they cannot reference any wimp USBPDev's objects, 
        // and (4) other objects for wimp drivers can only be referenced via memory addresses
        // [NOTE] This axiom has been covered in <IOMMU_DevHWProt>

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
            var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
            var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_OSDrvWrite_Stub(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == ws' &&
                WSD_OSDrvWrite_Stub(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_OSDrvWrite in the WK design
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

    var ts'_objs := s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos');
    var ts' := s.(objects := ts'_objs);

    // Prove pre-conditions of IOMMU_DevHWProt
    Lemma_OSDrvDevWrite_ProveSanityOfNewState_AllExceptSI1(s, ts', os_tds', os_fds', os_dos');
    assert OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(ts');
    Lemma_ValidState_ProveP_WimpObjs_HaveNoPIOAddr(ts');
    assert P_WimpObjs_HaveNoPIOAddr(ts');
    Lemma_ValidState_ProveP_PEHCIsObjs_HaveNoPIOAddr(ts');
    assert P_PEHCIsObjs_HaveNoPIOAddr(ts');

    // Apply IOMMU_DevHWProt
    var s' := IOMMU_DevHWProt(ts');

    // Prove the commutative diagram
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    var result := OSDrvWrite_ProveCommutativeDiagram_GetOpParamsForDesignModel(s, s', drv_sid);
    var td_id_val_map2 := result.0;
    var fd_id_val_map2 := result.1;
    var do_id_val_map2 := result.2;

    // Prove commutative diagram
    Lemma_OSDrvWrite_ProveCommutativeDiagram(s, dm, drv_sid, 
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map,
        ts', s');
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_OSDrvWrite_Stub(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true);
    assert WSM_IsSecureOps(s, s');

    (s', true)
}




/*********************** Operations - OSDev Write ********************/
// I/O access outside WK: Memory write by OS devices
function OSDevWrite_ByPAddr(
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

    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires var dm := WSM_MapState(s);
             DM_IsValidState(dm) && DM_IsSecureState(dm)
        // Pre-conditions needed by <WSD_OSDevWrite_Stub>. These pre-conditions can be proved, but need to be specified here
    requires var t1:= OSDevWrite_ByPAddr_InnerFunc(s, dev_sid, paddr, new_v);
             var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
             var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
             var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
             var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
             var t2 := WSD_OSDevWrite_Stub(WSM_MapState(s), dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
             WSM_MapState(t1.0) == t2.0
        // Requirement: The modifications in this operation maps to the corresponding modifications in the WK design spec

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
            var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
            result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
            var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
            var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
            var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
            var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_RedDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_OSDevWrite_Stub(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == ws' &&
                WSD_OSDevWrite_Stub(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_OSDevWrite in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
    var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
    var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
    var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;

    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    // Prove wsm_*_id_map must be active OS TDs/FDs/DOs in the OS partition
    Lemma_DM_DevWrite_Property(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_OSDevWrite_WriteObjsMustInSystemAndNotHCodedTDs(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    Lemma_OSDevAccess_ObjsToBeAccessedMustBeInOSParition(s, dm, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map));

    Lemma_OSDevWrite_ByPAddr_ProveAccessedObjsAreOSObjects(s, paddr, new_v, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);

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
    Lemma_OSDevWrite_ByPAddr_ProveSanityOfNewState_SI1(s, s', dev_sid, paddr, new_v);

    // Prove commutative diagram
    Lemma_OSDevWrite_ProveCommutativeDiagram(s, dm, dev_sid, 
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map,
        s');
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true);
    assert WSM_IsSecureOps(s, s');

    // Return
    (s', true)
}

function OSDevWrite_ByPIO(
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
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
             WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
        // Requirement: If the OS device writes to a set of TDs/FDs/DOs with some values, then the device must be able  
        // to write the corresponding objects with the corresponding values in the WK design model

    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires var dm := WSM_MapState(s);
             DM_IsValidState(dm) && DM_IsSecureState(dm)
        // Pre-conditions needed by <WSD_OSDevWrite_Stub>. These pre-conditions can be proved, but need to be specified here
    requires var t1:= OSDevWrite_ByPIO_InnerFunc(s, dev_sid, pio_addr, new_v);
             var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
             var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
             var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
             var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
             var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
             var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
             var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
             var t2 := WSD_OSDevWrite_Stub(WSM_MapState(s), dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
             WSM_MapState(t1.0) == t2.0
        // Requirement: The modifications in this operation maps to the corresponding modifications in the WK design spec

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
            var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
            result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
            var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
            var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
            var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
            var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_RedDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_OSDevWrite_Stub(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == ws' &&
                WSD_OSDevWrite_Stub(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_OSDevWrite in the WK design
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

    // Prove wsm_*_id_map must be active OS TDs/FDs/DOs in the OS partition
    Lemma_DM_DevWrite_Property(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_OSDevWrite_WriteObjsMustInSystemAndNotHCodedTDs(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
    Lemma_OSDevAccess_ObjsToBeAccessedMustBeInOSParition(s, dm, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map));

    Lemma_OSDevWrite_ByPIO_ProveAccessedObjsAreOSObjects(s, pio_addr, new_v, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);

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
    Lemma_OSDevWrite_ByPIO_ProveSanityOfNewState_SI1(s, s', dev_sid, pio_addr, new_v);

    // Prove commutative diagram
    Lemma_OSDevWrite_ProveCommutativeDiagram(s, dm, dev_sid, 
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map,
        s');
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true);
    assert WSM_IsSecureOps(s, s');

    // Return
    (s', true)
}

// [NOTE] Needs 60s to verify
function OSNonUSBPDevWrite_ByObjIDs(
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

    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires var dm := WSM_MapState(s);
             DM_IsValidState(dm) && DM_IsSecureState(dm)
        // Pre-conditions needed by <WSD_OSDevWrite_Stub>. These pre-conditions can be proved, but need to be specified here
    requires var t1:= OSNonUSBPDevWrite_ByObjIDs_InnerFunc(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
             var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
             var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
             var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
             var t2 := WSD_OSDevWrite_Stub(WSM_MapState(s), dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
             WSM_MapState(t1.0) == t2.0
        // Requirement: The modifications in this operation maps to the corresponding modifications in the WK design spec

    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
            var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
            var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_RedDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_OSDevWrite_Stub(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == ws' &&
                WSD_OSDevWrite_Stub(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_OSDevWrite in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    // Prove wsm_*_id_map must be active OS TDs/FDs/DOs in the OS partition
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
    Lemma_OSNonUSBPDevWrite_ByObjIDs_ProveSanityOfNewState_SI1(s, s', dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);

    // Prove commutative diagram
    Lemma_OSDevWrite_ProveCommutativeDiagram(s, dm, dev_sid, 
        wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map, td_id_val_map, fd_id_val_map, do_id_val_map,
        s');
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_OSDevWrite_Stub(dm, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true);
    assert WSM_IsSecureOps(s, s');

    // Return
    (s', true)
}




/*********************** Operations - WimpDrv ********************/
// I/O access: Wimp driver reads its DO in physical memory region [read_paddr_start, read_paddr_end), and copies the 
// content to the physical memory region [write_paddr_start, write_paddr_end)
// [NOTE] Because <read_paddr_end> and <write_paddr_end> is excluded, they could be ARCH_WORD_LIMIT. So the type is uint 
// instead of paddr
// [NOTE] Even though [read_paddr_start, read_paddr_end) could be a portion of the wimp driver's DO, this operation
// still maps to DM_GreenDrvReadRead, because the driver reads the DO
function WimpDrvRead_ByPAddr(
    s:state,
    drv_id_word:word,
    read_paddr_start:paddr,
    read_paddr_end:uint
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires drv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
             WSM_IsWimpDrvID(s.subjects, drv_id)
        // Requirement: The wimp driver must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_idword_in_record(globals, drv_id_word)
        // Requirement: The wimp driver must be registered
    requires var globals := wkm_get_globals(s.wk_mstate);
             var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_id.sid) in pids_parse_g_wimp_pids(globals)
        // Requirement: The given wimp driver with the ID <drv_id_word> must be in a wimp partition
    requires var globals := wkm_get_globals(s.wk_mstate);
             var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
             wimpdrv_do_get_paddr_base(globals, drv_slot) <= read_paddr_start < read_paddr_end <= wimpdrv_do_get_paddr_end(globals, drv_slot)
        // Requirement: The accessing physical memory must be inside the physical memory range of the wimp driver's DO
        
    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_id.sid, {}, {}, {wimpdrv_do_id})
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
            var read_objs := {wimpdrv_do_id.oid};
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_GreenDrvRead_PreConditions(ws, drv_id.sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_GreenDrvRead_InnerFunc(ws, drv_id.sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_RedDrvRead in the WK design
{
    // Prove only the wimp driver's DO is accessed
    var globals := wkm_get_globals(s.wk_mstate);
    var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
    Lemma_WimpDrvReadWriteObjs_ByPAddr_ProveFlagIsCompleteAndRecordedPIDIsNotInvalid(s, drv_id_word);
    Lemma_WimpDrvReadWriteObjs_ByPAddr_ProveAccessOwnDO(s, drv_slot, read_paddr_start, read_paddr_end);
    Lemma_subjects_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs(s, drv_slot, read_paddr_start, read_paddr_end);

    var s' := s;
    var d := true;

    var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
    var read_objs := {wimpdrv_do_id.oid};
    assert wimpdrv_do_id in WSM_AllDOIDs(s.objects);
    Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, drv_id.sid, wimpdrv_do_id.oid);
    assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_id.sid) == 
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_do_id.oid);
    assert WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_id.sid, {}, {}, {wimpdrv_do_id});

    // Prove commutative diagram
    var dm := WSM_MapSecureState(s);
    Lemma_WimpDrvRead_ProveCommutativeDiagram(s, dm, drv_id, {}, {}, {wimpdrv_do_id});
    Lemma_WimpDrvRead_ByPAddr_EquivilantReadObjs(wimpdrv_do_id);
    assert read_objs == TDIDsToObjIDs({}) + FDIDsToObjIDs({}) + DOIDsToObjIDs({wimpdrv_do_id});

    // Return
    (s', d)
}

// I/O access: Wimp driver writes its DO in physical memory
function WimpDrvWrite_ByPAddr(
    s:state,
    drv_id_word:word,
    paddr_start:paddr,
    paddr_end:uint,
    new_val:string
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires drv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
             WSM_IsWimpDrvID(s.subjects, drv_id)
        // Requirement: The wimp driver must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_idword_in_record(globals, drv_id_word)
        // Requirement: The wimp driver must be registered
    requires var globals := wkm_get_globals(s.wk_mstate);
             var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_id.sid) in pids_parse_g_wimp_pids(globals)
        // Requirement: The given wimp driver with the ID <drv_id_word> must be in a wimp partition
    requires var globals := wkm_get_globals(s.wk_mstate);
             var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
             wimpdrv_do_get_paddr_base(globals, drv_slot) <= paddr_start < paddr_end <= wimpdrv_do_get_paddr_end(globals, drv_slot)
        // Requirement: The accessing physical memory must be inside the physical memory range of the wimp driver's DO
        
    ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
            result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_id.sid, {}, {}, {wimpdrv_do_id})
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
            var new_do_val:DO_Val := wimpdrv_write_do_get_do_val(s, drv_id_word, paddr_start, paddr_end, new_val);
            var do_id_val_map:map<DO_ID, DO_Val> := map[wimpdrv_do_id := new_do_val];
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_GreenDrvWrite_PreConditions(ws, drv_id.sid, map[], map[], do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_WimpDrvWrite_Stub(ws, drv_id.sid, map[], map[], do_id_val_map).0 == ws' &&
                WSD_WimpDrvWrite_Stub(ws, drv_id.sid, map[], map[], do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_WimpDrvWrite in the WK design
{
    var dm:DM_State := WSM_MapSecureState(s);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    // Prove only the wimp driver's DO is accessed
    var globals := wkm_get_globals(s.wk_mstate);
    var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
    Lemma_WimpDrvReadWriteObjs_ByPAddr_ProveFlagIsCompleteAndRecordedPIDIsNotInvalid(s, drv_id_word);
    Lemma_WimpDrvReadWriteObjs_ByPAddr_ProveAccessOwnDO(s, drv_slot, paddr_start, paddr_end);
    Lemma_subjects_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs(s, drv_slot, paddr_start, paddr_end);

    // Implementation
    var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
    var new_do_val:DO_Val := wimpdrv_write_do_get_do_val(s, drv_id_word, paddr_start, paddr_end, new_val);

    var do_id_val_map:map<DO_ID, DO_Val> := map[wimpdrv_do_id := new_do_val];
    var new_wimpdrv_dos := WSM_WriteDOsVals(s.objects.wimpdrv_dos, do_id_val_map);

    // This operation is always allowed, because the accessing [paddr_start, paddr_end) is inside the physical memory 
    // range of the wimp driver's DO
    var s' := s.(objects := s.objects.(wimpdrv_dos := new_wimpdrv_dos));
    var d := true;

    // Prove WK_ValidObjs(s'.subjects, s'.objects)
    Lemma_WimpDrvDOUpdate_ProveSanityOfNewState(s, s', new_wimpdrv_dos);
    assert InstSaneState(s');

    // Prove OpsSaneStateSubset(s')
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s, s');
    assert OpsSaneStateSubset(s');

    // Prove commutative diagram
    Lemma_WimpDrvWrite_ProveWimpDrvAndItsDOInSamePartition(s, drv_id.sid, wimpdrv_do_id.oid);
    assert WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_id.sid, {}, {}, {wimpdrv_do_id});
    Lemma_WimpDrvWriteOwnDO_ProveCommutativeDiagram(s, dm, drv_id.sid, do_id_val_map, s');

    // Return
    (s', d)
}

// I/O access: USB peripheral device writes its objects
function USBPDevWrite_ByObjID(
    s:state,
    usbpdev_addr:USBPDev_Addr,
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(addr) &&
             usbpdev_addr != usb_parse_usbpdev_addr(addr)
        // Requirement: The USBPDev must be located at a non-empty address
    requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
             WSM_IsUSBPDevID(s.subjects, dev_id)
        // Requirement: The USB peripheral device must exist in the system
    requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
            // Requirement: the device must be active

    requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
             WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, map[], fd_id_val_map, do_id_val_map)
        // Requirement: If a USBPDev writes to a set of FDs/DOs with some values, then the device must be able to write 
        // the corresponding objects with the corresponding values in the WK design model

	requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
			 forall fd_id2 :: fd_id2 in fd_id_val_map
				==> fd_id2 in s.subjects.usbpdevs[dev_id].fd_ids
	requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
			 forall do_id2 :: do_id2 in do_id_val_map
				==> do_id2 in s.subjects.usbpdevs[dev_id].do_ids
		// Requirement: The USBPDev owns the objects to be accessed
        // [TODO] This requirement can be proven

	ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var td_id_val_map:map<TD_ID, TD_Val> := map[];
            var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map))
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var td_id_val_map:map<TD_ID, TD_Val> := map[];
            var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_DevWrite_PreConditions(ws, dev_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_DevWrite_Stub(ws, dev_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == ws' &&
                WSD_DevWrite_Stub(ws, dev_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_OSDevWrite in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

	reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
	
	// Implementation
	var new_usbpdevs_fds := WSM_WriteFDsVals(s.objects.usbpdev_fds, fd_id_val_map);
	var new_usbpdevs_dos := WSM_WriteDOsVals(s.objects.usbpdev_dos, do_id_val_map);

	// In this operation, USB peripheral devices can only modify its own objects
    var s' := s.(objects := s.objects.(usbpdev_fds := new_usbpdevs_fds, usbpdev_dos := new_usbpdevs_dos));
    var d := true;

    var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
    Lemma_USBPDevAccess_ProveSubjAndItsObjsInSamePartition(s, dev_id.sid, MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map));
    assert WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {}, MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map));
    var td_id_val_map:map<TD_ID, TD_Val> := map[];
    Lemma_MapGetKeys_EmptyMap(td_id_val_map);
    assert WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map));

    // Prove InstSaneState(s')
    Lemma_USBPDevObjsUpdate_ProveSanityOfNewState(s, s', new_usbpdevs_fds, new_usbpdevs_dos);
    assert InstSaneState(s');

    // Prove OpsSaneStateSubset(s')
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s, s');
    assert OpsSaneStateSubset(s');

    // Prove commutative diagram
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    Lemma_USBPDevWrite_ProveCommutativeDiagram(s, dm, dev_id.sid, fd_id_val_map, do_id_val_map, s');

    // Return
    (s', d)
}

// I/O access: USB peripheral device writes its objects
function USBPDevRead_ByObjID(
    s:state,
    usbpdev_addr:USBPDev_Addr,
    read_fds:set<FD_ID>,
    read_dos:set<DO_ID>
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(addr) &&
             usbpdev_addr != usb_parse_usbpdev_addr(addr)
        // Requirement: The USBPDev must be located at a non-empty address 
    requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
             WSM_IsUSBPDevID(s.subjects, dev_id)
        // Requirement: The USB peripheral device must exist in the system
    requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
            // Requirement: the device must be active

    requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
             WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, {}, read_fds, read_dos)
        // Requirement: If the device reads a set of TDs/FDs/DOs, then the device must be able to read the 
        // corresponding objects in the WK design model

	requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
			 forall fd_id2 :: fd_id2 in read_fds
				==> fd_id2 in s.subjects.usbpdevs[dev_id].fd_ids
	requires var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
			 forall do_id2 :: do_id2 in read_dos
				==> do_id2 in s.subjects.usbpdevs[dev_id].do_ids
		// Requirement: The USBPDev owns the objects to be accessed

	ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {}, read_fds, read_dos)
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            var read_objs := FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_DevRead_PreConditions(ws, dev_id.sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_DevRead_InnerFunc(ws, dev_id.sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_DevRead in the WK design
{
	var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    // Prove read_* must be active OS TDs/FDs/DOs in the OS partition
    var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
    var dev_sid := dev_id.sid;
    Lemma_SaneWSMState_MapSubjNonNULLPID(s, dm, dev_sid);
    assert DM_SubjPID(dm.subjects, dev_sid) != NULL;
    Lemma_DM_DevRead_Properties(dm, dev_sid, {}, read_fds, read_dos);

    Lemma_USBPDevAccess_ProveSubjAndItsObjsInSamePartition(s, dev_id.sid, read_fds, read_dos);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, {}, read_fds, read_dos);

    // Prove commutative diagram
    Lemma_DevRead_ProveCommutativeDiagram(s, dm, dev_sid, {}, read_fds, read_dos);
    var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
    assert DM_DevRead_PreConditions(dm, dev_sid, read_objs, map[], map[], map[]);
    assert DM_DevRead_InnerFunc(dm, dev_sid, read_objs, map[], map[], map[]) == (dm, true);
    Lemma_USBPDevRead_ByObjID_Summary(dm, dev_sid, read_fds, read_dos);

    (s, true)
}




/*********************** Operations - eEHCIs ********************/
// I/O access: eEHCI writes its objects
function EEHCIWriteOwnDO_ByOffset(
    s:state,
    eehci_id_word:word,
    eehci_slot:word,
    offset:uint32,
    new_val:word
) : (result:(state, bool))
    requires OpsSaneState(s)
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

	ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var t_write_params := WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(s, eehci_id_word, dev_id, offset, new_val);
            result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, MapGetKeys(t_write_params.0), MapGetKeys(t_write_params.1), MapGetKeys(t_write_params.2))
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var t_write_params := WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(s, eehci_id_word, dev_id, offset, new_val);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_GreenDevWrite_PreConditions(ws, dev_id.sid, t_write_params.0, t_write_params.1, t_write_params.2)) &&
            (result.1 == true ==> 
                (WSD_WimpDevWrite_Stub(ws, dev_id.sid, t_write_params.0, t_write_params.1, t_write_params.2).0 == ws' &&
                WSD_WimpDevWrite_Stub(ws, dev_id.sid, t_write_params.0, t_write_params.1, t_write_params.2).1 == true))
        // Property: Commutative diagram to WSD_OSDevWrite in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    // Implementation
    var old_globals := wkm_get_globals(s.wk_mstate);
    var new_globals := eehci_mem_set_status_reg(old_globals, eehci_slot, new_val);

    // This operation is always allowed, see the abstract I/O model
    var s' := s.(wk_mstate := s.wk_mstate.(globals := new_globals));
    var d := true;

    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    var t_write_params := WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(s, eehci_id_word, dev_id, offset, new_val);
    Lemma_EEHCIAccessOwnObjs_ProveSubjAndItsObjsInSamePartition(s, dev_id.sid, MapGetKeys(t_write_params.2));
    Lemma_MapGetKeys_EmptyMap(t_write_params.0);
    Lemma_MapGetKeys_EmptyMap(t_write_params.1);

    // Prove InstSaneState(s')
    Lemma_EEHCIWriteStatusReg_ProveSanityOfNewState(s, s', eehci_slot, new_val);
    assert InstSaneState(s');

    // Prove OpsSaneStateSubset(s')
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s, s');
    assert OpsSaneStateSubset(s');

    // Prove commutative diagram
    
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    Lemma_EEHCIWriteWriteOwnDO_ProveCommutativeDiagram(s, dm, eehci_id_word, eehci_slot, offset, new_val, s');

    // Return
    (s', d)
}

// I/O access: eEHCI reads its objects
function EEHCIReadOwnObjs_ByOffset(
    s:state,
    eehci_id_word:word,
    eehci_slot:word,
    offset:uint32
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI
    requires offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset || offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset ||
             offset == G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset || offset == G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset ||
             offset in eehci_usbtd_regs_offsets()
        // Requirement: eEHCIs can only read these registers among all fields in <g_eehci_mem>

    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             var t_read_objs := WSM_EEHCIRead_OwnRegsToIDs(s, eehci_id_word, dev_id, offset);
             WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, t_read_objs.0, t_read_objs.1, t_read_objs.2)
        // Requirement: If the device reads a set of TDs/FDs/DOs, then the device must be able to read the 
        // corresponding objects in the WK design model

	ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var t_read_objs := WSM_EEHCIRead_OwnRegsToIDs(s, eehci_id_word, dev_id, offset);
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, t_read_objs.0, t_read_objs.1, t_read_objs.2)
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var t_read_objs := WSM_EEHCIRead_OwnRegsToIDs(s, eehci_id_word, dev_id, offset);
            var read_objs := TDIDsToObjIDs(t_read_objs.0) + FDIDsToObjIDs(t_read_objs.1) + DOIDsToObjIDs(t_read_objs.2);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_DevRead_PreConditions(ws, dev_id.sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_DevRead_InnerFunc(ws, dev_id.sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_DevRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    // Prove read_* must be active OS TDs/FDs/DOs in the OS partition
    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    var dev_sid := dev_id.sid;
    
    var t_read_objs := WSM_EEHCIRead_OwnRegsToIDs(s, eehci_id_word, dev_id, offset);
    var read_tds := t_read_objs.0;
    var read_fds := t_read_objs.1;
    var read_dos := t_read_objs.2;

    Lemma_SaneWSMState_MapSubjNonNULLPID(s, dm, dev_sid);
    assert DM_SubjPID(dm.subjects, dev_sid) != NULL;
    Lemma_DM_DevRead_Properties(dm, dev_sid, read_tds, read_fds, read_dos);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, read_tds, read_fds, read_dos);
    Lemma_DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition_ImpliesWS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dm, dev_sid, read_tds, read_fds, read_dos);

    // Prove commutative diagram
    Lemma_DevRead_ProveCommutativeDiagram(s, dm, dev_sid, read_tds, read_fds, read_dos);

    (s, true)
}

// I/O access: eEHCI reads a USB TD and loads the transfers in it
function EEHCIReadUSBTD_BySlotID(
    s:state,
    eehci_id_word:word,
    eehci_slot:word,
    usbtd_slot:word
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI
    requires usbtd_slot != USBTD_SlotID_INVALID
        // Requirement: eEHCIs never access a USB TD with USBTD_SlotID_INVALID as the slot id
    requires var globals := wkm_get_globals(s.wk_mstate);
             CanActiveEEHCIReadUSBTD(globals, eehci_slot, usbtd_slot)

	ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures usbtd_map_valid_slot_id(usbtd_slot)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            isUInt32(USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            TestBit(usbtd_map_get_flags(globals, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
    ensures var globals := wkm_get_globals(s.wk_mstate);
             usbtd_map_get_pid(globals, usbtd_slot) != WS_PartitionID(PID_INVALID)
        // Properties needed by the following properties
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var td_id := EEHCIReadUSBTD_CanActiveEEHCIReadUSBTD_Property(s, eehci_id_word, eehci_slot,usbtd_slot);
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {td_id}, {}, {})
        // Property: If return true, then the subject and objects being accessed must be in the same partition
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var td_id := EEHCIReadUSBTD_CanActiveEEHCIReadUSBTD_Property(s, eehci_id_word, eehci_slot,usbtd_slot);
            var read_objs := TDIDsToObjIDs({td_id}) + FDIDsToObjIDs({}) + DOIDsToObjIDs({});
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_DevRead_PreConditions(ws, dev_id.sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_DevRead_InnerFunc(ws, dev_id.sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_DevRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var globals := wkm_get_globals(s.wk_mstate);
    Lemma_CanActiveEEHCIReadUSBTD_ProveProperty(globals, eehci_slot, usbtd_slot);

    // Prove read_* must be active OS TDs/FDs/DOs in the OS partition
    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    var dev_sid := dev_id.sid;
    
    var td_id := EEHCIReadUSBTD_CanActiveEEHCIReadUSBTD_Property(s, eehci_id_word, eehci_slot,usbtd_slot);
    var read_tds := {td_id};
    var read_fds := {};
    var read_dos := {};

    Lemma_SaneWSMState_MapSubjNonNULLPID(s, dm, dev_sid);
    assert DM_SubjPID(dm.subjects, dev_sid) != NULL;
    Lemma_DM_DevRead_Properties(dm, dev_sid, read_tds, read_fds, read_dos);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, read_tds, read_fds, read_dos);

    // Prove commutative diagram
    Lemma_DevRead_ProveCommutativeDiagram(s, dm, dev_sid, read_tds, read_fds, read_dos);

    (s, true)
}

// I/O access: eEHCI reads USB peripheral devices' objects by IDs
function EEHCIReadUSBPDevObj_ByObjID(
    s:state,
    eehci_id_word:word,
    eehci_slot:word,
    fd_ids:set<FD_ID>,
    do_ids:set<DO_ID>
) : (result:(state, bool))
    requires OpsSaneState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI
    requires forall id :: id in fd_ids
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD(s, eehci_slot, id)
    requires forall id :: id in do_ids
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DO(s, eehci_slot, id)
        // Requirement: The access must be defined

	ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {}, fd_ids, do_ids)
        // Property: If return true, then the subject and objects being accessed must be in the same partition

    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_DevRead_PreConditions(ws, dev_id.sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_DevRead_InnerFunc(ws, dev_id.sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_DevRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    EEHCIReadUSBPDev_EEHCIAccessUSBPDevObj_ByObjID_Property(s, eehci_id_word, eehci_slot, fd_ids, do_ids);

    // Prove read_* must be active OS TDs/FDs/DOs in the OS partition
    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    var dev_sid := dev_id.sid;
    
    var read_tds := {};
    var read_fds := fd_ids;
    var read_dos := do_ids;

    Lemma_SaneWSMState_MapSubjNonNULLPID(s, dm, dev_sid);
    assert DM_SubjPID(dm.subjects, dev_sid) != NULL;
    Lemma_DM_DevRead_Properties(dm, dev_sid, read_tds, read_fds, read_dos);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, read_tds, read_fds, read_dos);
    Lemma_DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition_ImpliesWS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dm, dev_sid, read_tds, read_fds, read_dos);
    assert WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, read_tds, fd_ids, do_ids);

    // Prove commutative diagram
    Lemma_DevRead_ProveCommutativeDiagram(s, dm, dev_sid, read_tds, read_fds, read_dos);

    (s, true)
}

// I/O access: eEHCI writes USB peripheral devices' objects by IDs
// [NOTE] Needs 80s to verify
function EEHCIWriteUSBPDevObj_ByObjID(
    s:state,
    eehci_id_word:word,
    eehci_slot:word,
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(state, bool))
    requires OpsSaneState(s)
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

    requires forall id :: id in fd_id_val_map
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD(s, eehci_slot, id)
    requires forall id :: id in do_id_val_map
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DO(s, eehci_slot, id)
        // Requirement: The access must be defined
    requires forall id :: id in fd_id_val_map
                ==> fd_id_val_map[id].v in usbpdev_string_range_for_fds_dos(s.subjects, EEHCIAccessUSBPDevObj_GetTargetUSBPDevID(s, id.oid), id.oid)
    requires forall id :: id in do_id_val_map
                ==> do_id_val_map[id].v in usbpdev_string_range_for_fds_dos(s.subjects, EEHCIAccessUSBPDevObj_GetTargetUSBPDevID(s, id.oid), id.oid)
        // Requirement: Writting values must be within the value ranges of these objects

	ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var td_id_val_map:map<TD_ID, TD_Val> := map[];
            var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_GreenDevWrite_PreConditions(ws, dev_id.sid, map[], fd_id_val_map, do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_WimpDevWrite_Stub(ws, dev_id.sid, map[], fd_id_val_map, do_id_val_map).0 == ws' &&
                WSD_WimpDevWrite_Stub(ws, dev_id.sid, map[], fd_id_val_map, do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_OSDevWrite in the WK design

    ensures var td_id_val_map:map<TD_ID, TD_Val> := map[];
            var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map))
        // Property: If return true, then the subject and objects being accessed must be in the same partition
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    EEHCIWriteUSBPDevObj_ByObjID_Property(s, eehci_id_word, eehci_slot, fd_id_val_map, do_id_val_map);

    // Prove *_id_map must be active TDs/FDs/DOs in the wimp partition
    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    Lemma_SaneWSMState_MapSubjGreenPID(s, dm, dev_id.sid);
    Lemma_DM_DevWrite_Property(dm, dev_id.sid, map[], fd_id_val_map, do_id_val_map);
    
    // Implementation
    Lemma_EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FDs_Property(s, eehci_slot, MapGetKeys(fd_id_val_map));
    Lemma_EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DOs_Property(s, eehci_slot, MapGetKeys(do_id_val_map));
	var new_usbpdevs_fds := WSM_WriteFDsVals(s.objects.usbpdev_fds, fd_id_val_map);
	var new_usbpdevs_dos := WSM_WriteDOsVals(s.objects.usbpdev_dos, do_id_val_map);

	// This operation is always allowed, see the abstract I/O model
    var s' := s.(objects := s.objects.(usbpdev_fds := new_usbpdevs_fds, usbpdev_dos := new_usbpdevs_dos));
    var d := true;

    var td_id_val_map:map<TD_ID, TD_Val> := map[];
    Lemma_MapGetKeys_EmptyMap(td_id_val_map);
    Lemma_DM_SubjAndWriteObjInSamePartition_ImpliesWS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dm, dev_id.sid, 
        MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map));
    assert WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map));

    // Prove InstSaneState(s')
    Lemma_USBPDevObjsUpdate_ProveSanityOfNewState(s, s', new_usbpdevs_fds, new_usbpdevs_dos);
    assert InstSaneState(s');

    // Prove OpsSaneStateSubset(s')
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s, s');
    assert OpsSaneStateSubset(s');

    // Prove commutative diagram
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    Lemma_EEHCIWriteUSBPDev_ProveP_EEHCIWriteUSBPDevObjs(s, dm, dev_id, fd_id_val_map, do_id_val_map);
    Lemma_EEHCIWriteUSBPDevObjs_ProveCommutativeDiagram(s, dm, eehci_id_word, eehci_slot, fd_id_val_map, do_id_val_map, s');

    // Return
    (s', d)
}

// I/O access: eEHCI reads the physical memory region [read_paddr_start, read_paddr_end) of the WimpDrv's DO 
function EEHCIReadObjs_ByPAddr(
    s:state,
    eehci_id_word:word,
    eehci_slot:word,
    read_paddr_start:paddr,
    read_paddr_end:uint // Because <read_paddr_end> is excluded, it could be ARCH_WORD_LIMIT. So the type is uint 
                        // instead of paddr
) : (result:(state, bool, word)) // result.2 is (wimpdrv_slot:word)
    requires OpsSaneState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI
    requires read_paddr_start < read_paddr_end
    requires EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer(s, eehci_slot, read_paddr_start, read_paddr_end)
        // Requirement: The access must be defined

	ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures var wimpdrv_slot := result.2;
            wimpdrv_valid_slot_id(wimpdrv_slot) &&
            wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, read_paddr_start, read_paddr_end)
    ensures var wimpdrv_slot := result.2;
            var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
            WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
        // Property needed by the following properties
    ensures var wimpdrv_slot := result.2;
            var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            result.1 == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {}, {}, {wimpdrv_do_id})
        // Property: If return true, then the subject and objects being accessed must be in the same partition
    ensures var wimpdrv_slot := result.2;
            var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs({}) + DOIDsToObjIDs({wimpdrv_do_id});
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_DevRead_PreConditions(ws, dev_id.sid, read_objs, map[], map[], map[])) &&
            (result.1 == true ==> 
                DM_DevRead_InnerFunc(ws, dev_id.sid, read_objs, map[], map[], map[]) == (ws', true))
        // Property: Commutative diagram to DM_DevRead in the WK design
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    // Prove only the wimp driver's DO is accessed
    var globals := wkm_get_globals(s.wk_mstate);
    Lemma_EEHCIReadWriteObjs_ByPAddr_ProveAccessWimpDrvDOsInSamePartitionOnly_ShowExistence(s, eehci_slot, read_paddr_start, read_paddr_end);
    var wimpdrv_slot:word :| wimpdrv_valid_slot_id(wimpdrv_slot) &&
                wimpdrv_DO_include_mem_region(globals, wimpdrv_slot, read_paddr_start, read_paddr_end) &&
                wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot);
    Lemma_wimpdrv_registed_and_active_must_exist_in_system(s, wimpdrv_slot);
    Lemma_subjects_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs(s, wimpdrv_slot, read_paddr_start, read_paddr_end);

    EEHCIReadWimpDrvDO_EEHCIAccessObjs_ByPAddr_Property(s, eehci_id_word, eehci_slot, read_paddr_start, read_paddr_end, wimpdrv_slot);

    // Prove read_* must be active OS TDs/FDs/DOs in the OS partition
    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    var dev_sid := dev_id.sid;
    
    var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
    var read_tds := {};
    var read_fds := {};
    var read_dos := {wimpdrv_do_id};

    Lemma_SaneWSMState_MapSubjNonNULLPID(s, dm, dev_sid);
    assert DM_SubjPID(dm.subjects, dev_sid) != NULL;
    Lemma_DM_DevRead_Properties(dm, dev_sid, read_tds, read_fds, read_dos);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    assert P_DMSubjectsHasUniqueIDs(dm.subjects);
    assert P_DMObjectsHasUniqueIDs(dm.objects);
    assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, dev_sid, read_tds, read_fds, read_dos);
    Lemma_DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition_ImpliesWS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dm, dev_sid, read_tds, read_fds, read_dos);

    // Prove commutative diagram
    Lemma_DevRead_ProveCommutativeDiagram(s, dm, dev_sid, read_tds, read_fds, read_dos);

    // Return
    (s, true, wimpdrv_slot)
}

// I/O access: eEHCI writes the physical memory region [write_paddr_start, write_paddr_end) of the WimpDrv's DO 
function EEHCIWriteObjs_ByPAddr(
    s:state,
    eehci_id_word:word,
    eehci_slot:word,
    write_paddr_start:paddr,
    write_paddr_end:uint, // Because <write_paddr_end> is excluded, it could be ARCH_WORD_LIMIT. So the type is uint 
                        // instead of paddr
    new_val:string
) : (result:(state, bool, word)) // result.2 is the accessed wimp driver's ID word
    requires OpsSaneState(s)
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
    requires write_paddr_start < write_paddr_end
    requires EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer(s, eehci_slot, write_paddr_start, write_paddr_end)
        // Requirement: The access must be defined

	ensures var s' := result.0;
            OpsSaneState(s')

    ensures var s' := result.0;
            WSM_IsSecureOps(s, s')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var wimpdrv_idword:word := result.2;
            wimpdrv_idword_in_record(wkm_get_globals(s.wk_mstate), wimpdrv_idword) &&
            (wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY) 
    ensures var wimpdrv_idword:word := result.2;
            WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword) in s.subjects.wimp_drvs
    ensures var wimpdrv_idword:word := result.2;
            var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := wimpdrv_get_slot_by_idword(globals, wimpdrv_idword);
            wimpdrv_do_get_paddr_base(globals, drv_slot) <= write_paddr_start < write_paddr_end <= wimpdrv_do_get_paddr_end(globals, drv_slot)
        // Properties needed by the following properties
    ensures var wimpdrv_idword:word := result.2;
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var new_do_val:DO_Val := wimpdrv_write_do_get_do_val(s, wimpdrv_idword, write_paddr_start, write_paddr_end, new_val);
            var do_id_val_map := map[wimpdrv_do_id := new_do_val];
            var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var ws := WSM_MapSecureState(s);
            var ws' := WSM_MapSecureState(result.0);
            (result.1 == true ==> DM_GreenDevWrite_PreConditions(ws, dev_id.sid, map[], map[], do_id_val_map)) &&
            (result.1 == true ==> 
                (WSD_WimpDevWrite_Stub(ws, dev_id.sid, map[], map[], do_id_val_map).0 == ws' &&
                WSD_WimpDevWrite_Stub(ws, dev_id.sid, map[], map[], do_id_val_map).1 == true))
        // Property: Commutative diagram to WSD_OSDevWrite in the WK design
    ensures var wimpdrv_idword:word := result.2;
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var new_do_val:DO_Val := wimpdrv_write_do_get_do_val(s, wimpdrv_idword, write_paddr_start, write_paddr_end, new_val);
            var do_id_val_map := map[wimpdrv_do_id := new_do_val];
            var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            result.1 == true
                ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {}, {}, MapGetKeys(do_id_val_map))
        // Property: If return true, then the subject and objects being accessed must be in the same partition
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);
    var globals := wkm_get_globals(s.wk_mstate);

    // Prove only the wimp driver's DO is accessed
    Lemma_EEHCIReadWriteObjs_ByPAddr_ProveAccessWimpDrvDOsInSamePartitionOnly_ShowExistence(s, eehci_slot, write_paddr_start, write_paddr_end);
    var wimpdrv_slot:word :| wimpdrv_valid_slot_id(wimpdrv_slot) &&
                wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, write_paddr_start, write_paddr_end) &&
                wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot);
    Lemma_wimpdrv_registed_and_active_must_exist_in_system(s, wimpdrv_slot);
    Lemma_subjects_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs(s, wimpdrv_slot, write_paddr_start, write_paddr_end);

    // Implementation
    var drv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
    var new_do_val:DO_Val := wimpdrv_write_do_get_do_val(s, drv_id_word, write_paddr_start, write_paddr_end, new_val);

    var do_id_val_map:map<DO_ID, DO_Val> := map[wimpdrv_do_id := new_do_val];
    var new_wimpdrv_dos := WSM_WriteDOsVals(s.objects.wimpdrv_dos, do_id_val_map);

    // This operation is always allowed, see the abstract I/O model
    var s' := s.(objects := s.objects.(wimpdrv_dos := new_wimpdrv_dos));
    var d := true;

    EEHCIWriteWimpDrvDO_ByPAddr_Property(s, eehci_id_word, eehci_slot, wimpdrv_slot, write_paddr_start, write_paddr_end, new_val);

    // Prove *_id_map must be active TDs/FDs/DOs in the wimp partition
    var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
    Lemma_SaneWSMState_MapSubjGreenPID(s, dm, dev_id.sid);
    Lemma_DM_DevWrite_Property(dm, dev_id.sid, map[], map[], do_id_val_map);

    var td_id_val_map:map<TD_ID, TD_Val> := map[];
    var fd_id_val_map:map<FD_ID, FD_Val> := map[];
    Lemma_MapGetKeys_EmptyMap(td_id_val_map);
    Lemma_MapGetKeys_EmptyMap(fd_id_val_map);
    Lemma_DM_SubjAndWriteObjInSamePartition_ImpliesWS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dm, dev_id.sid, 
        MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map));
    assert WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map));

    // Prove WK_ValidObjs(s'.subjects, s'.objects)
    Lemma_WimpDrvDOUpdate_ProveSanityOfNewState(s, s', new_wimpdrv_dos);
    assert InstSaneState(s');

    // Prove OpsSaneStateSubset(s')
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
    Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s, s');
    assert OpsSaneStateSubset(s');

    // Prove commutative diagram
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    Lemma_EEHCIWriteWimpDrvDO_ProveP_EEHCIWriteWimpDrvDO(s, dm, dev_id, do_id_val_map);
    Lemma_EEHCIWriteWimpDrvDO_ProveCommutativeDiagram(s, dm, eehci_id_word, eehci_slot, do_id_val_map, s');

    // Return
    (s', d, drv_id_word)
}




/*********************** Private Lemmas ********************/
lemma Lemma_DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition_ImpliesWS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(
    s:state, dm:DM_State, 
    s_id:Subject_ID, 
    read_tds:set<TD_ID>,
    read_fds:set<FD_ID>, 
    read_dos:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    
    requires DM_IsSubjID(dm.subjects, s_id)
    
    requires (forall td_id :: td_id in read_tds ==> td_id in AllTDIDs(dm.objects)) &&
             (forall fd_id :: fd_id in read_fds ==> fd_id in AllFDIDs(dm.objects)) &&
             (forall do_id :: do_id in read_dos ==> do_id in AllDOIDs(dm.objects))
        // Requirement: Driver only write existing objects

    requires DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, s_id, read_tds, read_fds, read_dos)

    ensures WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, s_id, read_tds, read_fds, read_dos)
{
    var globals := wkm_get_globals(s.wk_mstate);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    forall id | id in read_tds
        ensures WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
    {
        assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id)) == SubjPID_SlimState(dm.subjects, s_id);
        assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) == ObjPID_KObjects(dm.objects, id.oid);
    }
}

lemma Lemma_DM_SubjAndWriteObjInSamePartition_ImpliesWS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(
    s:state, dm:DM_State, 
    s_id:Subject_ID, 
    write_tds:set<TD_ID>,
    write_fds:set<FD_ID>, 
    write_dos:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    
    requires DM_IsSubjID(dm.subjects, s_id)
    
    requires write_tds <= DM_AllTDIDs(dm.objects)
    requires write_fds <= DM_AllFDIDs(dm.objects)
    requires write_dos <= DM_AllDOIDs(dm.objects)

    requires forall id :: id in write_tds
                ==> id.oid in AllObjsIDs(dm.objects) &&
                    ObjPID_KObjects(dm.objects, id.oid) == SubjPID_SlimState(dm.subjects, s_id)
    requires forall id :: id in write_fds
                ==> id.oid in AllObjsIDs(dm.objects) &&
                    ObjPID_KObjects(dm.objects, id.oid) == SubjPID_SlimState(dm.subjects, s_id)
    requires forall id :: id in write_dos
                ==> id.oid in AllObjsIDs(dm.objects) &&
                    ObjPID_KObjects(dm.objects, id.oid) == SubjPID_SlimState(dm.subjects, s_id)
        // Requirement: Subject and objects are in the same partition in the WK design

    ensures (forall td_id :: td_id in write_tds ==> td_id in WSM_AllTDIDs(s.objects)) &&
            (forall fd_id :: fd_id in write_fds ==> fd_id in WSM_AllFDIDs(s.objects)) &&
            (forall do_id :: do_id in write_dos ==> do_id in WSM_AllDOIDs(s.objects))
    ensures WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, s_id, write_tds, write_fds, write_dos)
{
    var globals := wkm_get_globals(s.wk_mstate);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    forall id | id in write_tds
        ensures WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
    {
        assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id)) == SubjPID_SlimState(dm.subjects, s_id);
        assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) == ObjPID_KObjects(dm.objects, id.oid);
    }
}