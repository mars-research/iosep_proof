include "DM_AdditionalPredicates.s.dfy"

function method DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(
    ws:DM_State, 
    s_id:Subject_ID, 
    read_tds:set<TD_ID>,
    read_fds:set<FD_ID>, 
    read_dos:set<DO_ID>
) : bool
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    
    requires DM_IsSubjID(ws.subjects, s_id)
    
    requires (forall td_id :: td_id in read_tds ==> td_id in AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in read_fds ==> fd_id in AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in read_dos ==> do_id in AllDOIDs(ws.objects))
        // Requirement: Driver only write existing objects
{
    (forall id :: id in read_tds
        ==> DM_SubjPID(ws.subjects, s_id) == DM_ObjPID(ws.objects, id.oid)) &&
    (forall id :: id in read_fds
        ==> DM_SubjPID(ws.subjects, s_id) == DM_ObjPID(ws.objects, id.oid)) &&
    (forall id :: id in read_dos
        ==> DM_SubjPID(ws.subjects, s_id) == DM_ObjPID(ws.objects, id.oid))
}

lemma Lemma_TDFDDOIDsToObjIDs_Sum_Property(td_id:TD_ID, fd_id:FD_ID, do_id:DO_ID, o_id:Object_ID)
    requires o_id in (TDIDsToObjIDs({td_id}) + FDIDsToObjIDs({fd_id}) + DOIDsToObjIDs({do_id}))

    ensures TD_ID(o_id) == td_id || FD_ID(o_id) == fd_id || DO_ID(o_id) == do_id
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_DevWrite_Property(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_sid, td_id2, td_id_val_map[td_id2])
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(ws, dev_sid, fd_id2, fd_id_val_map[fd_id2])
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(ws, dev_sid, do_id2, do_id_val_map[do_id2])

    ensures forall id :: id in td_id_val_map
                ==> id.oid in AllObjsIDs(ws.objects) &&
                    ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
    ensures forall id :: id in fd_id_val_map
                ==> id.oid in AllObjsIDs(ws.objects) &&
                    ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
    ensures forall id :: id in do_id_val_map
                ==> id.oid in AllObjsIDs(ws.objects) &&
                    ObjPID_KObjects(ws.objects, id.oid) == SubjPID_SlimState(ws.subjects, dev_sid)
        // Property 1: Objects to be modified must be in the same partition with the device
    ensures forall id :: id in td_id_val_map
                ==> id !in AllHCodedTDIDs(ws.subjects)
        // Property 2: Hardcoded TDs are unchanged
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed(
        k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
}




/*********************** Abstract Model Related - Transitive Closure  ********************/
lemma Lemma_K_DevAModesToObjFromTDs_ExistR_SlimState_PropertyDevAModesToObjFromTDs_ExistR_SlimState(
    k_params:ReachableTDsKParams,
    tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID
) returns (result_td_id:TD_ID)
    requires DevAModesToObj_SlimState_PreConditions(k_params, tds, dev_id, o_id)
    requires DevAModesToObjFromTDs_ExistR_SlimState(k_params, tds, dev_id, o_id)

    ensures result_td_id in tds &&        // Exist an active TD (<td_id>)
            CanActiveDevReadActiveTD(k_params, tds, dev_id, result_td_id) &&
                                // The device (<dev_id>) can read the (active) TD
            o_id in GetObjIDsRefedInTD(tds, result_td_id) &&
            R in GetAModesOfObjRefedInTD(tds, result_td_id, o_id)
{
    var td_id :| td_id in tds &&        // Exist an active TD (<td_id>)
            CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id) &&
                                // The device (<dev_id>) can read the (active) TD
            o_id in GetObjIDsRefedInTD(tds, td_id) &&
            R in GetAModesOfObjRefedInTD(tds, td_id, o_id);
                                // The TD refs the object (<o_id>) with R access mode

    return td_id;
}

lemma Lemma_K_DevRead_ReadObjsMustInSystemAndNotHCodedTDs(
    k:State, dev_id:Dev_ID, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= AllTDIDs(k.objects)

    requires forall id :: id in td_ids
            ==> K_DevRead_ReadTDMustBeInATransfer(k, dev_id.sid, id)
    requires forall id :: id in fd_ids
            ==> K_DevRead_ReadFDMustBeInATransfer(k, dev_id.sid, id)
    requires forall id :: id in do_ids
            ==> K_DevRead_ReadDOMustBeInATransfer(k, dev_id.sid, id)
        // Requirement: For each TD writes in <td_ids>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)

    requires StatePropertiesCorollary2(k)

    ensures forall id :: id in td_ids
            ==> id in KToKParams(k).objs_td_ids
    ensures forall id :: id in fd_ids
            ==> id in KToKParams(k).objs_fd_ids
    ensures forall id :: id in do_ids
            ==> id in KToKParams(k).objs_do_ids
    ensures forall td_id :: td_id in td_ids 
            ==> td_id !in KToKParams(k).hcoded_td_ids
{
    var k_tds_state := ActiveTDsState(k);
    Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant(k);
    assert k_tds_state in AllReachableActiveTDsStates(k);

    forall td_id2, dev_id2 | 
            dev_id2 in AllActiveDevs(k) && 
                // The device (<dev_id2>) is active
            td_id2 in AllActiveTDs(k) &&
                // The TD (<td_id2>) is active
            CanActiveDevReadActiveTD(KToKParams(k), k_tds_state, dev_id2, td_id2)
                // The TD is read by the device
        ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), k_tds_state, td_id2)
    {
        assert td_id2 in TDsStateGetTDIDs(k_tds_state);
    }

    Lemma_K_DevRead_ReadObjsMustInSystemAndNotHCodedTDs_Inner(k, dev_id, td_ids, fd_ids, do_ids);
}

// Lemma: In the active TDs' state, TDs refs TDs/FDs/DOs in system only
lemma Lemma_K_TDsInTransitiveClosureRefsTDsFDsDOsInSystemOnly(k:State, tds:map<TD_ID, TD_Val>, dev_id:Dev_ID, td_id:TD_ID)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
    requires IsValidState_ReachableTDsStates(k)

    requires tds == ActiveTDsState(k)
    requires td_id in tds

    requires dev_id in AllActiveDevs(k) && 
             CanActiveDevReadActiveTD(KToKParams(k), tds, dev_id, td_id)

    ensures forall id :: id in tds[td_id].trans_params_tds ==> id in AllTDIDs(k.objects)
    ensures forall id :: id in tds[td_id].trans_params_fds ==> id in AllFDIDs(k.objects)
    ensures forall id :: id in tds[td_id].trans_params_dos ==> id in AllDOIDs(k.objects)
{
    assert tds in AllReachableActiveTDsStates(k);
    
    assert td_id in TDsStateGetTDIDs(tds);
    assert !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), tds, td_id);
}

// Lemma: For the <target_fd_id>, if K_DevRead_ReadFDMustBeInATransfer holds, then DevAModesToObjFromTDs_ExistR_SlimState
// holds
lemma Lemma_K_DevRead_ReadFDMustBeInATransfer_ImpliesDevAModesToObjFromTDs_ExistR_SlimState(
    k:State, dev_sid:Subject_ID, target_fd_id:FD_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
    requires K_DevRead_ReadFDMustBeInATransfer(k, dev_sid, target_fd_id)
    requires target_fd_id in AllFDIDs(k.objects)

    ensures DevAModesToObjFromTDs_ExistR_SlimState(KToKParams(k), ActiveTDsState(k), Dev_ID(dev_sid), target_fd_id.oid)
{
    Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);
    assert K_UniqueIDsAndOwnedObjs(k.subjects, AllTDIDs(k.objects), AllFDIDs(k.objects), AllDOIDs(k.objects));

    var tds := ActiveTDsState(k);

    var td_id :| td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        tds, Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_fd_id in GetTDVal(k, td_id).trans_params_fds &&
                    R in GetTDVal(k, td_id).trans_params_fds[target_fd_id].amodes;

    assert td_id in tds;
    assert GetTDVal(k, td_id) == tds[td_id];
    assert target_fd_id.oid in GetObjIDsRefedInTD(tds, td_id);

    // Prove R in GetAModesOfObjRefedInTD(tds, td_id, target_fd_id.oid)
    Lemma_K_TDsInTransitiveClosureRefsTDsFDsDOsInSystemOnly(k, tds, Dev_ID(dev_sid), td_id);
    assert forall id :: id in tds[td_id].trans_params_tds ==> id in AllTDIDs(k.objects);
    assert forall id :: id in tds[td_id].trans_params_fds ==> id in AllFDIDs(k.objects);
    assert forall id :: id in tds[td_id].trans_params_dos ==> id in AllDOIDs(k.objects);

    assert GetAModesOfObjRefedInTD(tds, td_id, target_fd_id.oid) == tds[td_id].trans_params_fds[target_fd_id].amodes;
    assert R in GetAModesOfObjRefedInTD(tds, td_id, target_fd_id.oid);
}

// Lemma: For the <target_do_id>, if K_DevRead_ReadDOMustBeInATransfer holds, then DevAModesToObjFromTDs_ExistR_SlimState
// holds
lemma Lemma_K_DevRead_ReadDOMustBeInATransfer_ImpliesDevAModesToObjFromTDs_ExistR_SlimState(
    k:State, dev_sid:Subject_ID, target_do_id:DO_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
    requires K_DevRead_ReadDOMustBeInATransfer(k, dev_sid, target_do_id)
    requires target_do_id in AllDOIDs(k.objects)

    ensures DevAModesToObjFromTDs_ExistR_SlimState(KToKParams(k), ActiveTDsState(k), Dev_ID(dev_sid), target_do_id.oid)
{
    Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);
    assert K_UniqueIDsAndOwnedObjs(k.subjects, AllTDIDs(k.objects), AllFDIDs(k.objects), AllDOIDs(k.objects));

    var tds := ActiveTDsState(k);

    var td_id :| td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        tds, Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_do_id in GetTDVal(k, td_id).trans_params_dos &&
                    R in GetTDVal(k, td_id).trans_params_dos[target_do_id].amodes;

    assert td_id in tds;
    assert GetTDVal(k, td_id) == tds[td_id];
    assert target_do_id.oid in GetObjIDsRefedInTD(tds, td_id);

    // Prove R in GetAModesOfObjRefedInTD(tds, td_id, target_do_id.oid)
    Lemma_K_TDsInTransitiveClosureRefsTDsFDsDOsInSystemOnly(k, tds, Dev_ID(dev_sid), td_id);
    assert forall id :: id in tds[td_id].trans_params_tds ==> id in AllTDIDs(k.objects);
    assert forall id :: id in tds[td_id].trans_params_fds ==> id in AllFDIDs(k.objects);
    assert forall id :: id in tds[td_id].trans_params_dos ==> id in AllDOIDs(k.objects);

    assert GetAModesOfObjRefedInTD(tds, td_id, target_do_id.oid) == tds[td_id].trans_params_dos[target_do_id].amodes;
    assert R in GetAModesOfObjRefedInTD(tds, td_id, target_do_id.oid);
}




/*********************** Lemmas - Operations Inner Functions  ********************/
lemma Lemma_DM_RedDrvRead_InnerFunc_Properties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>,  // Map from destination DO to source DO

    result:(DM_State, bool)
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid
        // Requirement: the driver is in a red partition

    requires read_objs <= DM_AllObjsIDs(ws.objects)
    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in tds_dst_src
        // Requirement: The driver does not write any hardcoded TDs
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id.oid !in read_objs
        // Requirement: Read objects must not be any hardcoded TDs

    requires result == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures result.1 ==> result.0 == DM_RedDrvWrite_InnerFunc(ws, drv_sid, 
                                            DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)).1
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_GreenDrvRead_InnerFunc_Properties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>,  // Map from destination DO to source DO

    result:(DM_State, bool)
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
        // Requirement: the driver is in a green partition

    requires read_objs <= DM_AllObjsIDs(ws.objects)
    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in tds_dst_src
        // Requirement: The driver does not write any hardcoded TDs
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id.oid !in read_objs
        // Requirement: Read objects must not be any hardcoded TDs

    requires result == DM_GreenDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures result.1 ==> result.0 == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, 
                                            DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)).0
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_DevRead_ReadTDMustBeInATransfer_ProveReadInDevAModesToObj(
    k:State, dev_sid:Subject_ID, target_td_id:TD_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
    requires K_DevRead_ReadTDMustBeInATransfer(k, dev_sid, target_td_id)

    ensures R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), target_td_id.oid)
{
    var k_params := KToKParams(k);
    var k_tds_state := ActiveTDsState(k);
    var dev_id := Dev_ID(dev_sid);

    var td_id :| td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(k_params, 
                        k_tds_state, Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_td_id in GetTDVal(k, td_id).trans_params_tds &&
                    R in GetTDVal(k, td_id).trans_params_tds[target_td_id].amodes;

    assert target_td_id.oid in GetObjIDsRefedInTD(k_tds_state, td_id);
    assert R in GetAModesOfObjRefedInTD(k_tds_state, td_id, target_td_id.oid);

    assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, k_tds_state, dev_id, target_td_id.oid);
    Lemma_K_DevAModesToObjFromTDs_ExistR_SlimState_ProveDevAModesToObj_SlimState(k, dev_id, target_td_id.oid);
}

// [NOTE] Needs 50s to verify
lemma {:timeLimitMultiplier 7} Lemma_K_DevRead_ReadFDMustBeInATransfer_ProveReadInDevAModesToObj(
    k:State, dev_sid:Subject_ID, target_fd_id:FD_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
    requires K_DevRead_ReadFDMustBeInATransfer(k, dev_sid, target_fd_id)

    ensures R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), target_fd_id.oid)
{
    var k_params := KToKParams(k);
    var k_tds_state := ActiveTDsState(k);
    var dev_id := Dev_ID(dev_sid);

    var td_id :| td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(k_params, 
                        k_tds_state, Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_fd_id in GetTDVal(k, td_id).trans_params_fds &&
                    R in GetTDVal(k, td_id).trans_params_fds[target_fd_id].amodes &&
                    K_DevRead_TDRefObjWithDifferentObjectID(GetTDVal(k, td_id));

    reveal IsValidState_Objects_UniqueObjIDs();
    Lemma_SameIDsIffSameInternalIDs();

    assert target_fd_id.oid in GetObjIDsRefedInTD(k_tds_state, td_id);
    Lemma_K_DevRead_ReadFDMustBeInATransfer_ProveReadInDevAModesToObj_Inner(k, dev_sid, td_id, target_fd_id);
    assert R in GetAModesOfObjRefedInTD(k_tds_state, td_id, target_fd_id.oid);

    assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, k_tds_state, dev_id, target_fd_id.oid);
    Lemma_K_DevAModesToObjFromTDs_ExistR_SlimState_ProveDevAModesToObj_SlimState(k, dev_id, target_fd_id.oid);
}

// [NOTE] Needs 50s to verify
lemma {:timeLimitMultiplier 7} Lemma_K_DevRead_ReadDOMustBeInATransfer_ProveReadInDevAModesToObj(
    k:State, dev_sid:Subject_ID, target_do_id:DO_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
    requires K_DevRead_ReadDOMustBeInATransfer(k, dev_sid, target_do_id)

    ensures R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), target_do_id.oid)
{
    var k_params := KToKParams(k);
    var k_tds_state := ActiveTDsState(k);
    var dev_id := Dev_ID(dev_sid);

    var td_id :| td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(k_params, 
                        k_tds_state, Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_do_id in GetTDVal(k, td_id).trans_params_dos &&
                    R in GetTDVal(k, td_id).trans_params_dos[target_do_id].amodes &&
                    K_DevRead_TDRefObjWithDifferentObjectID(GetTDVal(k, td_id));

    reveal IsValidState_Objects_UniqueObjIDs();
    Lemma_SameIDsIffSameInternalIDs();

    assert target_do_id.oid in GetObjIDsRefedInTD(k_tds_state, td_id);
    Lemma_K_DevRead_ReadDOMustBeInATransfer_ProveReadInDevAModesToObj_Inner(k, dev_sid, td_id, target_do_id);
    assert R in GetAModesOfObjRefedInTD(k_tds_state, td_id, target_do_id.oid);

    assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, k_tds_state, dev_id, target_do_id.oid);
    Lemma_K_DevAModesToObjFromTDs_ExistR_SlimState_ProveDevAModesToObj_SlimState(k, dev_id, target_do_id.oid);
}




/*********************** Private Lemmas ********************/
lemma Lemma_K_DevRead_ReadFDMustBeInATransfer_ProveReadInDevAModesToObj_Inner(
    k:State, dev_sid:Subject_ID, td_id:TD_ID, target_fd_id:FD_ID
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires td_id in ActiveTDsState(k)
    
    requires K_DevRead_TDRefObjWithDifferentObjectID(GetTDVal(k, td_id))
    requires target_fd_id in GetTDVal(k, td_id).trans_params_fds

    ensures GetAModesOfObjRefedInTD(ActiveTDsState(k), td_id, target_fd_id.oid) == 
            GetTDVal(k, td_id).trans_params_fds[target_fd_id].amodes
{
    var k_tds_state := ActiveTDsState(k);
    var t1 := GetAModesOfObjRefedInTD(k_tds_state, td_id, target_fd_id.oid);
    var t2 := GetTDVal(k, td_id).trans_params_fds[target_fd_id].amodes;

    assert t2 == k_tds_state[td_id].trans_params_fds[target_fd_id].amodes;
}

lemma Lemma_K_DevRead_ReadDOMustBeInATransfer_ProveReadInDevAModesToObj_Inner(
    k:State, dev_sid:Subject_ID, td_id:TD_ID, target_do_id:DO_ID
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires td_id in ActiveTDsState(k)
    
    requires K_DevRead_TDRefObjWithDifferentObjectID(GetTDVal(k, td_id))
    requires target_do_id in GetTDVal(k, td_id).trans_params_dos

    ensures GetAModesOfObjRefedInTD(ActiveTDsState(k), td_id, target_do_id.oid) == 
            GetTDVal(k, td_id).trans_params_dos[target_do_id].amodes
{
    var k_tds_state := ActiveTDsState(k);
    var t1 := GetAModesOfObjRefedInTD(k_tds_state, td_id, target_do_id.oid);
    var t2 := GetTDVal(k, td_id).trans_params_dos[target_do_id].amodes;

    assert t2 == k_tds_state[td_id].trans_params_dos[target_do_id].amodes;
}

// [NOTE] Needs 100s to verify
lemma Lemma_K_DevRead_ReadObjsMustInSystemAndNotHCodedTDs_Inner(
    k:State, dev_id:Dev_ID, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
        // Requirement: Subjects have different internal IDs
    requires IsValidState_Objects(k)
    
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= AllTDIDs(k.objects)

    requires forall td_id2 :: td_id2 in td_ids
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD in the system 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    td_id2 in GetTDVal(k, td_id).trans_params_tds &&
                    R in GetTDVal(k, td_id).trans_params_tds[td_id2].amodes)
                        // The TD references the target TD (<td_id2>) with R
    requires forall fd_id2 :: fd_id2 in fd_ids
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD in the system 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    fd_id2 in GetTDVal(k, td_id).trans_params_fds &&
                    R in GetTDVal(k, td_id).trans_params_fds[fd_id2].amodes)
                        // The TD references the target FD (<fd_id2>) with R
    requires forall do_id2 :: do_id2 in do_ids
            ==> (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD in the system 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    do_id2 in GetTDVal(k, td_id).trans_params_dos &&
                    R in GetTDVal(k, td_id).trans_params_dos[do_id2].amodes)
                        // The TD references the target DO (<do_id2>) with R
        // Requirement: For each TD writes in <td_ids>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)

    requires forall td_id2, dev_id2 :: 
            dev_id2 in AllActiveDevs(k) && 
                // The device (<dev_id2>) is active
            td_id2 in AllActiveTDs(k) &&
                // The TD (<td_id2>) is active
            CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id2, td_id2)
                // The TD is read by the device
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), ActiveTDsState(k), td_id2)
        // Requirement: In the current TDs' state of k, any active TDs read by any
        // active devices have no invalid references to I/O objects
    requires StatePropertiesCorollary2(k)

    ensures forall id :: id in td_ids
            ==> id in KToKParams(k).objs_td_ids
    ensures forall id :: id in fd_ids
            ==> id in KToKParams(k).objs_fd_ids
    ensures forall id :: id in do_ids
            ==> id in KToKParams(k).objs_do_ids
    ensures forall td_id :: td_id in td_ids
            ==> td_id !in KToKParams(k).hcoded_td_ids
{
    var k_params := KToKParams(k);
    var tds_state := ActiveTDsState(k);

    forall td_id2 | td_id2 in td_ids
        ensures td_id2 in k_params.objs_td_ids
        ensures td_id2 !in k_params.hcoded_td_ids
    {
        assert R in DevAModesToObj_SlimState(k_params, tds_state, dev_id, td_id2.oid);
        assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, tds_state, dev_id, td_id2.oid);
        var td_id := Lemma_K_DevAModesToObjFromTDs_ExistR_SlimState_PropertyDevAModesToObjFromTDs_ExistR_SlimState(k_params, tds_state, dev_id, td_id2.oid);

        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id);
    }

    forall fd_id2 | fd_id2 in fd_ids
        ensures fd_id2 in k_params.objs_fd_ids
    {
        assert R in DevAModesToObj_SlimState(k_params, tds_state, dev_id, fd_id2.oid);
        assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, tds_state, dev_id, fd_id2.oid);
        var td_id := Lemma_K_DevAModesToObjFromTDs_ExistR_SlimState_PropertyDevAModesToObjFromTDs_ExistR_SlimState(k_params, tds_state, dev_id, fd_id2.oid);

        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id);
    }

    forall do_id2 | do_id2 in do_ids
        ensures do_id2 in k_params.objs_do_ids
    {
        assert R in DevAModesToObj_SlimState(k_params, tds_state, dev_id, do_id2.oid);
        assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, tds_state, dev_id, do_id2.oid);
        var td_id := Lemma_K_DevAModesToObjFromTDs_ExistR_SlimState_PropertyDevAModesToObjFromTDs_ExistR_SlimState(k_params, tds_state, dev_id, do_id2.oid);

        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id);
    }
}