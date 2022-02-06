include "../Abstract/Model.dfy"
include "Mappings_ValidState_SecureState.dfy"
include "Utils_DevsActivateCond.dfy"
include "DevHWProt_Func.dfy"
include "Model_Ops_Predicates.dfy"
include "Lemmas_Ops_SubjRead.dfy"

//******** DrvRead/DevRead ********//
function DM_RedDrvRead_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) : (result:(DM_State, bool))
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

    ensures result.1 ==> (
                        (forall td_id :: td_id in tds_dst_src ==> tds_dst_src[td_id] in ws.objects.active_non_hcoded_tds) &&
                        (forall fd_id :: fd_id in fds_dst_src ==> fds_dst_src[fd_id] in ws.objects.active_fds) &&
                        (forall do_id :: do_id in dos_dst_src ==> dos_dst_src[do_id] in ws.objects.active_dos)
                    )
        // Properties needed by the following properties
    ensures result.1 ==> result.0 == DM_RedDrvWrite_InnerFunc(ws, drv_sid, 
                                            DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)).1
    ensures !result.1 ==> result.0 == ws
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    if( forall o_id :: o_id in read_objs ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, o_id)) then
        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, drv_sid, read_objs);

        // Prove (forall td_id :: td_id in tds_dst_src ==> tds_dst_src[td_id] in ws.objects.active_non_hcoded_tds)
        assert forall td_id :: td_id in tds_dst_src ==> ObjPID_KObjects(ws.objects, tds_dst_src[td_id].oid) != NULL;
        Lemma_DrvRead_SrcObjsOfCopyMustBeActive(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);

        var ws2' := DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1;
        var d := DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2;
        (ws2',d)
    else
        (ws, false)
}

function method DM_GreenDrvRead_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: the driver is in a green partition

    requires read_objs <= DM_AllObjsIDs(ws.objects)
    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in tds_dst_src
        // Requirement: The driver does not write any hardcoded TDs

    ensures result.1 ==> result.0 == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, 
                                            DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)).0
    ensures !result.1 ==> result.0 == ws
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    if( forall o_id :: o_id in read_objs ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, o_id)) then
        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, drv_sid, read_objs);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);

        DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    else
        (ws, false)
}

function method DM_DevRead_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is active

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(ws, dev_sid, read_objs)
    requires DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    // Construct ws'
    var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
    var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
    var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);

    if(DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid) then
        // If the device is in the red partition
        DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    else
        // If the device is in a green partition
        DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}




//******** DrvWrite/DevWrite ********//
function DM_RedDrvWrite_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid
        // Requirement: the driver is in the red partition

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(ws.objects))

    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs

    ensures result.2 ==> DM_IsValidState(result.0)
    ensures MapGetKeys(result.1.objects.active_non_hcoded_tds) == MapGetKeys(ws.objects.active_non_hcoded_tds)

    ensures DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) <==> result.2
        // Property: Correctness of returning true
{
    if( DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) then
        // Construct ws'.objects
        var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
        var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
        var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
        var new_objects := t_objs3;

        var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_DrvDevWrite_ProveActiveObjsMustHaveNonNULLPID(ws.objects, td_id_val_map, fd_id_val_map, do_id_val_map, ws'.objects);
        Lemma_K_SameObjIDs_ProveIsValidState_Objects_UniqueObjIDs(ws.objects, ws'.objects);
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_DrvDevWrite_PreserveObjPIDs(ws.objects, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDM_FulFillIsValidState_SubjsOwnObjsThenInSamePartition_IfPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Apply DevHWProt
        var ws2' := DevHWProt(ws, ws');
        var ws_d := true;

        assert P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(ws', ws2');
        assert MapGetKeys(ws'.objects.active_non_hcoded_tds) == MapGetKeys(ws2'.objects.active_non_hcoded_tds);

        (ws', ws2', ws_d)
    else
        (ws, ws, false)
}

function method DM_GreenDrvWrite_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: the driver is in the green partition

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(ws.objects))
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs

    ensures IsValidState_Objects_UniqueObjIDs(result.0.objects)
    ensures AllTDIDs(ws.objects) == AllTDIDs(result.0.objects)
    ensures AllObjsIDs(ws.objects) == AllObjsIDs(result.0.objects)
        // Properties needed by the following property
    ensures forall id :: id in AllObjsIDs(ws.objects)
                ==> ObjPID_KObjects(result.0.objects, id) == ObjPID_KObjects(ws.objects, id)
        // Property:
    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures result.1 == true <==>
            (
                DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) &&
                DM_GreenDrvWrite_ChkNewValsOfTDs(ws, td_id_val_map)
            )
        // Property: Correctness of returning true
    ensures var k := DMStateToState(ws);
            result.1 == true ==> (forall id :: id in td_id_val_map ==> id in ws.objects.active_non_hcoded_tds) &&
                    (forall id :: id in fd_id_val_map ==> id in ws.objects.active_fds) &&
                    (forall id :: id in do_id_val_map ==> id in ws.objects.active_dos)
        // Properties needed by the following property
    ensures (result.1 == true ==> DrvDevWrite_Func(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DrvDeactivate in the abstract model
{
    if( DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) &&
        DM_GreenDrvWrite_ChkNewValsOfTDs(ws, td_id_val_map)
    ) then
        // Construct ws'.objects
        var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
        var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
        var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
        var new_objects := t_objs3;

        var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        Lemma_DrvDevWrite_PreserveObjPIDs(ws.objects, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_DrvDevWrite_ProveActiveObjsMustHaveNonNULLPID(ws.objects, td_id_val_map, fd_id_val_map, do_id_val_map, ws'.objects);

        // Prove Property 2
        var k' := DMStateToState(ws');
        assert k' == DrvDevWrite_Func(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map);

        (ws', ws_d)
    else
        (ws, false)
}

function method DM_RedDevWrite_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid
        // Requirement: the device is in the red partition

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_sid, td_id2, td_id_val_map[td_id2])
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(ws, dev_sid, fd_id2, fd_id_val_map[fd_id2])
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(ws, dev_sid, do_id2, do_id_val_map[do_id2])

    ensures IsValidState_Objects_UniqueObjIDs(result.0.objects)
    ensures AllTDIDs(ws.objects) == AllTDIDs(result.0.objects)
    ensures AllObjsIDs(ws.objects) == AllObjsIDs(result.0.objects)
        // Properties needed by the following property
    ensures forall id :: id in AllObjsIDs(ws.objects)
                ==> ObjPID_KObjects(result.0.objects, id) == ObjPID_KObjects(ws.objects, id)
    ensures forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> ObjStateUnchanged_TD(ws.objects, result.0.objects, td_id)
        // Property: 
    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures result.1 == true
        // Property: Correctness of returning true
    ensures var k := DMStateToState(ws);
            result.1 == true ==> (forall id :: id in td_id_val_map ==> id in ws.objects.active_non_hcoded_tds) &&
                    (forall id :: id in fd_id_val_map ==> id in ws.objects.active_fds) &&
                    (forall id :: id in do_id_val_map ==> id in ws.objects.active_dos)
        // Properties needed by the following property
    ensures (result.1 == true ==> DrvDevWrite_Func(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DrvDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    // Prove necessary preconditions
    Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed(
        k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map;

    // Construct ws'.objects
    var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
    var new_objects := t_objs3;

    var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
    var ws_d := true;

    Lemma_DrvDevWrite_PreserveObjPIDs(ws.objects, td_id_val_map, fd_id_val_map, do_id_val_map);
    Lemma_DrvDevWrite_ProveActiveObjsMustHaveNonNULLPID(k.objects, td_id_val_map, fd_id_val_map, do_id_val_map, ws'.objects);

    // Prove Property 2
    var k' := DMStateToState(ws');
    assert k' == DrvDevWrite_Func(k, td_id_val_map, fd_id_val_map, do_id_val_map);

    (ws', ws_d)
}

function method DM_GreenDevWrite_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
    requires DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid
        // Requirement: the device must be in a green partition

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_sid, td_id2, td_id_val_map[td_id2])
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(ws, dev_sid, fd_id2, fd_id_val_map[fd_id2])
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(ws, dev_sid, do_id2, do_id_val_map[do_id2])

    ensures result.1 == true
        // Property: Correctness of returning true
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    // Prove necessary preconditions
    Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed(
        k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map;

    // Construct ws'.objects
    var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
    var new_objects := t_objs3;

    var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
    var ws_d := true;

    Lemma_DrvDevWrite_PreserveObjPIDs(ws.objects, td_id_val_map, fd_id_val_map, do_id_val_map);

    (ws', ws_d)
}




//******** Create/Destroy Partition ********//
function method DM_EmptyPartitionCreate_InnerFunc(
    ws:DM_State, 
    new_pid:Partition_ID // The ID of the new partition
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
{
    if (new_pid != NULL) &&
        (new_pid !in ws.pids) 
    then
        // Add the ID of the creating partition into the new state
        var pids' := ws.pids + {new_pid};

        var ws'_subjects := ws.subjects;
        var ws'_objects := ws.objects;

        var ws' := DM_State(ws'_subjects, ws'_objects, pids', ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        (ws', ws_d)
    else
        (ws, false)
}

function method DM_EmptyPartitionDestroy_InnerFunc(
    ws:DM_State, 
    pid:Partition_ID // The ID of the partition to be destroyed
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
{
    if ((pid != NULL) &&
        (pid in ws.pids) &&
        (forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects) ==> DM_SubjPID(ws.subjects, s_id) != pid) &&
        (forall o_id :: o_id in DM_AllObjsIDs(ws.objects) ==> DM_ObjPID(ws.objects, o_id) != pid) &&
        pid != ws.red_pid)
            // OS partition cannot be destroyed
    then
        // Add the ID of the creating partition into the new state
        var pids' := ws.pids - {pid};

        var ws'_subjects := ws.subjects;
        var ws'_objects := ws.objects;

        var ws' := DM_State(ws'_subjects, ws'_objects, pids', ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        (ws', ws_d)
    else
        (ws, false)
}




//******** DrvActivate ********//
function method DM_DrvActivateToGreenPartition_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver to be activated
    green_pid:Partition_ID // ID of the partition to activate the driver into
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires green_pid != NULL
    requires green_pid != ws.red_pid
        // Requirement: the destination partition must be a green partition

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures var k := DMStateToState(ws);
            result.1 == true ==> (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.inactive_fds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.inactive_dos)
        // Properties needed by the following property
    ensures (result.1 == true ==> DrvActivate_Func(DMStateToState(ws), drv_sid, green_pid) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DrvDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Drv_Property(k, Drv_ID(drv_sid));

    var drv_id := Drv_ID(drv_sid);
    if((DM_SubjPID(ws.subjects, drv_sid) == NULL) && (green_pid in ws.pids)) then
        // Set the driver's partition ID to be <green_pid>
        var drv_state := ws.subjects.drvs[drv_id];
        var new_drv_state := Drv_State(green_pid, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
        var new_drvs := ws.subjects.drvs[drv_id := new_drv_state];
        var new_subjects := Subjects(new_drvs, ws.subjects.devs);

        // Construct k'.objects
        var tds_owned_by_drv:set<TD_ID> := ws.subjects.drvs[drv_id].td_ids;
        var fds_owned_by_drv:set<FD_ID> := ws.subjects.drvs[drv_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := ws.subjects.drvs[drv_id].do_ids;

        //// Prove the driver's objects are in <k.objects.inactive_*>
        Lemma_DrvActivate_DrvObjsInKMustBeInactive(k, drv_id);

        //// Modify the PID of these objects (i.e., SetObjsPIDs)
        var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(ws.objects, tds_owned_by_drv, green_pid);
        var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_drv, green_pid);
        var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_drv, green_pid);
        
        var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        Lemma_DrvActivate_ProveActiveObjsMustHaveNonNULLPID(k, drv_id, green_pid);

        // Prove Property 2
        var k' := DMStateToState(ws');
        assert k' == DrvActivate_Func(k, drv_sid, green_pid);

        (ws', ws_d)
    else
        (ws, false)
}

function method DM_DrvActivateToRedPartition_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures var k := DMStateToState(ws);
            result.1 == true ==> (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.inactive_fds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.inactive_dos)
        // Properties needed by the following property
    ensures (result.1 == true ==> DrvActivate_Func(DMStateToState(ws), drv_sid, ws.red_pid) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DrvDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Drv_Property(k, Drv_ID(drv_sid));

    var drv_id := Drv_ID(drv_sid);

    var pid := ws.red_pid;
    if((DM_SubjPID(ws.subjects, drv_sid) == NULL)) then
        // Set the driver's partition ID to be <red_pid>
        var drv_state := ws.subjects.drvs[drv_id];
        var new_drv_state := Drv_State(pid, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
        var new_drvs := ws.subjects.drvs[drv_id := new_drv_state];
        var new_subjects := Subjects(new_drvs, ws.subjects.devs);

        // Construct k'.objects
        var tds_owned_by_drv:set<TD_ID> := ws.subjects.drvs[drv_id].td_ids;
        var fds_owned_by_drv:set<FD_ID> := ws.subjects.drvs[drv_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := ws.subjects.drvs[drv_id].do_ids;

        //// Prove the driver's objects are in <k.objects.inactive_*>
        Lemma_DrvActivate_DrvObjsInKMustBeInactive(k, drv_id);

        //// Modify the PID of these objects (i.e., SetObjsPIDs)
        var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(ws.objects, tds_owned_by_drv, pid);
        var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_drv, pid);
        var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_drv, pid);
        
        var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        Lemma_DrvActivate_ProveActiveObjsMustHaveNonNULLPID(k, drv_id, pid);

        // Prove Property 2
        var k' := DMStateToState(ws');
        assert k' == DrvActivate_Func(k, drv_sid, pid);

        (ws', ws_d)
    else
        (ws, false)
}




//******** DevActivate ********//
function method DM_DevActivate_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device to be activated
    pid:Partition_ID // ID of the partition to activate the device into
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires pid != NULL

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures result.1 == true ==> (forall id :: id in ws.subjects.devs[Dev_ID(dev_sid)].td_ids && 
                    id != ws.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id 
                 ==> id in ws.objects.inactive_non_hcoded_tds)
    ensures result.1 == true ==> (forall id :: id in ws.subjects.devs[Dev_ID(dev_sid)].fd_ids ==> id in ws.objects.inactive_fds)
    ensures result.1 == true ==> (forall id :: id in ws.subjects.devs[Dev_ID(dev_sid)].do_ids ==> id in ws.objects.inactive_dos)
    ensures result.1 == true ==> (ws.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id in ws.objects.hcoded_tds)
        // Properties needed by the following property
    ensures (result.1 == true ==> DevActivate_Func(DMStateToState(ws), dev_sid, pid) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DevDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Dev_Property(k, Dev_ID(dev_sid));

    var dev_id := Dev_ID(dev_sid);
    if( (DM_SubjPID(ws.subjects, dev_sid) == NULL) && (pid in ws.pids) &&
            (pid == ws.red_pid ==> TryActivateDevInRed(ws, dev_id)) &&
            (pid != ws.red_pid ==> TryActivateDevInGreen(ws, dev_id)) &&
                // If the device is an ephemeral device, the two checks decide 
                // if we can activate the device into the destination partition
            (forall hcoded_td_id, td_id :: hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id &&
                        td_id in k.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
                    ==> W !in k.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds[td_id].amodes)
    ) then
        // Set the device's partition ID to be <pid>
        var dev_state := ws.subjects.devs[dev_id];
        var new_dev_state := Dev_State(pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
        var new_devs := ws.subjects.devs[dev_id := new_dev_state];
        var new_subjects := Subjects(ws.subjects.drvs, new_devs);

        // Construct k'.objects
        var tds_owned_by_dev:set<TD_ID> := ws.subjects.devs[dev_id].td_ids;
        var fds_owned_by_dev:set<FD_ID> := ws.subjects.devs[dev_id].fd_ids;
        var dos_owned_by_dev:set<DO_ID> := ws.subjects.devs[dev_id].do_ids;
        //// Clear the objects being activated
        var toactive_hcoded_td_id := dev_state.hcoded_td_id;
        var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};

        //// Prove the driver's objects are in <k.objects.inactive_*>
        Lemma_DevActivate_DevObjsInKMustBeInactive(k, dev_id);

        //// Modify the PID of these objects (i.e., SetObjsPIDs)
        var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(ws.objects, toclear_td_ids, pid);
        var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
        var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);
        var new_objects := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid);

        var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        Lemma_DevActivate_ProveActiveObjsMustHaveNonNULLPID(k, dev_id, pid);

        // Prove Property 2
        var k' := DMStateToState(ws');
        assert k' == DevActivate_Func(k, dev_sid, pid);

        // Call underlying functions to activate ephemeral devices
        if(Edev_Activate(DMStateToState(ws), dev_id)) then
            (ws', ws_d)
        else
            (ws, false)
    else
       (ws, false)
}




//******** ExternalObjsActivate ********//
function method DM_ExternalObjsActivateToGreenPartition_InnerFunc(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be activated
    green_pid:Partition_ID // ID of the partition to activate the objects into
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires td_ids <= AllTDIDs(ws.objects)
    requires fd_ids <= AllFDIDs(ws.objects)
    requires do_ids <= AllDOIDs(ws.objects)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects 

    requires green_pid != NULL
    requires green_pid != ws.red_pid

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures result.1 == true ==> (forall id :: id in td_ids ==> id in ws.objects.inactive_non_hcoded_tds)
    ensures result.1 == true ==> (forall id :: id in fd_ids ==> id in ws.objects.inactive_fds)
    ensures result.1 == true ==> (forall id :: id in do_ids ==> id in ws.objects.inactive_dos)
    ensures IsValidState(DMStateToState(ws))
    ensures var k := DMStateToState(ws);
            (result.1 == true) ==> (forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                        o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                    ==> !DoOwnObj(k, s_id, o_id))
        // Properties needed by the following property
    
    ensures (result.1 == true ==> ExternalObjsActivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids, green_pid) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DrvDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    if((forall td_id :: td_id in td_ids ==> DM_ObjPID(ws.objects, td_id.oid) == NULL) &&
           (forall fd_id :: fd_id in fd_ids ==> DM_ObjPID(ws.objects, fd_id.oid) == NULL) &&
           (forall do_id :: do_id in do_ids ==> DM_ObjPID(ws.objects, do_id.oid) == NULL) &&
           green_pid in ws.pids
    ) then
        Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
        Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
        Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, td_ids, fd_ids, do_ids);
        Lemma_DM_ExternalObjsActivateToGreenPartition_InnerFunc_ProvePreCondition1(ws, k, td_ids, fd_ids, do_ids);

        //// Prove the external objects are in <k.objects.inactive_*>
        Lemma_ExternalObjsActivate_ExternalObjsInKMustBeInactive(k, td_ids, fd_ids, do_ids);

        // Modify the PID of these objects (i.e., SetObjsPIDs) and clear the objects
        var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(ws.objects, td_ids, green_pid);
        var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fd_ids, green_pid);
        var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, do_ids, green_pid);

        var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        Lemma_ExternalObjsActivate_ProveActiveObjsMustHaveNonNULLPID(k, td_ids, fd_ids, do_ids, green_pid);

        // Prove Property 2
        var k' := DMStateToState(ws');
        assert k' == ExternalObjsActivate_Func(k, td_ids, fd_ids, do_ids, green_pid);

        (ws', ws_d)
    else
        (ws, false)
}

function method DM_ExternalObjsActivateToRedPartition_InnerFunc(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID> //  IDs of the objects to be activated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires td_ids <= AllTDIDs(ws.objects)
    requires fd_ids <= AllFDIDs(ws.objects)
    requires do_ids <= AllDOIDs(ws.objects)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects 

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures result.1 == true ==> (forall id :: id in td_ids ==> id in ws.objects.inactive_non_hcoded_tds)
    ensures result.1 == true ==> (forall id :: id in fd_ids ==> id in ws.objects.inactive_fds)
    ensures result.1 == true ==> (forall id :: id in do_ids ==> id in ws.objects.inactive_dos)
    ensures IsValidState(DMStateToState(ws))
    ensures var k := DMStateToState(ws);
            (result.1 == true) ==> (forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                        o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                    ==> !DoOwnObj(k, s_id, o_id))
        // Properties needed by the following property
    
    ensures (result.1 == true ==> ExternalObjsActivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids, ws.red_pid) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DrvDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    if((forall td_id :: td_id in td_ids ==> DM_ObjPID(ws.objects, td_id.oid) == NULL) &&
           (forall fd_id :: fd_id in fd_ids ==> DM_ObjPID(ws.objects, fd_id.oid) == NULL) &&
           (forall do_id :: do_id in do_ids ==> DM_ObjPID(ws.objects, do_id.oid) == NULL)
    ) then
        Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
        Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
        Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, td_ids, fd_ids, do_ids);
        Lemma_DM_ExternalObjsActivateToGreenPartition_InnerFunc_ProvePreCondition1(ws, k, td_ids, fd_ids, do_ids);

        //// Prove the external objects are in <k.objects.inactive_*>
        Lemma_ExternalObjsActivate_ExternalObjsInKMustBeInactive(k, td_ids, fd_ids, do_ids);

        // Modify the PID of these objects (i.e., SetObjsPIDs) and clear the objects
        var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(ws.objects, td_ids, ws.red_pid);
        var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fd_ids, ws.red_pid);
        var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, do_ids, ws.red_pid);

        var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        Lemma_ExternalObjsActivate_ProveActiveObjsMustHaveNonNULLPID(k, td_ids, fd_ids, do_ids, ws.red_pid);

        // Prove Property 2
        var k' := DMStateToState(ws');
        assert k' == ExternalObjsActivate_Func(k, td_ids, fd_ids, do_ids, ws.red_pid);

        (ws', ws_d)
    else
        (ws, false)
}




//******** DrvDeactivate ********//
function method DM_GreenDrvDeactivate_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: The driver must be in a green partition

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures var k := DMStateToState(ws);
            result.1 == true ==> (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.active_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.active_fds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.active_dos)
        // Properties needed by the following property
    ensures (result.1 == true ==> DrvDeactivate_Func(DMStateToState(ws), drv_sid) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DrvDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Drv_Property(k, Drv_ID(drv_sid));

    var drv_id := Drv_ID(drv_sid);
    var todeactivate_td_ids := ws.subjects.drvs[drv_id].td_ids;
    var todeactivate_fd_ids := ws.subjects.drvs[drv_id].fd_ids;
    var todeactivate_do_ids := ws.subjects.drvs[drv_id].do_ids;
    var pid := DM_SubjPID(ws.subjects, drv_sid);

    if( DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)
            // Ensure no other green TD in the same partition with the driver 
            // has transfers to any objects of the driver
      ) then
        // Set the driver's partition ID to be NULL
        var drv_state := ws.subjects.drvs[drv_id];
        var new_drv_state := Drv_State(NULL, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
        var new_drvs := ws.subjects.drvs[drv_id := new_drv_state];

        // Construct k'.subjects
        var new_subjects := Subjects(new_drvs, ws.subjects.devs);

        // Construct k'.objects
        var tds_owned_by_drv:set<TD_ID> := ws.subjects.drvs[drv_id].td_ids;
        var fds_owned_by_drv:set<FD_ID> := ws.subjects.drvs[drv_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := ws.subjects.drvs[drv_id].do_ids;

        //// Prove the driver's objects are in <k.objects.active_*>
        Lemma_DrvDeactivate_DrvObjsInKMustBeActive(k, drv_id);
        
        //// Modify the PID of these objects
        var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(ws.objects, tds_owned_by_drv);
        var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_drv);
        var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_drv);
        
        var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        Lemma_DrvDeactivate_ProveActiveObjsMustHaveNonNULLPID(k, drv_id);

        // Prove Property 2
        var k' := DMStateToState(ws');
        assert k' == DrvDeactivate_Func(k, drv_sid);

        (ws', ws_d)
    else
        (ws, false)
}

function method DM_RedDrvDeactivate_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid
        // Requirement: The driver must be in the partition

    requires P_RedDevsHaveNoTransferToGivenRedDrvAtAnyTime(ws, Drv_ID(drv_sid))

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures var k := DMStateToState(ws);
            result.1 == true ==> (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.active_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.active_fds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.active_dos)
        // Properties needed by the following property
    ensures (result.1 == true ==> DrvDeactivate_Func(DMStateToState(ws), drv_sid) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DrvDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Drv_Property(k, Drv_ID(drv_sid));

    var drv_id := Drv_ID(drv_sid);
    var todeactivate_td_ids := ws.subjects.drvs[drv_id].td_ids;
    var todeactivate_fd_ids := ws.subjects.drvs[drv_id].fd_ids;
    var todeactivate_do_ids := ws.subjects.drvs[drv_id].do_ids;
    var pid := DM_SubjPID(ws.subjects, drv_sid);

    // Set the driver's partition ID to be NULL
    var drv_state := ws.subjects.drvs[drv_id];
    var new_drv_state := Drv_State(NULL, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
    var new_drvs := ws.subjects.drvs[drv_id := new_drv_state];

    // Construct k'.subjects
    var new_subjects := Subjects(new_drvs, ws.subjects.devs);

    // Construct k'.objects
    var tds_owned_by_drv:set<TD_ID> := ws.subjects.drvs[drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := ws.subjects.drvs[drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := ws.subjects.drvs[drv_id].do_ids;

    //// Prove the driver's objects are in <k.objects.active_*>
    Lemma_DrvDeactivate_DrvObjsInKMustBeActive(k, drv_id);
    
    //// Modify the PID of these objects
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(ws.objects, tds_owned_by_drv);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_drv);
    var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_drv);
    
    var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
    var ws_d := true;

    Lemma_DrvDeactivate_ProveActiveObjsMustHaveNonNULLPID(k, drv_id);

    // Prove Property 2
    var k' := DMStateToState(ws');
    assert k' == DrvDeactivate_Func(k, drv_sid);

    (ws', ws_d)
}




//******** DevDeactivate ********//
function method DM_DevDeactivate_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID // ID of the device to be deactivated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active

    requires DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid 
                ==> P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, Dev_ID(dev_sid))
        // Requirement: If the device is in red, then no other red device has 
        // transfers to any objects of the device to be deactivated

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures result.1 == true ==> (forall id :: id in ws.subjects.devs[Dev_ID(dev_sid)].td_ids && 
                    id != ws.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id 
                 ==> id in ws.objects.active_non_hcoded_tds)
    ensures result.1 == true ==> (forall id :: id in ws.subjects.devs[Dev_ID(dev_sid)].fd_ids ==> id in ws.objects.active_fds)
    ensures result.1 == true ==> (forall id :: id in ws.subjects.devs[Dev_ID(dev_sid)].do_ids ==> id in ws.objects.active_dos)
    ensures result.1 == true ==> (ws.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id in ws.objects.hcoded_tds)
        // Properties needed by the following property
    ensures (result.1 == true ==> DevDeactivate_Func(DMStateToState(ws), dev_sid) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to DevDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Dev_Property(k, Dev_ID(dev_sid));

    var dev_id := Dev_ID(dev_sid);
    
    var todeactivate_td_ids := ws.subjects.devs[dev_id].td_ids;
    var todeactivate_fd_ids := ws.subjects.devs[dev_id].fd_ids;
    var todeactivate_do_ids := ws.subjects.devs[dev_id].do_ids;
    var pid := DM_SubjPID(ws.subjects, dev_sid);
    
    if( (DM_SubjPID(ws.subjects, dev_sid) != NULL && DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid
            ==> DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
                    todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid))
                    // Ensure no other green TD in the same partition with the driver 
                    // has transfers to any objects of the driver
    ) then
        // Set the device's partition ID to be <pid>
        var dev_state := ws.subjects.devs[dev_id];
        var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
        var new_devs := ws.subjects.devs[dev_id := new_dev_state];
        var new_subjects := Subjects(ws.subjects.drvs, new_devs);

        // Construct k'.objects
        var tds_owned_by_dev:set<TD_ID> := ws.subjects.devs[dev_id].td_ids;
        var fds_owned_by_dev:set<FD_ID> := ws.subjects.devs[dev_id].fd_ids;
        var dos_owned_by_dev:set<DO_ID> := ws.subjects.devs[dev_id].do_ids;

        //// Prove the driver's objects are in <k.objects.active_*>
        Lemma_DevDeactivate_DevObjsInKMustBeActive(k, dev_id);

        //// Modify the PID of these objects
        var todeactive_hcoded_td_id := dev_state.hcoded_td_id;
        var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
        var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(ws.objects, todeactive_other_td_ids);
        var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
        var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
        var new_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);
        
        var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        Lemma_DevDeactivate_ProveActiveObjsMustHaveNonNULLPID(k, dev_id);

        // Call underlying functions to deactivate ephemeral devices
        if(Edev_Deactivate(DMStateToState(ws), dev_id)) then
            (ws', ws_d)
        else
            (ws, false)
    else
       (ws, false)
}




//******** ExternalObjsDeactivate ********//
function method DM_GreenExternalObjsDeactivate_InnerFunc(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be deactivated
    green_pid:Partition_ID // The green partition that holds these objects
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires td_ids <= AllTDIDs(ws.objects)
    requires fd_ids <= AllFDIDs(ws.objects)
    requires do_ids <= AllDOIDs(ws.objects)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: no subject owns these external objects

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires forall id :: id in td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
        // Requirement: The objects must be in the same green partition

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures result.1 == true ==> (forall id :: id in td_ids ==> id in ws.objects.active_non_hcoded_tds)
    ensures result.1 == true ==> (forall id :: id in fd_ids ==> id in ws.objects.active_fds)
    ensures result.1 == true ==> (forall id :: id in do_ids ==> id in ws.objects.active_dos)
    ensures (result.1 == true ==> ExternalObjsDeactivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to ExternalObjsDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var todeactivate_td_ids := td_ids;
    var todeactivate_fd_ids := fd_ids;
    var todeactivate_do_ids := do_ids;

    if( DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid)
            // Ensure no other green TD in the same partition with the driver 
            // has transfers to any objects of the driver
    ) then
        Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
        Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
        Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, td_ids, fd_ids, do_ids);
        //// Prove the external objects are in <k.objects.inactive_*>
        Lemma_ExternalObjsDeactivate_ExternalObjsInKMustBeActive(k, td_ids, fd_ids, do_ids);

        // Construct ws'.objects
        //// Modify the PID of these objects
        var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(ws.objects, td_ids);
        var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fd_ids);
        var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, do_ids);
        
        var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        Lemma_ExternalObjsDeactivate_ProveActiveObjsMustHaveNonNULLPID(k, td_ids, fd_ids, do_ids);

        // Prove Property 2
        var k' := DMStateToState(ws');
        assert k' == ExternalObjsDeactivate_Func(k, td_ids, fd_ids, do_ids);

        (ws', ws_d)
    else
        (ws, false)
}

function method DM_RedExternalObjsDeactivate_InnerFunc(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID> //  IDs of the objects to be deactivated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires td_ids <= AllTDIDs(ws.objects)
    requires fd_ids <= AllFDIDs(ws.objects)
    requires do_ids <= AllDOIDs(ws.objects)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: no subject owns these external objects

    requires forall id :: id in td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == ws.red_pid
    requires forall id :: id in fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == ws.red_pid
    requires forall id :: id in do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == ws.red_pid
        // Requirement: The objects must be in the red partition

    requires P_RedDevsHaveNoTransferToGivenRedObjsAtAnyTime(ws, td_ids, fd_ids, do_ids)

    ensures IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(result.0.objects)
        // (Needed in the caller operation) Property 1: <active_*> records active objects (except HCoded TDs) only
    ensures result.1 == true ==> (forall id :: id in td_ids ==> id in ws.objects.active_non_hcoded_tds)
    ensures result.1 == true ==> (forall id :: id in fd_ids ==> id in ws.objects.active_fds)
    ensures result.1 == true ==> (forall id :: id in do_ids ==> id in ws.objects.active_dos)
    ensures (result.1 == true ==> ExternalObjsDeactivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids) == DMStateToState(result.0))
        // (Needed in the caller operation) Property 2: Commutative diagram to ExternalObjsDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var todeactivate_td_ids := td_ids;
    var todeactivate_fd_ids := fd_ids;
    var todeactivate_do_ids := do_ids;

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, td_ids, fd_ids, do_ids);
    //// Prove the external objects are in <k.objects.inactive_*>
    Lemma_ExternalObjsDeactivate_ExternalObjsInKMustBeActive(k, td_ids, fd_ids, do_ids);

    // Construct ws'.objects
    //// Modify the PID of these objects
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(ws.objects, td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fd_ids);
    var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, do_ids);
    
    var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
    var ws_d := true;

    Lemma_ExternalObjsDeactivate_ProveActiveObjsMustHaveNonNULLPID(k, td_ids, fd_ids, do_ids);

    // Prove Property 2
    var k' := DMStateToState(ws');
    assert k' == ExternalObjsDeactivate_Func(k, td_ids, fd_ids, do_ids);

    (ws', ws_d)
}