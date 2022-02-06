include "../../WK_Design/Model.dfy"

// [TODO] This file is an ugly hack. It should be removed once we convert operations in the abstract model, concrete 
// model and WK design spec to be Dafny functions
// [NOTE] Axioms in this file have already proved in the WK design. 

// Corresponding to DM_RedDrvWrite in the detailed model
function {:axiom} WSD_OSDrvWrite_Stub(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid
        // Requirement: the driver is in the red partition

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws_d := result.1;
            ws_d == true
                ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    ensures var ws' := result.0;
            ws' == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1
    ensures var ws_d := result.1;
            ws_d == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WSD_OSDevWrite_Stub(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

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

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))
        // Properties needed by the following properties
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device
    ensures var ws_d := result.1;
            ws_d == true

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WSD_WimpDrvRead_Stub(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) : (result:(DM_State, bool))
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
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
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id.oid !in read_objs
        // Requirement: Read objects must not be any hardcoded TDs

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')
    
    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_GreenDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WSD_WimpDrvWrite_Stub(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: the driver is in the green partition

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws_d := result.1;
            ws_d == true 
                ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WSD_WimpDevWrite_Stub(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

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

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))
        // Properties needed by the following property
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device
    ensures var ws_d := result.1;
            ws_d == true

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Correctness property for proving the commutative diagram

        
predicate DM_DevWrite_PreConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (DM_IsDevID(ws.subjects, Dev_ID(dev_sid))) &&
    (DM_SubjPID(ws.subjects, dev_sid) != NULL) &&
        // Requirement: the device must be active

    (forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_sid, td_id2, td_id_val_map[td_id2])) &&
    (forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(ws, dev_sid, fd_id2, fd_id_val_map[fd_id2])) &&
    (forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(ws, dev_sid, do_id2, do_id_val_map[do_id2])) &&

    (true)
}

function {:axiom} WSD_DevWrite_Stub(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: The device must be active

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_sid, td_id2, td_id_val_map[td_id2])
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(ws, dev_sid, fd_id2, fd_id_val_map[fd_id2])
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(ws, dev_sid, do_id2, do_id_val_map[do_id2])

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))
        // Properties needed by the following property
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device
    ensures var ws_d := result.1;
            ws_d == true

    ensures var ws' := result.0;
            var ws_d := result.1;
            DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid
                ==> (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures var ws' := result.0;
            var ws_d := result.1;
            DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid
                ==> (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WKD_EmptyPartitionCreate_Stub(
    ws:DM_State, 
    new_pid:Partition_ID // The ID of the new partition
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_EmptyPartitionCreate_InnerFunc(ws, new_pid)
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WKD_EmptyPartitionDestroy_Stub(
    ws:DM_State, 
    pid:Partition_ID // The ID of the new partition
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_EmptyPartitionDestroy_InnerFunc(ws, pid)
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WKD_DrvActivateToGreenPartition_Stub(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver to be activated
    green_pid:Partition_ID // ID of the partition to activate the driver into
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires green_pid != NULL
    requires green_pid != ws.red_pid
        // Requirement: the destination partition must be a green partition

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid)
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WKD_DevActivate_Stub(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device to be activated
    pid:Partition_ID // ID of the partition to activate the driver into
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires pid != NULL

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_DevActivate_InnerFunc(ws, dev_sid, pid)
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WKD_GreenDrvDeactivate_Stub(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: The driver must be in a green partition

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid)
        // Property: Correctness property for proving the commutative diagram


function {:axiom} WKD_DevDeactivate_Stub(
    ws:DM_State, 
    dev_sid:Subject_ID // ID of the device to be activated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active
    requires DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid 
                ==> P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, Dev_ID(dev_sid))
        // Requirement: If the device is in red, then no other red device has 
        // transfers to any objects of the device to be deactivated
        // [Note] This is not a protection constraint, because we can check it 
        // in this operation. Thus, this statement is not assumption, it is
        // just a check move into precondition.

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_DevDeactivate_InnerFunc(ws, dev_sid)
        // Property: Correctness property for proving the commutative diagram

function {:axiom} WKD_ExternalObjsActivateToGreenPartition_Stub(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID
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

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
        // Property: Correctness property for proving the commutative diagram

function {:axiom} WKD_GreenExternalObjsDeactivate_Stub(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID
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

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
        // Property: Correctness property for proving the commutative diagram


// Activate multiple devices into the red partition
function {:axiom} WKD_MultiDevs_ReturnOS_Stub(
    ws:DM_State, to_assign_dev_ids:seq<Dev_ID>
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires forall i, j :: 0 <= i < |to_assign_dev_ids| && 0 <= j < |to_assign_dev_ids|
                ==> (i == j <==> to_assign_dev_ids[i] == to_assign_dev_ids[j])
        // Requirement: No duplicate device ID in <to_assign_dev_ids>
    requires forall id :: id in to_assign_dev_ids ==> id in ws.subjects.devs
    requires |to_assign_dev_ids| >= 0

    ensures var ws' := result.0;
            var ws_d := result.1;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            var ws_d := result.1;
            DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var ws' := result.0;
            var ws_d := result.1;
            ws_d == true ==> P_WSD_DevActivate_Multi_SubjObjModifications(ws, ws', SeqToSet(to_assign_dev_ids), ws.red_pid)

    ensures var ws' := result.0;
            var ws_d := result.1;
            P_WSD_DevActivate_Multi_ConditionForReturnTrue(ws, SeqToSet(to_assign_dev_ids), ws.red_pid) ==> ws_d


function {:axiom} WKD_ExternalObjsActivateToRedPartition_Stub(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    
    requires td_ids <= AllTDIDs(ws.objects)
    requires fd_ids <= AllFDIDs(ws.objects)
    requires do_ids <= AllDOIDs(ws.objects)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_ExternalObjsActivateToRedPartition_InnerFunc(ws, td_ids, fd_ids, do_ids)
        // Property: Correctness property for proving the commutative diagram

function {:axiom} WKD_RedExternalObjsDeactivate_Stub(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
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
        // Requirement: The objects must be in the same green partition

    requires P_RedDevsHaveNoTransferToGivenRedObjsAtAnyTime(ws, td_ids, fd_ids, do_ids)
        // Requirement: No red device has transfers to given objects

    ensures var ws' := result.0;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            (ws', ws_d) == DM_RedExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids)
        // Property: Correctness property for proving the commutative diagram