include "../DetailedModel/Model.dfy"
include "DM_AdditionalPropertiesLemmas.dfy"
include "Utils.i.dfy"
include "SecurityProperties.dfy"

//******** Wimpy Kernel Operations ********//
// Corresponding to DM_RedDrvRead in the detailed model
function WSD_OSDrvRead(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) : (result:(DM_Trace, DM_State, bool, map<TD_ID, TD_Val>)) // returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool, ghost real_td_id_val_map:map<TD_ID, TD_Val>)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid
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

    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            DM_IsSecureOps(ws, ws')

    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            t.ws0 == ws
    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            DM_IsValidTrace(t)
    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            P_WSD_OpsProperties(ws, WSD_OSDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            (ws', ws_d) == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    var t := DM_Trace(ws, [op]);
    var read_result := DM_RedDrvRead(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    var ws' := read_result.0;
    var ws_d := read_result.1;
    var real_td_id_val_map := read_result.2;

    
    if(ws_d) then
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
        Lemma_OSDrvRead_ProvePWSOpsProperties(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d);
        (t, ws', ws_d, real_td_id_val_map)
    else
        assert DM_CalcNewStates(t) == [ws, ws];
        assert WSD_OSDrvRead_PostConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d);
        (t, ws', ws_d, real_td_id_val_map)
}

// Corresponding to DM_GreenDrvRead in the detailed model
method WSD_WimpDrvRead(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WSD_WimpDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties
    
    ensures (ws', ws_d) == DM_GreenDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_GreenDrvRead(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_WimpDrvRead_ProvePWSOpsProperties(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d);
}

// Corresponding to DM_DevRead in the detailed model
method WSD_DevRead(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is active

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(ws, dev_sid, read_objs)
    requires DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, dev_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device
    ensures ws_d == true

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WSD_DevRead_Op(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_DevRead_InnerFunc(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_DevRead(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_DevRead_ProvePWSOpsProperties(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d);
}

// Corresponding to DM_RedDrvWrite in the detailed model
// [NOTE] Needs 150s to verify
function WSD_OSDrvWrite(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_Trace, DM_State, bool, map<TD_ID, TD_Val>)) // returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool, ghost real_td_id_val_map:map<TD_ID, TD_Val>)
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

    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            DM_IsSecureOps(ws, ws')

    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            ws_d == true
                ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            t.ws0 == ws
    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            DM_IsValidTrace(t)
    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            P_WSD_OpsProperties(ws, WSD_OSDrvWrite_Op(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures var t := result.0;
            var ws' := result.1;
            var ws_d := result.2;
            var real_td_id_val_map := result.3;
            ws' == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 &&
            ws_d == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var t := DM_Trace(ws, [op]);
    var write_result := DM_RedDrvWrite(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var ws' := write_result.0;
    var ws_d := write_result.1;
    var real_td_id_val_map := write_result.2;

    Lemma_OSDrvWrite_ProvePWSOpsProperties(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d);
    if(ws_d) then
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
        (t, ws', ws_d, real_td_id_val_map)
    else
        assert DM_CalcNewStates(t) == [ws, ws];
        (t, ws', ws_d, real_td_id_val_map)
}

// Corresponding to DM_GreenDrvWrite in the detailed model
method WSD_WimpDrvWrite(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WSD_WimpDrvWrite_Op(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_GreenDrvWrite(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_WimpDrvWrite_ProvePWSOpsProperties(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d);
}

// Corresponding to DM_RedDevWrite in the detailed model
method WSD_OSDevWrite(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))
        // Properties needed by the following properties
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device
    ensures ws_d == true

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WSD_OSDrvWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_RedDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_OSDevWrite_ProvePWSOpsProperties(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d);
}

// Corresponding to DM_GreenDevWrite in the detailed model
method WSD_WimpDevWrite(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))
        // Properties needed by the following property
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device
    ensures ws_d == true

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WSD_WimpDevWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_GreenDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_WimpDevWrite_ProvePWSOpsProperties(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d);
}

// Utility Method (not counted as an operation): Corresponding to DM_Green/RedDevWrite
method WSD_DevWrite(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))
        // Properties needed by the following property
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device
    ensures ws_d == true

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid
                ==> P_WSD_OpsProperties(ws, WSD_WimpDevWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    ensures DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid
                ==> P_WSD_OpsProperties(ws, WSD_OSDrvWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid
                ==> (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid
                ==> (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Correctness property for proving the commutative diagram
{
    if(DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid)
    {
        var r1, r2, r3 := WSD_WimpDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        return r1, r2, r3;
    }
    else
    {
        var r1, r2, r3 := WSD_OSDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        return r1, r2, r3;
    }
}

method WKD_EmptyPartitionCreate(
    ws:DM_State, 
    new_pid:Partition_ID // The ID of the new partition
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_EmptyPartitionCreateOp(new_pid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_EmptyPartitionCreate_InnerFunc(ws, new_pid)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_EmptyPartitionCreateOp(new_pid);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_EmptyPartitionCreate(ws, new_pid);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_EmptyPartitionCreate_ProvePWSOpsProperties(ws, new_pid, t, ws', ws_d);
}

method WKD_EmptyPartitionDestroy(
    ws:DM_State, 
    pid:Partition_ID // The ID of the new partition
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_EmptyPartitionDestroyOp(pid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_EmptyPartitionDestroy_InnerFunc(ws, pid)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_EmptyPartitionDestroyOp(pid);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_EmptyPartitionDestroy(ws, pid);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_EmptyPartitionDestroy_ProvePWSOpsProperties(ws, pid, t, ws', ws_d);
}

method WKD_DrvActivateToGreenPartition(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver to be activated
    green_pid:Partition_ID // ID of the partition to activate the driver into
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires green_pid != NULL
    requires green_pid != ws.red_pid
        // Requirement: the destination partition must be a green partition

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_DrvActivateToGreenPartitionOp(drv_sid, green_pid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_DrvActivateToGreenPartition(ws, drv_sid, green_pid);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_DrvActivateToGreenPartition_ProvePWSOpsProperties(ws, drv_sid, green_pid, t, ws', ws_d);
}

method WKD_GreenDrvDeactivate(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: The driver must be in a green partition

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_GreenDrvDeactivateOp(drv_sid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_GreenDrvDeactivateOp(drv_sid);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_GreenDrvDeactivate(ws, drv_sid);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_GreenDrvDeactivate_ProvePWSOpsProperties(ws, drv_sid, t, ws', ws_d);
}

method WKD_DevActivate(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device to be activated
    pid:Partition_ID // ID of the partition to activate the driver into
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires pid != NULL

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_DevActivateOp(dev_sid, pid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_DevActivate_InnerFunc(ws, dev_sid, pid)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_DevActivateOp(dev_sid, pid);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_DevActivate(ws, dev_sid, pid);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_DevActivate_ProvePWSOpsProperties(ws, dev_sid, pid, t, ws', ws_d);
}

method WKD_DevDeactivate(
    ws:DM_State, 
    dev_sid:Subject_ID // ID of the device to be activated
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_DevDeactivateOp(dev_sid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_DevDeactivate_InnerFunc(ws, dev_sid)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_DevDeactivateOp(dev_sid);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_DevDeactivate(ws, dev_sid);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_DevDeactivate_ProvePWSOpsProperties(ws, dev_sid, t, ws', ws_d);
}

method WKD_ExternalObjsActivateToGreenPartition(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_ExternalObjsActivateToGreenPartition(ws, td_ids, fd_ids, do_ids, green_pid);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_ExternalObjsActivateToGreenPartition_ProvePWSOpsProperties(ws, td_ids, fd_ids, do_ids, green_pid, t, ws', ws_d);
}

method WKD_ExternalObjsActivateToRedPartition(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    
    requires td_ids <= AllTDIDs(ws.objects)
    requires fd_ids <= AllFDIDs(ws.objects)
    requires do_ids <= AllDOIDs(ws.objects)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_ExternalObjsActivateToRedPartition_InnerFunc(ws, td_ids, fd_ids, do_ids)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_ExternalObjsActivateToRedPartition(ws, td_ids, fd_ids, do_ids);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_ExternalObjsActivateToRedPartition_ProvePWSOpsProperties(ws, td_ids, fd_ids, do_ids, t, ws', ws_d);
}

method WKD_GreenExternalObjsDeactivate(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid);
    t := DM_Trace(ws, [op]);
    assert DM_GreenExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid);
    assert P_DM_OpsFulfillPreConditions(ws, op);
    ws', ws_d := DM_GreenExternalObjsDeactivate(ws, td_ids, fd_ids, do_ids, green_pid);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_GreenExternalObjsDeactivate_ProvePWSOpsProperties(ws, td_ids, fd_ids, do_ids, green_pid, t, ws', ws_d);
}

method WKD_RedExternalObjsDeactivate(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures (ws', ws_d) == DM_RedExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids)
        // Property: Correctness property for proving the commutative diagram
{
    var op := DM_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids);
    t := DM_Trace(ws, [op]);
    assert DM_RedExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids);
    assert P_DM_OpsFulfillPreConditions(ws, op);
    ws', ws_d := DM_RedExternalObjsDeactivate(ws, td_ids, fd_ids, do_ids);

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_RedExternalObjsDeactivate_ProvePWSOpsProperties(ws, td_ids, fd_ids, do_ids, t, ws', ws_d);
}

// Activate multiple devices into the red partition
method WKD_MultiDevs_ReturnOS(
    ws:DM_State, to_assign_dev_ids:seq<Dev_ID>
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires forall i, j :: 0 <= i < |to_assign_dev_ids| && 0 <= j < |to_assign_dev_ids|
                ==> (i == j <==> to_assign_dev_ids[i] == to_assign_dev_ids[j])
        // Requirement: No duplicate device ID in <to_assign_dev_ids>
    requires forall id :: id in to_assign_dev_ids ==> id in ws.subjects.devs
    requires |to_assign_dev_ids| >= 0

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures ws_d == true ==> P_WSD_DevActivate_Multi_SubjObjModifications(ws, ws', SeqToSet(to_assign_dev_ids), ws.red_pid)
    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == DevActivateMulti_ToTraceOps(to_assign_dev_ids, ws.red_pid)
        // Property 2: <t> is the desired trace
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WKD_MultiDevs_ReturnOSOp(to_assign_dev_ids))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties

    ensures P_WSD_DevActivate_Multi_ConditionForReturnTrue(ws, SeqToSet(to_assign_dev_ids), ws.red_pid) ==> ws_d
{
    var ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;

    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();

    // Activate devices
    ghost var t1:DM_Trace;
    ghost var t1_detailed:DM_Trace_Detailed;
    t1, t1_detailed, ws2, d := WSD_DevActivate_Multi(ws, to_assign_dev_ids, ws.red_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_MultiDevs_ReturnOS_ProvePWSOpsProperties(ws, to_assign_dev_ids, t, ws', ws_d);
        return t, ws', ws_d;
    }

    ws' := ws2;
    t := t1;
    ws_d := true;

    Lemma_MultiDevs_ReturnOS_ProvePWSOpsProperties(ws, to_assign_dev_ids, t, ws', ws_d);
}





/*
// Create an empty wimp partition 
method WK_WimpDrvsDevs_Registration_CreatePartition(
    ws:DM_State
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool, green_pid:Partition_ID)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_EmptyPartitionCreateOp(green_pid)]
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws_d == true ==> green_pid != NULL
    ensures ws_d == true ==> green_pid != ws.red_pid
    ensures ws_d == true ==> green_pid !in ws.pids 
    ensures ws_d == true ==> green_pid in ws'.pids
        // Property: If returns true, then create a new wimp (green) partition

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WK_WimpDrvsDevs_Registration_CreatePartition_Op())
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties
{
    var last_ws:DM_State, new_last_ws:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;
    var new_pid := GetNewPartitionID(ws);

    // Create partition
    ghost var t1:DM_Trace := DM_Trace(ws, [DM_EmptyPartitionCreateOp(new_pid)]);
    new_last_ws, d := DM_EmptyPartitionCreate(ws, new_pid);
    if(!d)
    { return DM_Trace(ws, []), ws, false, ws.red_pid;}
    assert DM_IsValidTrace(t1);
    assert new_last_ws == SeqLastElem(DM_CalcNewStates(t1));
    assert P_DMState_UnchangedStateVarsAndFields(ws, new_last_ws);
    last_ws := new_last_ws;

    ws' := last_ws;
    t := t1;
    ws_d := true;
    green_pid := new_pid;

    Lemma_WimpDrvsDevs_Registration_CreatePartition_ProvePWSOpsProperties(ws, t, ws', ws_d);
}

// Move devices, and activate drivers and external objects into the given 
// wimp partition 
method WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs(
    ws:DM_State, to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires to_deactivate_dev_id in ws.subjects.devs
    requires DM_SubjPID(ws.subjects, to_deactivate_dev_id.sid) == ws.red_pid
    requires P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, to_deactivate_dev_id)
        // Requirement: For the device to be deactivated

    requires forall i, j :: 0 <= i < |to_assign_drv_ids| && 0 <= j < |to_assign_drv_ids|
                ==> (i == j <==> to_assign_drv_ids[i] == to_assign_drv_ids[j])
        // Requirement: No duplicate device ID in <to_assign_drv_ids>
    requires forall i, j :: 0 <= i < |to_assign_dev_ids| && 0 <= j < |to_assign_dev_ids|
                ==> (i == j <==> to_assign_dev_ids[i] == to_assign_dev_ids[j])
        // Requirement: No duplicate device ID in <to_assign_dev_ids>
    requires forall id :: id in to_assign_drv_ids ==> id in ws.subjects.drvs
    requires |to_assign_drv_ids| >= 0
    requires forall id :: id in to_assign_dev_ids ==> id in ws.subjects.devs
    requires |to_assign_dev_ids| >= 0

    requires to_assign_external_td_ids <= DM_AllTDIDs(ws.objects)
    requires to_assign_external_fd_ids <= DM_AllFDIDs(ws.objects)
    requires to_assign_external_do_ids <= DM_AllDOIDs(ws.objects)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: We have already create a green partition

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_DevDeactivateOp(to_deactivate_dev_id.sid)] + DevActivateMulti_ToTraceOps(to_assign_dev_ids, green_pid) +
                                    WimpDrvActivateMulti_ToTraceOps(to_assign_drv_ids, green_pid) + 
                                    [DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid)]
        // Property 2: <t> is the desired trace
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op(to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties
{
    var ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;

    // Deactivate device
    ghost var t1:DM_Trace := DM_Trace(ws, [DM_DevDeactivateOp(to_deactivate_dev_id.sid)]);
    ws2, d := DM_DevDeactivate(ws, to_deactivate_dev_id.sid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
            to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    assert DM_IsValidTrace(t1);
    assert ws2 == SeqLastElem(DM_CalcNewStates(t1));
    assert P_DMState_UnchangedStateVarsAndFields(ws, ws2);

    // Activate devices
    ghost var t2:DM_Trace;
    ghost var t2_detailed:DM_Trace_Detailed;
    t2, t2_detailed, ws3, d := WSD_DevActivate_Multi(ws2, to_assign_dev_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
            to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    ghost var t1_t2 := ValidDMTrace_Concat(t1, t2);
    Lemma_WSD_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t2_detailed.states, ws2, ws3);
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws2, ws3);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws2, ws3, t1, t2);
    assert ws3 == SeqLastElem(DM_CalcNewStates(t1_t2));

    // Activate drivers
    ghost var t3:DM_Trace;
    ghost var t3_detailed:DM_Trace_Detailed;
    t3, t3_detailed, ws4, d := WSD_WimpDrvActivate_Multi(ws3, to_assign_drv_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
            to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    Lemma_WSD_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t3_detailed.states, ws3, ws4);
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws3, ws4);
    
    // Activate external objects
    assert DM_IsValidState(ws4) && DM_IsSecureState(ws4);
    assert P_DMState_UnchangedStateVarsAndFields(ws, ws4);
    Lemma_ExternalObjsActivateDeactivate_ProvePreConditions(ws, ws4, to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids);

    var op4 := DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid);
    ghost var t4:DM_Trace := DM_Trace(ws4, [op4]);
    ws5, d := DM_ExternalObjsActivateToGreenPartition(ws4, to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
            to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    Lemma_WK_WimpDrvsDevs_Registration_ProveValidTrace_AfterActivateExternalObjsToGreenPartition(
        ws4, t4, to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid);
    assert DM_IsValidTrace(t4);
    ghost var t3_t4 := ValidDMTrace_Concat(t3, t4);
    Lemma_DM_CalcNewStates_OneDMOp_Property(ws4, op4, ws5);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws3, ws4, ws5, t3, t4);
    assert ws5 == SeqLastElem(DM_CalcNewStates(t3_t4));

    ws' := ws5;
    t := ValidDMTrace_Concat(t1_t2, t3_t4);
    ws_d := true;

    // Prove property 2
    var seq1 := [DM_DevDeactivateOp(to_deactivate_dev_id.sid)];
    var seq2 := DevActivateMulti_ToTraceOps(to_assign_dev_ids, green_pid);
    var seq3 := WimpDrvActivateMulti_ToTraceOps(to_assign_drv_ids, green_pid);
    var seq4 := [DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid)];

    Lemma_DMTraceConcat_IsConcatOfDMOps(t1_t2, t1, t2, seq1, seq2);
    Lemma_DMTraceConcat_IsConcatOfDMOps(t3_t4, t3, t4, seq3, seq4);
    assert t1_t2.ops == seq1 + seq2;
    assert t3_t4.ops == seq3 + seq4;

    Lemma_ConcatFourOpSeq(t1_t2, t3_t4, t, seq1, seq2, seq3, seq4); 
    assert t.ops == seq1 + seq2 + seq3 + seq4;

    // Prove ws' == SeqLastElem(DM_CalcNewStates(t))
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws3, ws', t1_t2, t3_t4);
    assert ws' == SeqLastElem(DM_CalcNewStates(t));
    
    // Prove DM_IsSecureOps(ws, ws')
    Lemma_WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProveSameTransitionContraintOverInputAndOutputState(
        ws, ws2, ws3, ws4, ws5,
        to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
        to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid);

    Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
        to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
}

// Move devices, and deactivate wimp drivers and external objects out of the 
// given wimp partition, and then destroy the partition
// (needs 60s to verify)
method WK_WimpDrvsDevs_Unregistration(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires forall i, j :: 0 <= i < |to_deactivate_drv_ids| && 0 <= j < |to_deactivate_drv_ids|
                ==> (i == j <==> to_deactivate_drv_ids[i] == to_deactivate_drv_ids[j])
        // Requirement: No duplicate device ID in <to_deactivate_drv_ids>
    requires forall i, j :: 0 <= i < |to_deactivate_dev_ids| && 0 <= j < |to_deactivate_dev_ids|
                ==> (i == j <==> to_deactivate_dev_ids[i] == to_deactivate_dev_ids[j])
        // Requirement: No duplicate device ID in <to_deactivate_dev_ids>
    requires forall id :: id in to_deactivate_drv_ids ==> id in ws.subjects.drvs
    requires |to_deactivate_drv_ids| >= 0
    requires forall id :: id in to_deactivate_dev_ids ==> id in ws.subjects.devs
    requires |to_deactivate_dev_ids| >= 0

    requires forall id :: id in to_deactivate_drv_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid
    requires forall id :: id in to_deactivate_dev_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid
        // Requirement: Drivers and devices to be deactivated must be from the 
        // green partition

    requires forall i, j :: 0 <= i < |devs_to_activate_in_red| && 0 <= j < |devs_to_activate_in_red|
                ==> (i == j <==> devs_to_activate_in_red[i] == devs_to_activate_in_red[j])
        // Requirement: No duplicate device ID in <devs_to_activate_in_red>
    requires forall id :: id in devs_to_activate_in_red ==> id in ws.subjects.devs
    requires |devs_to_activate_in_red| >= 0
        // Requirement: Devices to be activated in the red partition must be 
        // existing devices

    requires to_deactivate_external_td_ids <= DM_AllTDIDs(ws.objects)
    requires to_deactivate_external_fd_ids <= DM_AllFDIDs(ws.objects)
    requires to_deactivate_external_do_ids <= DM_AllDOIDs(ws.objects)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_deactivate_external_td_ids) + FDIDsToObjIDs(to_deactivate_external_fd_ids) + DOIDsToObjIDs(to_deactivate_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
    requires forall id :: id in to_deactivate_external_td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in to_deactivate_external_fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in to_deactivate_external_do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
        // Requirement: External objects to be deactivated must be from the 
        // green partition

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: A green partition to be destroyed

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws') 

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)] +
                                WimpDrvDeactivateMulti_ToTraceOps(to_deactivate_drv_ids) +
                                GreenDevDeactivateMulti_ToTraceOps(to_deactivate_dev_ids) +
                                DevActivateMulti_ToTraceOps(devs_to_activate_in_red, ws.red_pid) +
                                [DM_EmptyPartitionDestroyOp(green_pid)]
                                
        // Property 2: <t> is the desired trace
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures P_WSD_OpsProperties(ws, WK_WimpDrvsDevs_Unregistration_Op(to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid))
        // Property: The implemetation of this operation fulfills the specification of P_WSD_OpsProperties
{
    var ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;

    // Call WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs
    ghost var t1:DM_Trace;
    t1, ws2, d := WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                    to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Unregistration_ProvePWSOpsProperties(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
            to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
            green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    assert DM_IsValidTrace(t1);
    assert ws2 == SeqLastElem(DM_CalcNewStates(t1));

    // Call WK_WimpDrvsDevs_UnRegistration_DestroyPartition
    ghost var t2:DM_Trace;
    t2, ws3, d := WK_WimpDrvsDevs_UnRegistration_DestroyPartition(ws2, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Unregistration_ProvePWSOpsProperties(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
            to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
            green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    ghost var t1_t2 := ValidDMTrace_Concat(t1, t2);
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws2, ws3);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws2, ws3, t1, t2);
    assert ws3 == SeqLastElem(DM_CalcNewStates(t1_t2));

    ws' := ws3;
    t := t1_t2;
    ws_d := true;
    
    Lemma_WimpDrvsDevs_Unregistration_ProvePWSOpsProperties(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
        to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
        green_pid, t, ws', ws_d);
} */




//******** Utility functions ********//
// Get the partition ID to be associated with the newly created partition
method {:axiom} GetNewPartitionID(ws:DM_State) returns (new_pid:Partition_ID)
    ensures new_pid != NULL
    ensures new_pid != ws.red_pid
    ensures new_pid !in ws.pids




//******** Utility Operations ********//
/*
// (needs 70s to verify)
method WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires forall i, j :: 0 <= i < |to_deactivate_drv_ids| && 0 <= j < |to_deactivate_drv_ids|
                ==> (i == j <==> to_deactivate_drv_ids[i] == to_deactivate_drv_ids[j])
        // Requirement: No duplicate device ID in <to_deactivate_drv_ids>
    requires forall i, j :: 0 <= i < |to_deactivate_dev_ids| && 0 <= j < |to_deactivate_dev_ids|
                ==> (i == j <==> to_deactivate_dev_ids[i] == to_deactivate_dev_ids[j])
        // Requirement: No duplicate device ID in <to_deactivate_dev_ids>
    requires forall id :: id in to_deactivate_drv_ids ==> id in ws.subjects.drvs
    requires |to_deactivate_drv_ids| >= 0
    requires forall id :: id in to_deactivate_dev_ids ==> id in ws.subjects.devs
    requires |to_deactivate_dev_ids| >= 0

    requires forall id :: id in to_deactivate_drv_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid
    requires forall id :: id in to_deactivate_dev_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid
        // Requirement: Drivers and devices to be deactivated must be from the 
        // green partition

    requires forall i, j :: 0 <= i < |devs_to_activate_in_red| && 0 <= j < |devs_to_activate_in_red|
                ==> (i == j <==> devs_to_activate_in_red[i] == devs_to_activate_in_red[j])
        // Requirement: No duplicate device ID in <devs_to_activate_in_red>
    requires forall id :: id in devs_to_activate_in_red ==> id in ws.subjects.devs
    requires |devs_to_activate_in_red| >= 0
        // Requirement: Devices to be activated in the red partition must be 
        // existing devices

    requires to_deactivate_external_td_ids <= DM_AllTDIDs(ws.objects)
    requires to_deactivate_external_fd_ids <= DM_AllFDIDs(ws.objects)
    requires to_deactivate_external_do_ids <= DM_AllDOIDs(ws.objects)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_deactivate_external_td_ids) + FDIDsToObjIDs(to_deactivate_external_fd_ids) + DOIDsToObjIDs(to_deactivate_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
    requires forall id :: id in to_deactivate_external_td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in to_deactivate_external_fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in to_deactivate_external_do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
        // Requirement: External objects to be deactivated must be from the 
        // green partition

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: A green partition to be destroyed

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws') 

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)] +
                                WimpDrvDeactivateMulti_ToTraceOps(to_deactivate_drv_ids) +
                                GreenDevDeactivateMulti_ToTraceOps(to_deactivate_dev_ids) +
                                DevActivateMulti_ToTraceOps(devs_to_activate_in_red, ws.red_pid)
        // Property 2: <t> is the desired trace
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures ws'.pids == ws.pids
        // Utility properties needed by <WK_WimpDrvsDevs_Unregistration>
{
    var ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;

    // Deactivate external objects
    ghost var t1:DM_Trace := DM_Trace(ws, [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)]);
    ws2, d := DM_GreenExternalObjsDeactivate(ws, to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        return t, ws', ws_d;
    }
    assert DM_IsValidTrace(t1);
    assert ws2 == SeqLastElem(DM_CalcNewStates(t1));
    assert ws2.pids == ws.pids;

    // Deactivate drivers
    ghost var t2:DM_Trace;
    ghost var t2_detailed:DM_Trace_Detailed;
    t2, t2_detailed, ws3, d := WSD_WimpDrvDeactivate_Multi(ws2, to_deactivate_drv_ids);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        return t, ws', ws_d;
    }
    ghost var t1_t2 := ValidDMTrace_Concat(t1, t2);
    Lemma_WSD_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t2_detailed.states, ws2, ws3);
    assert ws3.pids == ws2.pids; 
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws2, ws3);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws2, ws3, t1, t2);
    assert ws3 == SeqLastElem(DM_CalcNewStates(t1_t2));

    // Deactivate devices
    ghost var t3:DM_Trace;
    ghost var t3_detailed:DM_Trace_Detailed;
    t3, t3_detailed, ws4, d := WSD_DevDeactivate_FromGreen_Multi(ws3, to_deactivate_dev_ids); 
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        return t, ws', ws_d;
    }
    assert SeqLastElem(t3_detailed.states) == ws4;
    assert t3_detailed.states[|t3_detailed.states|-1] == ws4;
    Lemma_WSD_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t3_detailed.states, ws3, ws4);
    assert ws4.pids == ws3.pids;
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws3, ws4);

    // Activate devices
    ghost var t4:DM_Trace;
    ghost var t4_detailed:DM_Trace_Detailed;
    t4, t4_detailed, ws5, d := WSD_DevActivate_Multi(ws4, devs_to_activate_in_red, ws.red_pid); 
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        return t, ws', ws_d;
    }
    ghost var t3_t4 := ValidDMTrace_Concat(t3, t4);
    assert SeqLastElem(t4_detailed.states) == ws5;
    assert t4_detailed.states[|t4_detailed.states|-1] == ws5;
    Lemma_WSD_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t4_detailed.states, ws4, ws5);
    assert ws5.pids == ws4.pids;
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws4, ws5);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws3, ws4, ws5, t3, t4);
    assert ws5 == SeqLastElem(DM_CalcNewStates(t3_t4));

    ws' := ws5;
    t := ValidDMTrace_Concat(t1_t2, t3_t4);
    ws_d := true;

    // Prove property 2
    var seq1 := [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)];
    var seq2 := WimpDrvDeactivateMulti_ToTraceOps(to_deactivate_drv_ids);
    var seq3 := GreenDevDeactivateMulti_ToTraceOps(to_deactivate_dev_ids);
    var seq4 := DevActivateMulti_ToTraceOps(devs_to_activate_in_red, ws.red_pid);

    Lemma_DMTraceConcat_IsConcatOfDMOps(t1_t2, t1, t2, seq1, seq2);
    Lemma_DMTraceConcat_IsConcatOfDMOps(t3_t4, t3, t4, seq3, seq4);
    assert t1_t2.ops == seq1 + seq2;
    assert t3_t4.ops == seq3 + seq4;
    Lemma_ConcatFourOpSeq(t1_t2, t3_t4, t, seq1, seq2, seq3, seq4); 
    assert t.ops == seq1 + seq2 + seq3 + seq4;

    // Prove ws' == SeqLastElem(DM_CalcNewStates(t))
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws3, ws', t1_t2, t3_t4);
    assert ws' == SeqLastElem(DM_CalcNewStates(t));

    // Prove DM_IsSecureOps(ws, ws')
    Lemma_WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs_ProveSameTransitionContraintOverInputAndOutputState(
        ws, ws2, ws3, ws4, ws5,
        to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red, 
        to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
        green_pid);
        
    // Prove ws'.pids == ws.pids
    assert ws2.pids == ws.pids;
    assert ws3.pids == ws2.pids;
    assert ws4.pids == ws3.pids;
    assert ws5.pids == ws4.pids;
    assert ws' == ws5;
    Lemma_WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs_ProvePIDsAreUnchanged(
        ws, ws2, ws3, ws4, ws5, ws');
    assert ws'.pids == ws.pids;
}

method WK_WimpDrvsDevs_UnRegistration_DestroyPartition(
    ws:DM_State, green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: A green partition to be destroyed

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_EmptyPartitionDestroyOp(green_pid)]
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws_d == true ==> green_pid !in ws'.pids
        // Property: If returns true, then destroy the green partition

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
        // [NOTE] These properties defines the commutative diagram in model instantiation. Each ops in the sound WK 
        // design maps to a sequence of ops in the concrete model.
    ensures ws'.subjects == ws.subjects
    ensures ws'.objects == ws.objects
        // Utility properties needed by <WK_WimpDrvsDevs_Unregistration>
{
    var last_ws:DM_State, new_last_ws:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;

    // Destroy partition
    ghost var t1:DM_Trace := DM_Trace(ws, [DM_EmptyPartitionDestroyOp(green_pid)]);
    new_last_ws, d := DM_EmptyPartitionDestroy(ws, green_pid);
    if(!d)
    { 
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        return t, ws', ws_d;
    }
    assert DM_IsValidTrace(t1);
    assert new_last_ws == SeqLastElem(DM_CalcNewStates(t1));
    assert P_DMState_UnchangedStateVarsAndFields(ws, new_last_ws);
    last_ws := new_last_ws;

    ws' := last_ws;
    t := t1;
    ws_d := true;
}
*/



//******** Utility Lemmas ********//
lemma Lemma_OSDrvRead_ProvePWSOpsProperties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>, // Map from destination DO to source DO
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_OSDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires WSD_OSDrvRead_PostConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WSD_OSDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvRead_ProvePWSOpsProperties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>, // Map from destination DO to source DO
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_WimpDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires WSD_WimpDrvRead_PostConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WSD_WimpDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevRead_ProvePWSOpsProperties(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>, // Map from destination DO to source DO
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_DevRead_PreConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires WSD_DevRead_PostConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WSD_DevRead_Op(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_OSDrvWrite_ProvePWSOpsProperties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>, // IDs of DOs, and values to be written
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_OSDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires WSD_OSDrvWrite_PostConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WSD_OSDrvWrite_Op(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvWrite_ProvePWSOpsProperties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>, // IDs of DOs, and values to be written
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_WimpDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires WSD_WimpDrvWrite_PostConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WSD_WimpDrvWrite_Op(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_OSDevWrite_ProvePWSOpsProperties(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>, // IDs of DOs, and values to be written
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_OSDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires WSD_OSDevWrite_PostConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WSD_OSDevWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDevWrite_ProvePWSOpsProperties(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>, // IDs of DOs, and values to be written
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_WimpDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires WSD_WimpDevWrite_PostConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WSD_WimpDevWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_EmptyPartitionCreate_ProvePWSOpsProperties(
    ws:DM_State, 
    new_pid:Partition_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_EmptyPartitionCreate_PreConditions(ws, new_pid)
    requires WKD_EmptyPartitionCreate_PostConditions(ws, new_pid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_EmptyPartitionCreateOp(new_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_EmptyPartitionDestroy_ProvePWSOpsProperties(
    ws:DM_State, 
    pid:Partition_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_EmptyPartitionDestroy_PreConditions(ws, pid)
    requires WKD_EmptyPartitionDestroy_PostConditions(ws, pid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_EmptyPartitionDestroyOp(pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvActivateToGreenPartition_ProvePWSOpsProperties(
    ws:DM_State,
    drv_sid:Subject_ID, 
    green_pid:Partition_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_DrvActivateToGreenPartition_PreConditions(ws, drv_sid, green_pid)
    requires WKD_DrvActivateToGreenPartition_PostConditions(ws, drv_sid, green_pid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_DrvActivateToGreenPartitionOp(drv_sid, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_GreenDrvDeactivate_ProvePWSOpsProperties(
    ws:DM_State, 
    drv_sid:Subject_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_GreenDrvDeactivate_PreConditions(ws, drv_sid)
    requires WKD_GreenDrvDeactivate_PostConditions(ws, drv_sid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_GreenDrvDeactivateOp(drv_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevActivate_ProvePWSOpsProperties(
    ws:DM_State,
    dev_sid:Subject_ID, 
    pid:Partition_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_DevActivate_PreConditions(ws, dev_sid, pid)
    requires WKD_DevActivate_PostConditions(ws, dev_sid, pid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_DevActivateOp(dev_sid, pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_ProvePWSOpsProperties(
    ws:DM_State,
    dev_sid:Subject_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_DevDeactivate_PreConditions(ws, dev_sid)
    requires WKD_DevDeactivate_PostConditions(ws, dev_sid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_DevDeactivateOp(dev_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ExternalObjsActivateToGreenPartition_ProvePWSOpsProperties(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_ExternalObjsActivateToGreenPartition_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)
    requires WKD_ExternalObjsActivateToGreenPartition_PostConditions(ws, td_ids, fd_ids, do_ids, green_pid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ExternalObjsActivateToRedPartition_ProvePWSOpsProperties(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_ExternalObjsActivateToRedPartition_PreConditions(ws, td_ids, fd_ids, do_ids)
    requires WKD_ExternalObjsActivateToRedPartition_PostConditions(ws, td_ids, fd_ids, do_ids, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_GreenExternalObjsDeactivate_ProvePWSOpsProperties(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_GreenExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)
    requires WKD_GreenExternalObjsDeactivate_PostConditions(ws, td_ids, fd_ids, do_ids, green_pid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_RedExternalObjsDeactivate_ProvePWSOpsProperties(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_RedExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids)
    requires WKD_RedExternalObjsDeactivate_PostConditions(ws, td_ids, fd_ids, do_ids, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_MultiDevs_ReturnOS_ProvePWSOpsProperties(
    ws:DM_State, to_assign_dev_ids:seq<Dev_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_MultiDevs_ReturnOS_PreConditions(ws, to_assign_dev_ids)
    requires WKD_MultiDevs_ReturnOS_PostConditions(ws, to_assign_dev_ids, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WKD_MultiDevs_ReturnOSOp(to_assign_dev_ids))
{
    // Dafny can automatically prove this lemma
}

/*
lemma Lemma_WimpDrvsDevs_Registration_CreatePartition_ProvePWSOpsProperties(
    ws:DM_State,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Registration_CreatePartition_PreConditions(ws)
    requires WK_WimpDrvsDevs_Registration_CreatePartition_PostConditions(ws, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WK_WimpDrvsDevs_Registration_CreatePartition_Op())
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(
    ws:DM_State, to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PreConditions(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids,
                green_pid)
    requires WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PostConditions(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids,
                green_pid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op(to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvsDevs_Unregistration_ProvePWSOpsProperties(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Unregistration_PreConditions(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
                green_pid)
    requires WK_WimpDrvsDevs_Unregistration_PostConditions(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
                green_pid, t, ws', ws_d)
    
    ensures P_WSD_OpsProperties(ws, WK_WimpDrvsDevs_Unregistration_Op(to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs_ProvePIDsAreUnchanged(
    ws:DM_State, ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State, ws':DM_State
)
    requires ws2.pids == ws.pids
    requires ws3.pids == ws2.pids
    requires ws4.pids == ws3.pids
    requires ws5.pids == ws4.pids
    requires ws' == ws5
    
    ensures ws'.pids == ws.pids
{
    // Dafny can automatically prove this lemma
}
*/