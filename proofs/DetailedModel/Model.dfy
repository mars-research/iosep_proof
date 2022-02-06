include "Model_Ops_Predicates.dfy"
include "K_Operations_Stubs.dfy"
include "Model_InnerFuncs.dfy"
include "Lemmas_Ops_SubjRead.dfy"
include "Lemmas_Ops_SubjWrite.dfy"
include "Lemmas_Ops_SubjObjActivate.dfy"
include "Lemmas_Ops_SubjObjDeactivate.dfy"
include "Lemmas_Ops_GreenDrvWrite_SI1.dfy"
include "Lemmas_Model_InnerFuncs.dfy"

// [TODO] Operations in Dafny method should be defined in Dafny functions

//******** DrvRead/DevRead ********//
// Operation: Driver in the red partition reads a set of objects, and copies 
// the values if needed
// [NOTE] Needs 260s to verify
function DM_RedDrvRead(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) : (result:(DM_State, bool, map<TD_ID, TD_Val>)) // returns (ws':DM_State, ws_d:bool, ghost real_td_id_val_map:map<TD_ID, TD_Val>)
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

    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            DM_IsSecureOps(ws, ws')
    
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            (ws', ws_d) == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            P_DM_OpsProperties(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            DM_CalcNewState(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            var k := DMStateToState(ws);
            (ws_d == true 
                ==> (forall id :: id in real_td_id_val_map ==> id in k.objects.active_non_hcoded_tds) &&
                    (forall id :: id in fds_dst_src ==> id in k.objects.active_fds) &&
                    (forall id :: id in dos_dst_src ==> id in k.objects.active_dos))
        // Properties needed by the following properties
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), 
                                real_td_id_val_map, 
                                DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src),
                                DMStateToState(ws'))

    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), 
                                    real_td_id_val_map, 
                                    DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)
                                ) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    if( forall o_id :: o_id in read_objs ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, o_id)) then
        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, drv_sid, read_objs);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);
        var drvwrite_result := DM_RedDrvWrite(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        var ws' := drvwrite_result.0;
        var ws_d := drvwrite_result.1;
        var real_td_id_val_map := drvwrite_result.2;
        
        if(ws_d) then
            // Prove DM_CalcNewState() == (ws', ws_d)
            Lemma_DM_RedDrvRead_ProveFunctionCorrectness_WhenRedDrvWriteReturnTrue(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', real_td_id_val_map);
            Lemma_DM_RedDrvRead_ProvePreConditionsOfDM_CalcNewState(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
            ghost var result1 := DM_CalcNewState(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
            assert result1 == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
            assert result1 == (ws', ws_d);

            (ws', ws_d, real_td_id_val_map)
        else
            assert ws_d == false;
            assert ws' == ws;
            
            Lemma_DM_RedDrvRead_ProveFunctionCorrectness_WhenRedDrvWriteReturnFalse(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws');
            Lemma_DM_RedDrvRead_ProveDM_CalcNewState(
                ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);

            (ws', ws_d, real_td_id_val_map)
    else
        var ws' := ws;
        var ws_d := false;
        Lemma_DM_RedDrvRead_ProveFalseCase(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);

        (ws', ws_d, map[])
}

// Operation: Driver in a green partition reads a set of objects, and copies 
// the values if needed
// [NOTE] Needs 330s to verify
method DM_GreenDrvRead(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')
    
    ensures ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    ensures (ws', ws_d) == DM_GreenDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    ensures P_DM_OpsProperties(ws, DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
    ensures DM_CalcNewState(ws, DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state
    
    ensures IsValidState(DMStateToState(ws)) 
    ensures ws_d == true ==> P_DrvRead_ReturnTrue_Def(DMStateToState(ws), drv_sid, 
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property: DrvRead in the abstract model returns true
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), 
                                DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src),
                                DMStateToState(ws'))
    
    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), 
                                    DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)
                                ) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvRead in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    if( forall o_id :: o_id in read_objs ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, o_id))
    {
        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, drv_sid, read_objs);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);
        ws', ws_d := DM_GreenDrvWrite(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

        if(ws_d)
        {
            assert P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

            Lemma_K_P_DrvRead_ReturnTrue_Def_Prove(k, drv_sid, read_objs, 
                tds_dst_src, fds_dst_src, dos_dst_src,
                td_id_val_map, fd_id_val_map, do_id_val_map);
            assert P_DrvRead_ReturnTrue_Def(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);

            // Prove DM_CalcNewState() == (ws', ws_d)
            Lemma_DM_GreenDrvRead_ProvePreConditionsOfDM_CalcNewState(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
            ghost var result1 := DM_CalcNewState(ws, DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
            assert result1 == DM_GreenDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
            assert result1 == (ws', ws_d);
        }
        else
        {
            assert ws_d == false;
            assert ws' == ws;
            
            Lemma_DM_GreenDrvRead_ProveDM_CalcNewState(
                ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
        }
    }
    else
    {
        ws' := ws;
        ws_d := false;

        Lemma_DM_GreenDrvRead_ProveDM_CalcNewState(
                ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
    }
}

// Operation: Device reads a set of objects, and copies the values if needed.
// The device could be in the red partition, or a green partition.
// (needs 130s to verify)
method DM_DevRead(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is active

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(ws, dev_sid, read_objs)
    requires DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')
    
    ensures ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, dev_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device

    ensures (ws', ws_d) == DM_DevRead_InnerFunc(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    ensures P_DM_OpsProperties(ws, DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
    ensures DM_CalcNewState(ws, DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures ws_d == true
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), 
                                DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src),
                                DMStateToState(ws'))
        
    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), 
                                    DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)
                              ) == DMStateToState(ws'))
        // Property: Commutative diagram to DevRead in the abstract model
        // [NOTE] This is because DevRead in the abstract model (always) returns
        // true, and DevRead modifies state as specified in DrvDevWrite_Func
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Dev_ID(dev_sid) in k.subjects.devs;

    var dev_id := Dev_ID(dev_sid);
    {
        var k', d := DevRead(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
        assert d == true;

        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, dev_sid, read_objs);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);

        if(DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid)
        {
            // If the device is in the red partition
            ws', ws_d := DM_RedDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);       
        }
        else
        {
            // If the device is in a green partition
            ws', ws_d := DM_GreenDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        }
        assert ws_d == true;
        
        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_DevRead_ProvePreConditionsOfDM_CalcNewState(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
        assert result1 == DM_DevRead_InnerFunc(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
        assert result1 == (ws', ws_d);
    }
}




//******** DrvWrite/DevWrite ********//
// Operation: Driver in the red partition writes a set of objects with values
// [NOTE] Need 260s to verify
function DM_RedDrvWrite(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool, map<TD_ID, TD_Val>)) //returns (ws':DM_State, ws_d:bool, ghost real_td_id_val_map:map<TD_ID, TD_Val>)
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

    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            DM_IsSecureOps(ws, ws')

    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            ws' == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            ws_d == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            P_DM_OpsProperties(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            DM_CalcNewState(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state
    
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            var k := DMStateToState(ws);
            (ws_d == true 
                ==> (forall id :: id in td_id_val_map ==> id in k.objects.active_non_hcoded_tds) &&
                    (forall id :: id in fd_id_val_map ==> id in k.objects.active_fds) &&
                    (forall id :: id in do_id_val_map ==> id in k.objects.active_dos))
        // Properties needed by the following properties
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            ws_d == true
                ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            ws_d == true ==> (forall td_id2 :: td_id2 in real_td_id_val_map ==> td_id2 in DMStateToState(ws).objects.active_non_hcoded_tds)
        // Property needed by the properties below
    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), real_td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))

    ensures var ws' := result.0;
            var ws_d := result.1;
            var real_td_id_val_map := result.2;
            (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), real_td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Drv_ID(drv_sid) in k.subjects.drvs;

    var drv_id := Drv_ID(drv_sid);

    var result := DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var in_ws' := result.0;
    var ws' := result.1;
    var ws_d := result.2;
    if(ws_d) then
        // Prove DM_IsValidState(ws')
        assert DevHWProt_ReturnGoodSnapshotOfRedTDs(in_ws', ws');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        assert P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_SubjsPIDsRedPID(in_ws', ws');
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(in_ws', ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState_SI2(ws')
        Lemma_NewDM_RedDrvWrite_SameDMAllActiveGreenUSBTDs(ws, in_ws', ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_RedDrvWrite_CommonValidityPropertiesOfNewDM_AndUnchangedPIDsOfGreenFDsDOs(ws, in_ws', ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', DMStateToState(ws'));
        assert DM_IsSecureState_SI2(ws');

        // Prove DM_IsSecureState_SI3(ws')
        Lemma_NewDM_RedDrvWrite_SameDMAllObjsIDsAndObjPIDs(ws, in_ws', ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_DrvWrite_NewDM_FulfillSI3(ws, ws');

        // Prove DM_IsSecureState(ws')
        assert DM_IsSecureState_SI1(ws');        
        assert DM_IsSecureState(ws');

        // Prove k' == DMStateToState(ws')
        var ws_k' := DMStateToState(ws');
        Lemma_DMStateToState_SecureK(ws', ws_k');
        assert IsValidState(ws_k') && IsSecureState(ws_k');
        //// Calculate actual <td_id_val_map>, <fd_id_val_map>, <do_id_val_map> written
        var td_id_val_map2 := TDsStateDiff(TDStateToTDVal(ws'.objects.active_non_hcoded_tds), TDStateToTDVal(ws.objects.active_non_hcoded_tds));
        Lemma_NewDM_RedDrvWrite_MappedStateOfNewDMIsProposedWriteResultOfMappedStateOfDM(ws, in_ws', ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert ws_k' == DrvWrite_ProposedNewState(k, td_id_val_map2, fd_id_val_map, do_id_val_map);
        //// Prove k' == DMStateToState(ws')
        Lemma_RedDrvWrite_PIDsOfAllTDsInTDDValMap2AreUnmodified(ws, k, in_ws', ws', drv_sid, td_id_val_map, td_id_val_map2, fd_id_val_map, do_id_val_map);
        Lemma_RedDrvWrite_ProveP_DrvWrite_ReturnTrue_Def(k, ws_k', drv_sid, td_id_val_map2, fd_id_val_map, do_id_val_map);
        var drvwrite_result := DrvWrite_Stub(k, drv_sid, td_id_val_map2, fd_id_val_map, do_id_val_map);
        var k' := drvwrite_result.0;
        var d := drvwrite_result.1;
        assert d == true;
        Lemma_DM_RedDrvWrite_ProveNewWSMapsToNewK_IfReturnTrue(k, ws', drv_sid, td_id_val_map2, fd_id_val_map, do_id_val_map);
        assert k' == DMStateToState(ws');

        var real_td_id_val_map := td_id_val_map2;
        Lemma_DrvDevWrite_Func_Prove(k, k', td_id_val_map2, fd_id_val_map, do_id_val_map);

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_RedDrvWrite_ProvePreConditionsOfDM_CalcNewState(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
        assert result1 == (DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1, 
                           DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2);
        assert result1 == (ws', ws_d);

        (ws', ws_d, real_td_id_val_map)
    else
        assert ws' == ws;
        assert ws_d == false;
        var real_td_id_val_map := td_id_val_map;

        assert DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert DM_RedDrvWrite_PostConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        assert ws' == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1;
        assert ws_d == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2;

        Lemma_DM_RedDrvWrite_ProveFalseCase(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert DM_CalcNewState(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws', ws_d);

        (ws', ws_d, real_td_id_val_map)
}

// Operation: Driver in a green partition writes a set of objects with values
// [NOTE] Needs 400s to verify
method DM_GreenDrvWrite(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures P_DM_OpsProperties(ws, DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    ensures DM_CalcNewState(ws, DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures var k := DMStateToState(ws);
            (ws_d == true 
                ==> (forall id :: id in td_id_val_map ==> id in k.objects.active_non_hcoded_tds) &&
                    (forall id :: id in fd_id_val_map ==> id in k.objects.active_fds) &&
                    (forall id :: id in do_id_val_map ==> id in k.objects.active_dos))
        // Properties needed by the following properties
    ensures ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver
    ensures IsValidState(DMStateToState(ws))
    ensures ws_d == true ==> P_DrvWrite_ReturnTrue_Def(DMStateToState(ws), drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: DrvWrite in the abstract model returns true

    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))

    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Drv_ID(drv_sid) in k.subjects.drvs;

    var drv_id := Drv_ID(drv_sid);

    var result := DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    ws' := result.0;
    ws_d := result.1;
    if(ws_d)
    {
        // Construct ws'.objects
        var t_objs1 := WriteActiveNonHCodedTDsVals(ws.objects, td_id_val_map);
        var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
        var new_objects := WriteActiveDOsVals(t_objs2, do_id_val_map);

        ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        ws_d := true;

        Lemma_DrvDevWrite_PreserveObjPIDs(ws.objects, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDM_FulFillIsValidState_SubjsOwnObjsThenInSamePartition_IfPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');
        
        // Prove DM_IsSecureState_SI2(ws')
        var ws_k' := DMStateToState(ws');
        Lemma_DM_GreenDrvWrite_FulfillSI2(ws, k, ws', ws_k', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert DM_IsSecureState_SI2(ws');

        // Prove DM_IsSecureState_SI3(ws')
        Lemma_NewDM_GreenDrvWrite_SameDMAllObjsIDsAndObjPIDs(ws, ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_DrvWrite_NewDM_FulfillSI3(ws, ws');

        // Prove DM_IsSecureState(ws')
        Lemma_NewDM_GreenDrvWrite_SameDMRedTDs(ws, ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_DM_SI1HoldsIfRedTDsAreUnchanged(ws, k, ws', ws_k');
        assert DM_IsSecureState_SI1(ws');
        assert DM_IsSecureState(ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DMStateToState_SecureK(ws', ws_k');
        assert IsValidState(ws_k') && IsSecureState(ws_k');
        assert ws_k' == DrvWrite_ProposedNewState(k, td_id_val_map, fd_id_val_map, do_id_val_map);
        var k', d := DrvWrite(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert d == true;
        assert k' == DMStateToState(ws');

        Lemma_DrvDevWrite_Func_Prove(k, k', td_id_val_map, fd_id_val_map, do_id_val_map);

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_GreenDrvWrite_ProvePreConditionsOfDM_CalcNewState(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
        assert result1 == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
    }
}

// Operation: Device in the red partition writes a set of objects with values
// [NOTE] Need 10s to verify
method DM_RedDevWrite(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')
                    
    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(ws.objects))
        // Properties needed by the following properties
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device
        
    ensures (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures P_DM_OpsProperties(ws, DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    ensures DM_CalcNewState(ws, DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state
        
    ensures var k := DMStateToState(ws);
            (forall id :: id in td_id_val_map ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in fd_id_val_map ==> id in k.objects.active_fds) &&
            (forall id :: id in do_id_val_map ==> id in k.objects.active_dos)
        // Properties needed by the following properties
    ensures ws_d == true
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))

    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(ws'))
        // Property: Commutative diagram to DevWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Dev_ID(dev_sid) in k.subjects.devs;

    var dev_id := Dev_ID(dev_sid);
    {
        var k', d := DevWrite(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert d == true;

        var result := DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        ws' := result.0;
        ws_d := result.1;

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove k' == DMStateToState(ws')
        assert k' == DMStateToState(ws');
        Lemma_DM_DevWrite_AllWrittenObjsMustBeInSamePartitionWithDev(ws, k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');
        
        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws, ws');
        //Lemma_DrvDevWrite_PreserveObjPIDs(ws.objects, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_DM_DrvDevWrite_ProveNewDM_FulfillSI2_IfGreenTDsAreUnchanged_PreConditions(ws, td_id_val_map, fd_id_val_map, do_id_val_map, ws'.objects);
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        Lemma_DrvDevWrite_Func_Prove(k, k', td_id_val_map, fd_id_val_map, do_id_val_map);
        
        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_RedDevWrite_ProvePreConditionsOfDM_CalcNewState(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
        assert result1 == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert result1 == (ws', ws_d);
    }
}

// Operation: Device in a green partition writes a set of objects with values
// [NOTE] Needs 10s to verify
method DM_GreenDevWrite(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')
                    
    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(ws.objects))
        // Properties needed by the following property
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device

    ensures (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures P_DM_OpsProperties(ws, DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    ensures DM_CalcNewState(ws, DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures var k := DMStateToState(ws);
            (forall id :: id in td_id_val_map ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in fd_id_val_map ==> id in k.objects.active_fds) &&
            (forall id :: id in do_id_val_map ==> id in k.objects.active_dos)
        // Properties needed by the following properties
    ensures ws_d == true
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))

    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(ws'))
        // Property: Commutative diagram to DevWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Dev_ID(dev_sid) in k.subjects.devs;

    var dev_id := Dev_ID(dev_sid);

    {
        var k', d := DevWrite(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert d == true;

        var result := DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        ws' := result.0;
        ws_d := result.1;

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_DM_DrvDevWrite_ProveP_DMAndNewDM_SameSubjObjPID(ws, td_id_val_map, fd_id_val_map, do_id_val_map, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove k' == DMStateToState(ws')
        assert k' == DMStateToState(ws');
        Lemma_DM_DevWrite_AllWrittenObjsMustBeInSamePartitionWithDev(ws, k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        
        // Prove TDs are not modified
        Lemma_DM_ValidState_ProveP_DMSubjectsHasUniqueIDs(ws);
        Lemma_DM_DevsInGreen_Prove(ws, dev_id);
        Lemma_GreenDevWrite_TDsAreUnmodified(ws, k, dev_id, td_id_val_map);
        Lemma_GreenDevWrite_TDsInDMObjectsAreSame(ws, ws', td_id_val_map, fd_id_val_map, do_id_val_map);
        
        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');
        
        // Prove DM_IsSecureState(ws')
        Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws, ws');
        Lemma_DM_DrvDevWrite_ProveNewDM_FulfillSI2_IfGreenTDsAreUnchanged_PreConditions(ws, td_id_val_map, fd_id_val_map, do_id_val_map, ws'.objects);
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        Lemma_DrvDevWrite_Func_Prove(k, k', td_id_val_map, fd_id_val_map, do_id_val_map);

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_GreenDevWrite_ProvePreConditionsOfDM_CalcNewState(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
        assert result1 == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert result1 == (ws', ws_d);
    }
}




//******** Create/Destroy Partition ********//
// Operation: Create an empty I/O partition
// [NOTE] Needs 10s to verify
method DM_EmptyPartitionCreate(
    ws:DM_State, 
    new_pid:Partition_ID // The ID of the new partition
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_EmptyPartitionCreate_InnerFunc(ws, new_pid)
    ensures P_DM_OpsProperties(ws, DM_EmptyPartitionCreateOp(new_pid))
    ensures DM_CalcNewState(ws, DM_EmptyPartitionCreateOp(new_pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state
    
    ensures ws_d ==> EmptyPartitionCreate_Prop(DMStateToState(ws), new_pid, DMStateToState(ws'), true)

    ensures (ws_d == true ==> EmptyPartitionCreate_Func(DMStateToState(ws), new_pid) == DMStateToState(ws'))
        // Property: Commutative diagram to EmptyPartitionCreate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var result := DM_EmptyPartitionCreate_InnerFunc(ws, new_pid);
    ws' := result.0;
    ws_d := result.1; 
    if(ws_d)
    {
        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove k' == DMStateToState(ws')
        assert (new_pid != NULL) && (new_pid !in k.pids);
        var k', d := EmptyPartitionCreate(k, new_pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws, ws');
        Lemma_EmptyPartitionCreateDestroy_ProveTDsAreUnmodified(ws, ws');
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_EmptyPartitionCreateOp(ws, new_pid, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_EmptyPartitionCreateOp(new_pid));
        assert result1 == DM_EmptyPartitionCreate_InnerFunc(ws, new_pid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_EmptyPartitionCreate_ProveFalseCase(ws, new_pid);
    }
}

// Operation: Destroy an I/O partition
// [NOTE] Needs 10s to verify
method DM_EmptyPartitionDestroy(
    ws:DM_State, 
    pid:Partition_ID // The ID of the partition to be destroyed
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_EmptyPartitionDestroy_InnerFunc(ws, pid)
    ensures P_DM_OpsProperties(ws, DM_EmptyPartitionDestroyOp(pid))
    ensures DM_CalcNewState(ws, DM_EmptyPartitionDestroyOp(pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures ws_d ==> EmptyPartitionDestroy_Prop(DMStateToState(ws), pid, DMStateToState(ws'), true)

    ensures (ws_d == true ==> EmptyPartitionDestroy_Func(DMStateToState(ws), pid) == DMStateToState(ws'))
        // Property: Commutative diagram to EmptyPartitionDestroy in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var result := DM_EmptyPartitionDestroy_InnerFunc(ws, pid);
    ws' := result.0;
    ws_d := result.1; 
    if(ws_d)
    {
        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DM_EmptyPartitionDestroy_ProveCheckOfDevActivateInK(ws, k, pid);
        var k', d := EmptyPartitionDestroy(k, pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_EmptyPartitionDestroy_ProveRedPIDStillExists(ws, ws', pid);
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws, ws');
        Lemma_EmptyPartitionCreateDestroy_ProveTDsAreUnmodified(ws, ws');
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_EmptyPartitionDestroyOp(ws, pid, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_EmptyPartitionDestroyOp(pid));
        assert result1 == DM_EmptyPartitionDestroy_InnerFunc(ws, pid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_EmptyPartitionDestroy_ProveFalseCase(ws, pid);
    }
}




//******** DrvActivate ********//
// Operation: Activate a driver into a green partition
// [NOTE] Red drivers do not need to be deactivated/activated, because they do
// not need to be moved to green partitions
// [NOTE] Needs 40s to verify
method DM_DrvActivateToGreenPartition(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver to be activated
    green_pid:Partition_ID // ID of the partition to activate the driver into
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires green_pid != NULL
    requires green_pid != ws.red_pid
        // Requirement: the destination partition must be a green partition

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid)
    ensures P_DM_OpsProperties(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid))
    ensures DM_CalcNewState(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures var k := DMStateToState(ws);
            (ws_d == true 
                ==> (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.inactive_fds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.inactive_dos))
        // Property needed by the following property
    ensures (ws_d == true ==> P_DrvActivate_ModificationToState(DMStateToState(ws), drv_sid, green_pid, DMStateToState(ws')))

    ensures (ws_d == true ==> DrvActivate_Func(DMStateToState(ws), drv_sid, green_pid) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvActivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Drv_Property(k, Drv_ID(drv_sid));

    var drv_id := Drv_ID(drv_sid);
    
    var result := DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid);
    ws' := result.0;
    ws_d := result.1; 
    if(ws_d)
    {
        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        var tds_owned_by_drv:set<TD_ID> := ws.subjects.drvs[drv_id].td_ids;
        var fds_owned_by_drv:set<FD_ID> := ws.subjects.drvs[drv_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := ws.subjects.drvs[drv_id].do_ids;

        var new_objects := ws'.objects;
        var new_subjects := ws'.subjects;
        assert ws'.red_pid == ws.red_pid;

        // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
        var toactivate_s_ids:set<Subject_ID> := {drv_sid};
        var toactivate_td_ids := tds_owned_by_drv;
        var toactivate_fd_ids := fds_owned_by_drv;
        var toactivate_do_ids := dos_owned_by_drv;

        Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DrvDevActivate_AllObjsToBeActivatedAreInactiveInK(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k, drv_id, toactivate_td_ids);
        Lemma_DrvActivate_ProveSubjsObjsFulfillProperties(k, new_subjects, new_objects, drv_id, green_pid);
        assert SubjObjActivate_PropertiesOfNewTDs(k, new_objects, toactivate_td_ids, green_pid);
        assert SubjObjActivate_PropertiesOfNewFDs(k, new_objects, toactivate_fd_ids, green_pid);
        assert SubjObjActivate_PropertiesOfNewDOs(k, new_objects, toactivate_do_ids, green_pid);
        assert SubjObjActivate_PropertiesOfNewSubjs(k, new_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, green_pid);

        Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, new_subjects.devs, new_objects, toactivate_td_ids, green_pid);

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DM_DevActivate_ProveCheckOfDevActivateInK(ws, k, drv_sid, green_pid);
        assert (SubjPID(k, drv_sid) == NULL) && (green_pid in k.pids);
        var k', d := DrvActivate(k, drv_sid, green_pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');
        
        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
        Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
        Lemma_NewDM_SubjObjActivate_FulfillSI2(ws, k, ws', k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, green_pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_DrvActivateToGreenPartitionOp(ws, drv_sid, green_pid, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid));
        assert result1 == DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_DrvActivateToGreenPartition_ProveFalseCase(ws, drv_sid, green_pid);
    }
}

// Operation: Activate a driver into the red partition
// [NOTE] Red drivers do not need to be deactivated/activated, because they do
// not need to be moved to green partitions
method DM_DrvActivateToRedPartition(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_DrvActivateToRedPartition_InnerFunc(ws, drv_sid)
    ensures P_DM_OpsProperties(ws, DM_DrvActivateToRedPartitionOp(drv_sid))
    ensures DM_CalcNewState(ws, DM_DrvActivateToRedPartitionOp(drv_sid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures var k := DMStateToState(ws);
            (ws_d == true 
                ==> (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.inactive_fds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.inactive_dos))
        // Property needed by the following property
    ensures (ws_d == true ==> P_DrvActivate_ModificationToState(DMStateToState(ws), drv_sid, ws.red_pid, DMStateToState(ws')))

    ensures (ws_d == true ==> DrvActivate_Func(DMStateToState(ws), drv_sid, ws.red_pid) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvActivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Drv_Property(k, Drv_ID(drv_sid));

    var drv_id := Drv_ID(drv_sid);
    var pid := ws.red_pid;

    var result := DM_DrvActivateToRedPartition_InnerFunc(ws, drv_sid);
    ws' := result.0;
    ws_d := result.1; 
    if(ws_d)
    {
        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        var tds_owned_by_drv:set<TD_ID> := ws.subjects.drvs[drv_id].td_ids;
        var fds_owned_by_drv:set<FD_ID> := ws.subjects.drvs[drv_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := ws.subjects.drvs[drv_id].do_ids;

        var new_objects := ws'.objects;
        var new_subjects := ws'.subjects;
        assert ws'.red_pid == ws.red_pid;

        // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
        var toactivate_s_ids:set<Subject_ID> := {drv_sid};
        var toactivate_td_ids := tds_owned_by_drv;
        var toactivate_fd_ids := fds_owned_by_drv;
        var toactivate_do_ids := dos_owned_by_drv;

        Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DrvDevActivate_AllObjsToBeActivatedAreInactiveInK(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k, drv_id, toactivate_td_ids);
        Lemma_DrvActivate_ProveSubjsObjsFulfillProperties(k, new_subjects, new_objects, drv_id, pid);
        assert SubjObjActivate_PropertiesOfNewTDs(k, new_objects, toactivate_td_ids, pid);
        assert SubjObjActivate_PropertiesOfNewFDs(k, new_objects, toactivate_fd_ids, pid);
        assert SubjObjActivate_PropertiesOfNewDOs(k, new_objects, toactivate_do_ids, pid);
        assert SubjObjActivate_PropertiesOfNewSubjs(k, new_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

        Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, new_subjects.devs, new_objects, toactivate_td_ids, pid);

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DM_DevActivate_ProveCheckOfDevActivateInK(ws, k, drv_sid, pid);
        assert (SubjPID(k, drv_sid) == NULL) && (pid in k.pids);
        var k', d := DrvActivate(k, drv_sid, pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');
        
        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
        Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
        Lemma_NewDM_SubjObjActivate_FulfillSI2(ws, k, ws', k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_DrvActivateToRedPartitionOp(ws, drv_sid, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_DrvActivateToRedPartitionOp(drv_sid));
        assert result1 == DM_DrvActivateToRedPartition_InnerFunc(ws, drv_sid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_DrvActivateToRedPartition_ProveFalseCase(ws, drv_sid);
    }
}




//******** DevActivate ********//
// Operation: Activate a device into a partition. The partition could be green
// or red partition. For example, devices are moved between red and green.
// [NOTE] Need 50s to verify
method DM_DevActivate(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device to be activated
    pid:Partition_ID // ID of the partition to activate the device into
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires pid != NULL

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_DevActivate_InnerFunc(ws, dev_sid, pid)
    ensures P_DM_OpsProperties(ws, DM_DevActivateOp(dev_sid, pid))
    ensures DM_CalcNewState(ws, DM_DevActivateOp(dev_sid, pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures var k := DMStateToState(ws);
            (ws_d == true 
                ==> (forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].td_ids && id != k.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id
                        ==> id in k.objects.inactive_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].fd_ids ==> id in k.objects.inactive_fds) &&
                    (forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].do_ids ==> id in k.objects.inactive_dos))
        // Property needed by the following property
    ensures (ws_d == true ==> P_DevActivate_ModificationToState(DMStateToState(ws), dev_sid, pid, DMStateToState(ws')))

    ensures (ws_d == true ==> DevActivate_Func(DMStateToState(ws), dev_sid, pid) == DMStateToState(ws'))
        // Property: Commutative diagram to DevActivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Dev_Property(k, Dev_ID(dev_sid));

    var dev_id := Dev_ID(dev_sid);
    {
        var result := DM_DevActivate_InnerFunc(ws, dev_sid, pid);
        ws' := result.0;
        ws_d := result.1; 
        if(ws_d)
        {
            assert P_DMAndNewDM_SameObjectID(ws, ws');
            assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

            var tds_owned_by_dev:set<TD_ID> := ws.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := ws.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := ws.subjects.devs[dev_id].do_ids;

            var new_objects := ws'.objects;
            var new_subjects := ws'.subjects;
            assert ws'.red_pid == ws.red_pid;

            // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
            var toactivate_s_ids:set<Subject_ID> := {dev_sid};
            var toactivate_td_ids := tds_owned_by_dev;
            var toactivate_fd_ids := fds_owned_by_dev;
            var toactivate_do_ids := dos_owned_by_dev;

            Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
            Lemma_DrvDevActivate_AllObjsToBeActivatedAreInactiveInK(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
            Lemma_DevActivate_ProveSubjsObjsFulfillProperties(k, new_subjects, new_objects, dev_id, pid);
            assert SubjObjActivate_PropertiesOfNewTDs(k, new_objects, toactivate_td_ids, pid);
            assert SubjObjActivate_PropertiesOfNewFDs(k, new_objects, toactivate_fd_ids, pid);
            assert SubjObjActivate_PropertiesOfNewDOs(k, new_objects, toactivate_do_ids, pid);
            assert SubjObjActivate_PropertiesOfNewSubjs(k, new_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

            Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, new_subjects.devs, new_objects, toactivate_td_ids, pid);

            // Prove common validity properties
            Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

            Lemma_NewDM_SameSubjObjIDs(ws, ws');
            Lemma_NewDM_SameSubjObjOwnership(ws, ws');

            // Prove k' == DMStateToState(ws')
            Lemma_DM_DevActivate_ProveCheckOfDevActivateInK(ws, k, dev_sid, pid);
            assert (SubjPID(k, dev_sid) == NULL) && (pid in k.pids);
            var k', d := DevActivate(k, dev_sid, pid);
            assert d == true;
            assert k' == DMStateToState(ws');
            
            // Prove DM_IsValidState_SubjsObjsPIDs(ws')
            Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
            assert DM_IsValidState_SubjsObjsPIDs(ws');

            // Prove DM_IsValidState(ws')
            Lemma_NewDM_DevActivate_OtherDevsHaveUnchangedPIDs(ws, ws', dev_id, pid);
            Lemma_NewDM_IsValidState_DevActivate_DevsActivateCond(ws, ws', dev_id, pid);
            assert DM_IsValidState(ws');

            // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
            Lemma_DevActivate_HCodedTDsBeingActivatedHaveNoWriteTransfersToTDs(k, dev_id);
            Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
            Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
            Lemma_NewDM_SubjObjActivate_FulfillSI2(ws, k, ws', k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
            Lemma_NewDMFromNewK_FulfillSI3(ws', k');
            assert DM_IsSecureState_SI3(ws');
            Lemma_NewDMFromNewK_FulfillSI1(ws', k');
            assert DM_IsSecureState(ws');

            // Prove DM_CalcNewState() == (ws', ws_d)
            Lemma_ProveP_DM_OpsProperties_DevActivateOp(ws, dev_sid, pid, ws', ws_d);
            ghost var result1 := DM_CalcNewState(ws, DM_DevActivateOp(dev_sid, pid));
            assert result1 == DM_DevActivate_InnerFunc(ws, dev_sid, pid);
            assert result1 == (ws', ws_d);
        }
        else
        {
            assert ws' == ws;
            assert ws_d == false;
            Lemma_DM_DevActivate_ProveFalseCase(ws, dev_sid, pid);
        }
    }
}




//******** ExternalObjsActivate ********//
// Operation: Activate external objects into a green partition
// [NOTE] External objects in red do not need to be deactivated/activated,
// because these objects do not need to be moved to green partitions
// [NOTE] Needs 20s to verify
method DM_ExternalObjsActivateToGreenPartition(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be activated
    green_pid:Partition_ID // ID of the partition to activate the objects into
) returns (ws':DM_State, ws_d:bool)
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

    ensures (ws', ws_d) == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
    ensures P_DM_OpsProperties(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid))
    ensures DM_CalcNewState(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures (ws_d == true 
                ==> (forall s_id, o_id :: s_id in AllSubjsIDs(DMStateToState(ws).subjects) &&
                            o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                        ==> !DoOwnObj(DMStateToState(ws), s_id, o_id)))
        // Property needed by the following property
    ensures (ws_d == true 
                ==> P_ExternalObjsActivate_ModificationToState(DMStateToState(ws), 
                        td_ids, fd_ids, do_ids, green_pid, DMStateToState(ws')))

    ensures (ws_d == true ==> ExternalObjsActivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids, green_pid) == DMStateToState(ws'))
        // Property: Commutative diagram to ExternalObjsActivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var result := DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
    ws' := result.0;
    ws_d := result.1;
    if(ws_d)
    {
        var new_objects := ws'.objects;
        var new_subjects := ws'.subjects;
        assert ws'.red_pid == ws.red_pid;

        Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, td_ids, fd_ids, do_ids);
        // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
        var toactivate_s_ids:set<Subject_ID> := {};
        var toactivate_td_ids := td_ids;
        var toactivate_fd_ids := fd_ids;
        var toactivate_do_ids := do_ids;

        Lemma_ExternalObjsActivate_AllObjsToBeActivatedAreExternalObjs(k, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        assert SubjObjActivate_PropertiesOfNewTDs(k, new_objects, toactivate_td_ids, green_pid);
        assert SubjObjActivate_PropertiesOfNewFDs(k, new_objects, toactivate_fd_ids, green_pid);
        assert SubjObjActivate_PropertiesOfNewDOs(k, new_objects, toactivate_do_ids, green_pid);
        assert SubjObjActivate_PropertiesOfNewSubjs(k, k.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, green_pid); 

        Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, k.subjects.devs, new_objects, toactivate_td_ids, green_pid);

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DM_ExternalObjActivate_ProveCheckOfDevActivateInK(ws, k, td_ids, fd_ids, do_ids, green_pid);
        
        var k', d := ExternalObjsActivate(k, td_ids, fd_ids, do_ids, green_pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
        Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
        Lemma_NewDM_SubjObjActivate_FulfillSI2(ws, k, ws', k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, green_pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_ExternalObjsActivateToGreenPartitionOp(ws, td_ids, fd_ids, do_ids, green_pid, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid));
        assert result1 == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_ExternalObjsActivateToGreenPartition_ProveFalseCase(ws, td_ids, fd_ids, do_ids, green_pid);
    }
}

// Operation: Activate external objects into the OS partition
// [NOTE] External objects in red do not need to be deactivated/activated,
// because these objects do not need to be moved to green partitions
// [NOTE] Needs 20s to verify
method DM_ExternalObjsActivateToRedPartition(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID> //  IDs of the objects to be activated
) returns (ws':DM_State, ws_d:bool)
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

    ensures (ws', ws_d) == DM_ExternalObjsActivateToRedPartition_InnerFunc(ws, td_ids, fd_ids, do_ids)
    ensures P_DM_OpsProperties(ws, DM_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids))
    ensures DM_CalcNewState(ws, DM_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures (ws_d == true 
                ==> (forall s_id, o_id :: s_id in AllSubjsIDs(DMStateToState(ws).subjects) &&
                            o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                        ==> !DoOwnObj(DMStateToState(ws), s_id, o_id)))
        // Property needed by the following property
    ensures (ws_d == true 
                ==> P_ExternalObjsActivate_ModificationToState(DMStateToState(ws), 
                        td_ids, fd_ids, do_ids, ws.red_pid, DMStateToState(ws')))

    ensures (ws_d == true ==> ExternalObjsActivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids, ws.red_pid) == DMStateToState(ws'))
        // Property: Commutative diagram to ExternalObjsActivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var result := DM_ExternalObjsActivateToRedPartition_InnerFunc(ws, td_ids, fd_ids, do_ids);
    ws' := result.0;
    ws_d := result.1;
    if(ws_d)
    {
        var new_objects := ws'.objects;
        var new_subjects := ws'.subjects;
        assert ws'.red_pid == ws.red_pid;

        Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, td_ids, fd_ids, do_ids);
        // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
        var toactivate_s_ids:set<Subject_ID> := {};
        var toactivate_td_ids := td_ids;
        var toactivate_fd_ids := fd_ids;
        var toactivate_do_ids := do_ids;

        var pid := ws.red_pid;
        Lemma_ExternalObjsActivate_AllObjsToBeActivatedAreExternalObjs(k, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        assert SubjObjActivate_PropertiesOfNewTDs(k, new_objects, toactivate_td_ids, pid);
        assert SubjObjActivate_PropertiesOfNewFDs(k, new_objects, toactivate_fd_ids, pid);
        assert SubjObjActivate_PropertiesOfNewDOs(k, new_objects, toactivate_do_ids, pid);
        assert SubjObjActivate_PropertiesOfNewSubjs(k, k.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid); 

        Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, k.subjects.devs, new_objects, toactivate_td_ids, pid);

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DM_ExternalObjActivate_ProveCheckOfDevActivateInK(ws, k, td_ids, fd_ids, do_ids, pid);
        
        var k', d := ExternalObjsActivate(k, td_ids, fd_ids, do_ids, pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
        Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
        Lemma_NewDM_SubjObjActivate_FulfillSI2(ws, k, ws', k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_ExternalObjsActivateToRedPartitionOp(ws, td_ids, fd_ids, do_ids, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids));
        assert result1 == DM_ExternalObjsActivateToRedPartition_InnerFunc(ws, td_ids, fd_ids, do_ids);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_ExternalObjsActivateToRedPartition_ProveFalseCase(ws, td_ids, fd_ids, do_ids);
    }
}




//******** DrvDeactivate ********//
// Operation: Deactivate a driver from a green partition
// [NOTE] Red drivers do not need to be deactivated/activated, because they do
// not need to be moved to green partitions
// [NOTE] Needs 50s to verify
method DM_GreenDrvDeactivate(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: The driver must be in a green partition

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid)
    ensures P_DM_OpsProperties(ws, DM_GreenDrvDeactivateOp(drv_sid))
    ensures DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures var k := DMStateToState(ws);
            (ws_d == true 
                ==> (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.active_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.active_fds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.active_dos))
        // Property needed by the following property
    ensures (ws_d == true ==> P_DrvDeactivate_ModificationToState(DMStateToState(ws), drv_sid, DMStateToState(ws')))

    ensures (ws_d == true ==> DrvDeactivate_Func(DMStateToState(ws), drv_sid) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvDeactivate in the abstract model
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

    var result := DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid);
    ws' := result.0;
    ws_d := result.1;
    if(ws_d)
    {
        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        {
            assert pid != NULL;
            assert pid != ws.red_pid;
                
            assert DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws);
            Lemma_DM_DrvDeactivate_ObjectsToBeDeactivatedAreInSamePartitionWithDrv(ws, drv_id,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

            // Prove the condition saves us from checking CAS
            //// Build CAS for K
            Lemma_SubjObjDeactivate_ProvePreConditionsOfBuildCAS(k, {ActiveTDsState(k)});
            var k_cas_for_dev_in_green := BuildCAS(k, KToKParams(k), {ActiveTDsState(k)});
            Lemma_GreenDrvDeactivate_HCodedTDsAreNotBeingDeactivated(k, drv_id);
            Lemma_DM_ObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivated_ThenNoOtherDevHasTransferToTheseObjs(ws, k, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, pid); 
            assert DM_ObjDeactivate_ChkNoOtherDevHasTransferToObjToBeDeactivated_IfTheObjIsInGreen(ws, k,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, {ActiveTDsState(k)});
                // Property: Ensure no active device in the same partition with the driver 
                // has transfers to any objects of the driver

            Lemma_DM_ObjsDeactivate_ProveCheckOfObjDeactivateInK(ws, k, pid,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, {ActiveTDsState(k)});
        }
        var k', d := DrvDeactivate(k, drv_sid);
        assert d == true;
        assert k' == DMStateToState(ws');
        
        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
        Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
        Lemma_NewDM_SubjObjDeactivate_FulfillSI2(ws, k, ws', k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_GreenDrvDeactivateOp(ws, drv_sid, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid));
        assert result1 == DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_GreenDrvDeactivate_ProveFalseCase(ws, drv_sid);
    }
}

// Operation: Deactivate a driver from the red partition
// [NOTE] Red drivers do not need to be deactivated/activated, because they do
// not need to be moved to green partitions
method DM_RedDrvDeactivate(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid
        // Requirement: The driver must be in the red partition

    requires P_RedDevsHaveNoTransferToGivenRedDrvAtAnyTime(ws, Drv_ID(drv_sid))

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_RedDrvDeactivate_InnerFunc(ws, drv_sid)
    ensures P_DM_OpsProperties(ws, DM_RedDrvDeactivateOp(drv_sid))
    ensures DM_CalcNewState(ws, DM_RedDrvDeactivateOp(drv_sid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures var k := DMStateToState(ws);
            (ws_d == true 
                ==> (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].td_ids ==> id in k.objects.active_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].fd_ids ==> id in k.objects.active_fds) &&
                    (forall id :: id in k.subjects.drvs[Drv_ID(drv_sid)].do_ids ==> id in k.objects.active_dos))
        // Property needed by the following property
    ensures (ws_d == true ==> P_DrvDeactivate_ModificationToState(DMStateToState(ws), drv_sid, DMStateToState(ws')))

    ensures (ws_d == true ==> DrvDeactivate_Func(DMStateToState(ws), drv_sid) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvDeactivate in the abstract model
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
    assert pid == ws.red_pid;

    var result := DM_RedDrvDeactivate_InnerFunc(ws, drv_sid);
    ws' := result.0;
    ws_d := result.1;
    if(ws_d)
    {
        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DM_DrvDeactivate_ProveCheckOfDrvDeactivateInK_IfDrvIsInRed(ws, k, drv_sid);
        assert DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws);
        Lemma_DM_DrvDeactivate_ObjectsToBeDeactivatedAreInSamePartitionWithDrv(ws, drv_id,
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

        var k', d := DrvDeactivate(k, drv_sid);
        assert d == true;
        assert k' == DMStateToState(ws');
        
        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
        Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
        Lemma_NewDM_SubjObjDeactivate_FulfillSI2(ws, k, ws', k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_RedDrvDeactivateOp(ws, drv_sid, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_RedDrvDeactivateOp(drv_sid));
        assert result1 == DM_RedDrvDeactivate_InnerFunc(ws, drv_sid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_RedDrvDeactivate_ProveFalseCase(ws, drv_sid);
    }
}




//******** DevDeactivate ********//
// Operation: Deactivate a device from red or green partitions
// [NOTE] Needs 50s to verify
method DM_DevDeactivate(
    ws:DM_State, 
    dev_sid:Subject_ID // ID of the device to be deactivated
) returns (ws':DM_State, ws_d:bool)
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
    
    ensures (ws', ws_d) == DM_DevDeactivate_InnerFunc(ws, dev_sid)
    ensures P_DM_OpsProperties(ws, DM_DevDeactivateOp(dev_sid))
    ensures DM_CalcNewState(ws, DM_DevDeactivateOp(dev_sid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures var k := DMStateToState(ws);
            (ws_d == true 
                ==> (forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].td_ids && id != k.subjects.devs[Dev_ID(dev_sid)].hcoded_td_id
                        ==> id in k.objects.active_non_hcoded_tds) &&
                    (forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].fd_ids ==> id in k.objects.active_fds) &&
                    (forall id :: id in k.subjects.devs[Dev_ID(dev_sid)].do_ids ==> id in k.objects.active_dos))
        // Property needed by the following property
    ensures (ws_d == true ==> P_DevDeactivate_ModificationToState(DMStateToState(ws), dev_sid, DMStateToState(ws')))

    ensures (ws_d == true ==> DevDeactivate_Func(DMStateToState(ws), dev_sid) == DMStateToState(ws'))
        // Property: Commutative diagram to DevDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Dev_Property(k, Dev_ID(dev_sid));

    var dev_id := Dev_ID(dev_sid);
    var dev_state := ws.subjects.devs[dev_id];

    var todeactivate_td_ids := ws.subjects.devs[dev_id].td_ids;
    var todeactivate_fd_ids := ws.subjects.devs[dev_id].fd_ids;
    var todeactivate_do_ids := ws.subjects.devs[dev_id].do_ids;
    var pid := DM_SubjPID(ws.subjects, dev_sid);
    
    var result := DM_DevDeactivate_InnerFunc(ws, dev_sid);
    ws' := result.0;
    ws_d := result.1; 
    if(ws_d)
    {
        var tds_owned_by_dev:set<TD_ID> := ws.subjects.devs[dev_id].td_ids;
        var fds_owned_by_dev:set<FD_ID> := ws.subjects.devs[dev_id].fd_ids;
        var dos_owned_by_dev:set<DO_ID> := ws.subjects.devs[dev_id].do_ids;

        var new_objects := ws'.objects;
        var new_subjects := ws'.subjects;
        assert ws'.red_pid == ws.red_pid;

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        if(DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid)
        {
            Lemma_DM_DevDeactivate_ProveCheckOfDevDeactivateInK_IfDevIsInRed(ws, k, dev_sid);
        }
        else
        {
            assert DM_SubjPID(ws.subjects, dev_sid) != NULL;
            assert DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid;

            // Prove the condition saves us from checking CAS
            //// Build CAS for K
            Lemma_SubjObjDeactivate_ProvePreConditionsOfBuildCAS(k, {ActiveTDsState(k)});
            var k_cas_for_dev_in_green := BuildCAS(k, KToKParams(k), {ActiveTDsState(k)});
            Lemma_DevDeactivate_HCodedTDsOfOtherDevsAreNotBeingDeactivated(k, dev_id);
            Lemma_DM_DevDeactivate_NoOtherGreenTDsRefObjsOfDevToBeDeactivated_ThenNoOtherDevHasTransferToDev(ws, k, dev_id, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, pid); 
            assert DM_DevDeactivate_ChkNoOtherDevHasTransferToDevToBeDeactivated_IfTheDevIsInGreen(ws, k, dev_sid, k_cas_for_dev_in_green, {ActiveTDsState(k)});
                // Check the CAS only when the device to be deactivated is in green
                // Ensure no active device in the same partition with the device 
                // has transfers to any objects of the device

            Lemma_DM_DevDeactivate_ProveCheckOfDevDeactivateInK_IfDevIsInGreen(ws, k, dev_sid, k_cas_for_dev_in_green, {ActiveTDsState(k)});
        }
        var k', d := DevDeactivate(k, dev_sid);
        assert d == true;
        assert k' == DMStateToState(ws');
            
        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_DevDeactivate_OtherDevsHaveUnchangedPIDs(ws, ws', dev_id);
        Lemma_NewDM_IsValidState_DevDeactivate_DevsActivateCond(ws, ws', dev_id);
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_DevDeactivate_ActiveDevsInNewKIsSubsetOfOnesInK(k, k', dev_id, dev_state);
        Lemma_DM_DevDeactivate_PropertiesOfObjsToBeDeactivated(ws, dev_id,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
        Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
        Lemma_NewDM_SubjObjDeactivate_FulfillSI2(ws, k, ws', k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');
        
        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_DevDeactivateOp(ws, dev_sid, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_DevDeactivateOp(dev_sid));
        assert result1 == DM_DevDeactivate_InnerFunc(ws, dev_sid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_DevDeactivate_ProveFalseCase(ws, dev_sid);
    }
}




//******** ExternalObjsDeactivate ********//
// Operation: Deactivate wimp USB TDs, external wimp FDs and external wimp DOs
// from the given green partition
// [NOTE] External objects in red do not need to be deactivated/activated,
// because these objects do not need to be moved to green partitions
// [NOTE] Needs 10s to verify
method DM_GreenExternalObjsDeactivate(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be deactivated
    green_pid:Partition_ID // The green partition that holds these objects
) returns (ws':DM_State, ws_d:bool)
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

    ensures (ws', ws_d) == DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
    ensures P_DM_OpsProperties(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid))
    ensures DM_CalcNewState(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures ws_d == true 
                ==> (forall id :: id in td_ids ==> id in ws.objects.active_non_hcoded_tds) &&
                    (forall id :: id in fd_ids ==> id in ws.objects.active_fds) &&
                    (forall id :: id in do_ids ==> id in ws.objects.active_dos)
        // Property needed by the following property
    ensures (ws_d == true 
                ==> P_ExternalObjsDeactivate_ModificationToState(DMStateToState(ws), DMStateToState(ws'),
                        td_ids, fd_ids, do_ids))

    ensures (ws_d == true ==> ExternalObjsDeactivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids) == DMStateToState(ws'))
        // Property: Commutative diagram to ExternalObjsDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var todeactivate_td_ids := td_ids;
    var todeactivate_fd_ids := fd_ids;
    var todeactivate_do_ids := do_ids;

    var result := DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
    ws' := result.0;
    ws_d := result.1;
    if(ws_d)
    {
        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        // Prove the condition saves us from checking CAS
        //// Build CAS for K
        Lemma_SubjObjDeactivate_ProvePreConditionsOfBuildCAS(k, {ActiveTDsState(k)});
        var k_cas_for_dev_in_green := BuildCAS(k, KToKParams(k), {ActiveTDsState(k)});
        Lemma_ExternalObjsDeactivate_HCodedTDsAreNotBeingDeactivated(ws, k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        Lemma_DM_ObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivated_ThenNoOtherDevHasTransferToTheseObjs(ws, k, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, green_pid); 
        assert DM_ObjDeactivate_ChkNoOtherDevHasTransferToObjToBeDeactivated_IfTheObjIsInGreen(ws, k,
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, {ActiveTDsState(k)});
            // Property: Ensure no active device in the same partition with the objects 
            // has transfers to any of these objects 

        Lemma_DM_ExternalWimpObjsDeactivate_ProveCheckOfObjDeactivateInK(ws, k, green_pid,
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, {ActiveTDsState(k)});
        Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        var k', d := ExternalObjsDeactivate(k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
        Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
        Lemma_NewDM_SubjObjDeactivate_FulfillSI2(ws, k, ws', k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_GreenExternalObjsDeactivateOp(ws, td_ids, fd_ids, do_ids, green_pid, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid));
        assert result1 == DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_GreenExternalObjsDeactivate_ProveFalseCase(ws, td_ids, fd_ids, do_ids, green_pid);
    }
}

// Operation: Deactivate OS external TDs, external FDs and external DOs
// from the given green partition
// [NOTE] External objects in red do not need to be deactivated/activated,
// because these objects do not need to be moved to green partitions
// [NOTE] Needs 10s to verify
method DM_RedExternalObjsDeactivate(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID> //  IDs of the objects to be deactivated
) returns (ws':DM_State, ws_d:bool)
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

    ensures (ws', ws_d) == DM_RedExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids)
    ensures P_DM_OpsProperties(ws, DM_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids))
    ensures DM_CalcNewState(ws, DM_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures td_ids <= AllTDIDs(DMStateToState(ws).objects)
    ensures fd_ids <= AllFDIDs(DMStateToState(ws).objects)
    ensures do_ids <= AllDOIDs(DMStateToState(ws).objects)
    ensures ws_d == true 
                ==> (forall id :: id in td_ids ==> id in ws.objects.active_non_hcoded_tds) &&
                    (forall id :: id in fd_ids ==> id in ws.objects.active_fds) &&
                    (forall id :: id in do_ids ==> id in ws.objects.active_dos)
        // Property needed by the following property
    ensures (ws_d == true 
                ==> P_ExternalObjsDeactivate_ModificationToState(DMStateToState(ws), DMStateToState(ws'),
                        td_ids, fd_ids, do_ids))

    ensures (ws_d == true ==> ExternalObjsDeactivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids) == DMStateToState(ws'))
        // Property: Commutative diagram to ExternalObjsDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var todeactivate_td_ids := td_ids;
    var todeactivate_fd_ids := fd_ids;
    var todeactivate_do_ids := do_ids;

    var result := DM_RedExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids);
    ws' := result.0;
    ws_d := result.1;
    var pid := ws.red_pid;
    if(ws_d)
    {
        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        Lemma_DM_RedExternalObjsDeactivate_ProveCheckOfExternalObjsDeactivateInK(ws, k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

        Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids); 
        var k', d := ExternalObjsDeactivate(k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_GreenTDsMustBeInActiveTDsState(ws, k);
        Lemma_DM_ValidState_ProveK_UniqueIDsAndOwnedObjs(ws');
        Lemma_NewDM_SubjObjDeactivate_FulfillSI2(ws, k, ws', k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_ProveP_DM_OpsProperties_RedExternalObjsDeactivateOp(ws, td_ids, fd_ids, do_ids, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids));
        assert result1 == DM_RedExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        Lemma_DM_RedExternalObjsDeactivate_ProveFalseCase(ws, td_ids, fd_ids, do_ids);
    }
}




//******** Util Lemmas ********//
lemma Lemma_DM_RedDrvRead_ProveFalseCase(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires DM_RedDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    requires (ws, false) == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures P_DM_OpsProperties(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
    ensures DM_CalcNewState(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
    assert result == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
}

lemma Lemma_DM_RedDrvWrite_ProveNewWSMapsToNewK_IfReturnTrue(
    k:State, ws':DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
)
    requires DrvWrite_PreConditions(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.active_non_hcoded_tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.active_fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.active_dos)

    requires var ws_k' := DMStateToState(ws');
            ws_k' == DrvWrite_ProposedNewState(k, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires DrvWrite_Stub(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true

    ensures var k' := DrvWrite_Stub(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0;
            k' == DMStateToState(ws')
{
    var k' := DrvWrite_Stub(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0;
    var ws_k' := DMStateToState(ws');

    assert P_DrvDevWrite_ModificationToState(k, td_id_val_map, fd_id_val_map, do_id_val_map, k');
    assert DrvWrite_ProposedNewState(k, td_id_val_map, fd_id_val_map, do_id_val_map) == k';
}

lemma Lemma_DM_RedDrvWrite_ProveFalseCase(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) 
    requires DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == ws
    requires DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2 == false

    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures DM_CalcNewState(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws, false)
{
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
}

lemma Lemma_ProveP_DM_OpsProperties_EmptyPartitionCreateOp(
    ws:DM_State, 
    pid:Partition_ID,
    ws':DM_State, ws_d:bool
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires (ws', ws_d) == DM_EmptyPartitionCreate_InnerFunc(ws, pid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_EmptyPartitionCreateOp(ws, DM_EmptyPartitionCreateOp(pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_EmptyPartitionCreate_ProveFalseCase(
    ws:DM_State, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires (ws, false) == DM_EmptyPartitionCreate_InnerFunc(ws, pid)

    ensures P_DM_OpsProperties(ws, DM_EmptyPartitionCreateOp(pid))
    ensures DM_CalcNewState(ws, DM_EmptyPartitionCreateOp(pid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_EmptyPartitionCreateOp(pid));
    assert result == DM_EmptyPartitionCreate_InnerFunc(ws, pid);
}

lemma Lemma_ProveP_DM_OpsProperties_EmptyPartitionDestroyOp(
    ws:DM_State, 
    pid:Partition_ID,
    ws':DM_State, ws_d:bool
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires (ws', ws_d) == DM_EmptyPartitionDestroy_InnerFunc(ws, pid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_EmptyPartitionDestroyOp(ws, DM_EmptyPartitionDestroyOp(pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_EmptyPartitionDestroy_ProveFalseCase(
    ws:DM_State, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires (ws, false) == DM_EmptyPartitionDestroy_InnerFunc(ws, pid)

    ensures P_DM_OpsProperties(ws, DM_EmptyPartitionDestroyOp(pid))
    ensures DM_CalcNewState(ws, DM_EmptyPartitionDestroyOp(pid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_EmptyPartitionDestroyOp(pid));
    assert result == DM_EmptyPartitionDestroy_InnerFunc(ws, pid);
}

lemma Lemma_ProveP_DM_OpsProperties_DrvActivateToGreenPartitionOp(
    ws:DM_State, 
    drv_sid:Subject_ID, green_pid:Partition_ID, 
    ws':DM_State, ws_d:bool
)
    requires (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
                Drv_ID(drv_sid) in ws.subjects.drvs &&
                green_pid != NULL &&
                green_pid != ws.red_pid)

    requires (ws', ws_d) == DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_DrvActivateToGreenPartitionOp(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ProveP_DM_OpsProperties_DrvActivateToRedPartitionOp(
    ws:DM_State, 
    drv_sid:Subject_ID, 
    ws':DM_State, ws_d:bool
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws) &&
                Drv_ID(drv_sid) in ws.subjects.drvs

    requires (ws', ws_d) == DM_DrvActivateToRedPartition_InnerFunc(ws, drv_sid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_DrvActivateToRedPartitionOp(ws, DM_DrvActivateToRedPartitionOp(drv_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_DrvActivateToGreenPartition_ProveFalseCase(
    ws:DM_State, 
    drv_sid:Subject_ID, green_pid:Partition_ID
)
    requires (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
                Drv_ID(drv_sid) in ws.subjects.drvs &&
                green_pid != NULL &&
                green_pid != ws.red_pid)

    requires (ws, false) == DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid)

    ensures P_DM_OpsProperties(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid))
    ensures DM_CalcNewState(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid));
    assert result == DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid);
}

lemma Lemma_DM_DrvActivateToRedPartition_ProveFalseCase(
    ws:DM_State, 
    drv_sid:Subject_ID
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws) &&
                Drv_ID(drv_sid) in ws.subjects.drvs

    requires (ws, false) == DM_DrvActivateToRedPartition_InnerFunc(ws, drv_sid)

    ensures P_DM_OpsProperties(ws, DM_DrvActivateToRedPartitionOp(drv_sid))
    ensures DM_CalcNewState(ws, DM_DrvActivateToRedPartitionOp(drv_sid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_RedDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_DrvActivateToRedPartitionOp(drv_sid));
    assert result == DM_DrvActivateToRedPartition_InnerFunc(ws, drv_sid);
}

lemma Lemma_ProveP_DM_OpsProperties_DevActivateOp(
    ws:DM_State, 
    dev_sid:Subject_ID, pid:Partition_ID,
    ws':DM_State, ws_d:bool
)
    requires (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
            Dev_ID(dev_sid) in ws.subjects.devs &&
            pid != NULL)
    requires (ws', ws_d) == DM_DevActivate_InnerFunc(ws, dev_sid, pid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_DevActivateOp(ws, DM_DevActivateOp(dev_sid, pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_DevActivate_ProveFalseCase(
    ws:DM_State, 
    dev_sid:Subject_ID, pid:Partition_ID
)
    requires (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
            Dev_ID(dev_sid) in ws.subjects.devs &&
            pid != NULL)

    requires (ws, false) == DM_DevActivate_InnerFunc(ws, dev_sid, pid)

    ensures P_DM_OpsProperties(ws, DM_DevActivateOp(dev_sid, pid))
    ensures DM_CalcNewState(ws, DM_DevActivateOp(dev_sid, pid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_DevActivateOp(dev_sid, pid));
    assert result == DM_DevActivate_InnerFunc(ws, dev_sid, pid);
}

lemma Lemma_ProveP_DM_OpsProperties_ExternalObjsActivateToGreenPartitionOp(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be deactivated
    green_pid:Partition_ID, 
    ws':DM_State, ws_d:bool
)
    requires DM_ExternalObjsActivateToGreenPartition_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)
    requires (ws', ws_d) == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_ExternalObjsActivateToGreenPartitionOp(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ProveP_DM_OpsProperties_ExternalObjsActivateToRedPartitionOp(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be deactivated
    ws':DM_State, ws_d:bool
)
    requires DM_ExternalObjsActivateToRedPartition_PreConditions(ws, td_ids, fd_ids, do_ids)
    requires (ws', ws_d) == DM_ExternalObjsActivateToRedPartition_InnerFunc(ws, td_ids, fd_ids, do_ids)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_ExternalObjsActivateToRedPartitionOp(ws, DM_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_ExternalObjsActivateToGreenPartition_ProveFalseCase(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
    requires DM_ExternalObjsActivateToGreenPartition_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)

    requires (ws, false) == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)

    ensures P_DM_OpsProperties(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid))
    ensures DM_CalcNewState(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid));
    assert result == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
}

lemma Lemma_DM_ExternalObjsActivateToRedPartition_ProveFalseCase(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires DM_ExternalObjsActivateToRedPartition_PreConditions(ws, td_ids, fd_ids, do_ids)

    requires (ws, false) == DM_ExternalObjsActivateToRedPartition_InnerFunc(ws, td_ids, fd_ids, do_ids)

    ensures P_DM_OpsProperties(ws, DM_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids))
    ensures DM_CalcNewState(ws, DM_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_ExternalObjsActivateToRedPartitionOp(td_ids, fd_ids, do_ids));
    assert result == DM_ExternalObjsActivateToRedPartition_InnerFunc(ws, td_ids, fd_ids, do_ids);
}

lemma Lemma_ProveP_DM_OpsProperties_GreenDrvDeactivateOp(
    ws:DM_State, 
    drv_sid:Subject_ID,
    ws':DM_State, ws_d:bool
)
    requires (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
            Drv_ID(drv_sid) in ws.subjects.drvs &&
            DM_SubjPID(ws.subjects, drv_sid) != NULL &&
            DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid)
    requires (ws', ws_d) == DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_GreenDrvDeactivateOp(ws, DM_GreenDrvDeactivateOp(drv_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ProveP_DM_OpsProperties_RedDrvDeactivateOp(
    ws:DM_State, 
    drv_sid:Subject_ID,
    ws':DM_State, ws_d:bool
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws) &&
            Drv_ID(drv_sid) in ws.subjects.drvs &&
            DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid &&
            P_RedDevsHaveNoTransferToGivenRedDrvAtAnyTime(ws, Drv_ID(drv_sid))
    requires (ws', ws_d) == DM_RedDrvDeactivate_InnerFunc(ws, drv_sid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_RedDrvDeactivateOp(ws, DM_RedDrvDeactivateOp(drv_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_GreenDrvDeactivate_ProveFalseCase(ws:DM_State, drv_sid:Subject_ID)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: The driver must be in a green partition

    requires (ws, false) == DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid)

    ensures P_DM_OpsProperties(ws, DM_GreenDrvDeactivateOp(drv_sid))
    ensures DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid));
    assert result == DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid);
}

lemma Lemma_DM_RedDrvDeactivate_ProveFalseCase(ws:DM_State, drv_sid:Subject_ID)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid
        // Requirement: The driver must be in the red partition

    requires P_RedDevsHaveNoTransferToGivenRedDrvAtAnyTime(ws, Drv_ID(drv_sid))

    requires (ws, false) == DM_RedDrvDeactivate_InnerFunc(ws, drv_sid)

    ensures P_DM_OpsProperties(ws, DM_RedDrvDeactivateOp(drv_sid))
    ensures DM_CalcNewState(ws, DM_RedDrvDeactivateOp(drv_sid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_RedDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_RedDrvDeactivateOp(drv_sid));
    assert result == DM_RedDrvDeactivate_InnerFunc(ws, drv_sid);
}

lemma Lemma_ProveP_DM_OpsProperties_DevDeactivateOp(
    ws:DM_State, 
    dev_sid:Subject_ID,
    ws':DM_State, ws_d:bool
)
    requires DM_DevDeactivate_PreConditions(ws, dev_sid)
    requires (ws', ws_d) == DM_DevDeactivate_InnerFunc(ws, dev_sid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_DevDeactivateOp(ws, DM_DevDeactivateOp(dev_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_DevDeactivate_ProveFalseCase(
    ws:DM_State, 
    dev_sid:Subject_ID
)
    requires DM_DevDeactivate_PreConditions(ws, dev_sid)

    requires (ws, false) == DM_DevDeactivate_InnerFunc(ws, dev_sid)

    ensures P_DM_OpsProperties(ws, DM_DevDeactivateOp(dev_sid))
    ensures DM_CalcNewState(ws, DM_DevDeactivateOp(dev_sid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_DevDeactivateOp(dev_sid));
    assert result == DM_DevDeactivate_InnerFunc(ws, dev_sid);
}

lemma Lemma_ProveP_DM_OpsProperties_GreenExternalObjsDeactivateOp(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be deactivated
    green_pid:Partition_ID, 
    ws':DM_State, ws_d:bool
)
    requires DM_GreenExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)
    requires (ws', ws_d) == DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_GreenExternalObjsDeactivateOp(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ProveP_DM_OpsProperties_RedExternalObjsDeactivateOp(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be deactivated
    ws':DM_State, ws_d:bool
)
    requires DM_RedExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids)
    requires (ws', ws_d) == DM_RedExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids)
    requires DM_Common_PostConditions(ws, ws', ws_d)

    ensures P_DM_OpsProperties_RedExternalObjsDeactivateOp(ws, DM_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_GreenExternalObjsDeactivate_ProveFalseCase(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
    requires DM_GreenExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)

    requires (ws, false) == DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)

    ensures P_DM_OpsProperties(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid))
    ensures DM_CalcNewState(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid));
    assert result == DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
}

lemma Lemma_DM_RedExternalObjsDeactivate_ProveFalseCase(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires DM_RedExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids)

    requires (ws, false) == DM_RedExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids)

    ensures P_DM_OpsProperties(ws, DM_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids))
    ensures DM_CalcNewState(ws, DM_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids)) == (ws, false)
{
    assert DM_Common_PostConditions(ws, ws, false);

    // Prove DM_CalcNewState(ws, DM_RedDrvDeactivateOp(drv_sid)) == (ws, false)
    var result := DM_CalcNewState(ws, DM_RedExternalObjsDeactivateOp(td_ids, fd_ids, do_ids));
    assert result == DM_RedExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids);
}