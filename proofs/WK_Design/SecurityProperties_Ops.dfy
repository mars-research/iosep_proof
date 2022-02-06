include "../DetailedModel/Model.dfy"
include "DM_AdditionalPropertiesLemmas.dfy"
include "Utils.dfy"
include "DevActivate_Multi_Mtd.dfy"

datatype WSD_Op   =  WSD_OSDrvReadOp(drv_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) | 
                    WSD_WimpDrvReadOp(drv_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) |
                    WSD_DevRead_Op(dev_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) |
                    WSD_OSDrvWrite_Op(drv_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    WSD_WimpDrvWrite_Op(drv_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    WSD_OSDevWrite_Op(dev_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    WSD_WimpDevWrite_Op(dev_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) | 

                    WKD_EmptyPartitionCreateOp(new_pid:Partition_ID) | 
                    WKD_EmptyPartitionDestroyOp(pid:Partition_ID) |
                    WKD_DrvActivateToGreenPartitionOp(drv_sid:Subject_ID, green_pid:Partition_ID) |
                    WKD_GreenDrvDeactivateOp(drv_sid:Subject_ID) | 
                    WKD_DevActivateOp(dev_sid:Subject_ID, pid:Partition_ID) |
                    WKD_DevDeactivateOp(dev_sid:Subject_ID) |
                    WKD_ExternalObjsActivateToGreenPartitionOp(td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID) | 
                    WKD_ExternalObjsActivateToRedPartitionOp(td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>) | 
                    WKD_GreenExternalObjsDeactivateOp(td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID) |
                    WKD_RedExternalObjsDeactivateOp(td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>) |

                    WKD_MultiDevs_ReturnOSOp(to_assign_dev_ids:seq<Dev_ID>)
                    /*WK_WimpDrvsDevs_Registration_CreatePartition_Op() | 
                    WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op(to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
                        to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
                        green_pid:Partition_ID) |
                    WK_WimpDrvsDevs_Unregistration_Op(to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
                        to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
                        green_pid:Partition_ID) */

datatype WSD_Trace = WSD_Trace(ws0:DM_State, ops:seq<WSD_Op>)




//******** Property of Each Operation ********//
predicate P_WSD_OSDrvRead_Op(ws:DM_State, op:WSD_Op)
    requires op.WSD_OSDrvReadOp?
{
    WSD_OSDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WSD_OSDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, t, ws', ws_d))
}

predicate P_WSD_WimpDrvRead_Op(ws:DM_State, op:WSD_Op)
    requires op.WSD_WimpDrvReadOp?
{
    WSD_WimpDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WSD_WimpDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, t, ws', ws_d))
}

predicate P_WSD_DevRead_Op(ws:DM_State, op:WSD_Op)
    requires op.WSD_DevRead_Op?
{
    WSD_DevRead_PreConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WSD_DevRead_PostConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, t, ws', ws_d))
}

predicate P_WSD_OSDrvWrite_Op(ws:DM_State, op:WSD_Op)
    requires op.WSD_OSDrvWrite_Op?
{
    WSD_OSDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WSD_OSDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d))
}

predicate P_WSD_WimpDrvWrite_Op(ws:DM_State, op:WSD_Op)
    requires op.WSD_WimpDrvWrite_Op?
{
    WSD_WimpDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WSD_WimpDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d))
}

predicate P_WSD_OSDevWrite_Op(ws:DM_State, op:WSD_Op)
    requires op.WSD_OSDevWrite_Op?
{
    WSD_OSDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WSD_OSDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d))
}

predicate P_WSD_WimpDevWrite_Op(ws:DM_State, op:WSD_Op)
    requires op.WSD_WimpDevWrite_Op?
{
    WSD_WimpDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WSD_WimpDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d))
}

predicate P_WKD_EmptyPartitionCreate_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_EmptyPartitionCreateOp?
{
    WKD_EmptyPartitionCreate_PreConditions(ws, op.new_pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_EmptyPartitionCreate_PostConditions(ws, op.new_pid, t, ws', ws_d))
}

predicate P_WKD_EmptyPartitionDestroy_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_EmptyPartitionDestroyOp?
{
    WKD_EmptyPartitionDestroy_PreConditions(ws, op.pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_EmptyPartitionDestroy_PostConditions(ws, op.pid, t, ws', ws_d))
}

predicate P_WKD_DrvActivateToGreenPartition_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_DrvActivateToGreenPartitionOp?
{
    WKD_DrvActivateToGreenPartition_PreConditions(ws, op.drv_sid, op.green_pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_DrvActivateToGreenPartition_PostConditions(ws, op.drv_sid, op.green_pid, t, ws', ws_d))
}

predicate P_WKD_GreenDrvDeactivate_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_GreenDrvDeactivateOp?
{
    WKD_GreenDrvDeactivate_PreConditions(ws, op.drv_sid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_GreenDrvDeactivate_PostConditions(ws, op.drv_sid, t, ws', ws_d))
}

predicate P_WKD_DevActivate_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_DevActivateOp?
{
    WKD_DevActivate_PreConditions(ws, op.dev_sid, op.pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_DevActivate_PostConditions(ws, op.dev_sid, op.pid, t, ws', ws_d))
}

predicate P_WKD_DevDeactivate_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_DevDeactivateOp?
{
    WKD_DevDeactivate_PreConditions(ws, op.dev_sid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_DevDeactivate_PostConditions(ws, op.dev_sid, t, ws', ws_d))
}

predicate P_WKD_ExternalObjsActivateToGreenPartition_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_ExternalObjsActivateToGreenPartitionOp?
{
    WKD_ExternalObjsActivateToGreenPartition_PreConditions(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_ExternalObjsActivateToGreenPartition_PostConditions(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid, t, ws', ws_d))
}

predicate P_WKD_ExternalObjsActivateToRedPartition_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_ExternalObjsActivateToRedPartitionOp?
{
    WKD_ExternalObjsActivateToRedPartition_PreConditions(ws, op.td_ids, op.fd_ids, op.do_ids)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_ExternalObjsActivateToRedPartition_PostConditions(ws, op.td_ids, op.fd_ids, op.do_ids, t, ws', ws_d))
}

predicate P_WKD_GreenExternalObjsDeactivate_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_GreenExternalObjsDeactivateOp?
{
    WKD_GreenExternalObjsDeactivate_PreConditions(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_GreenExternalObjsDeactivate_PostConditions(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid, t, ws', ws_d))
}

predicate P_WKD_RedExternalObjsDeactivate_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_RedExternalObjsDeactivateOp?
{
    WKD_RedExternalObjsDeactivate_PreConditions(ws, op.td_ids, op.fd_ids, op.do_ids)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_RedExternalObjsDeactivate_PostConditions(ws, op.td_ids, op.fd_ids, op.do_ids, t, ws', ws_d))
}

predicate P_WKD_MultiDevs_ReturnOS_Op(ws:DM_State, op:WSD_Op)
    requires op.WKD_MultiDevs_ReturnOSOp?
{
    WKD_MultiDevs_ReturnOS_PreConditions(ws, op.to_assign_dev_ids)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WKD_MultiDevs_ReturnOS_PostConditions(ws, op.to_assign_dev_ids, t, ws', ws_d))
}


/*
predicate P_WK_WimpDrvsDevs_Registration_CreatePartition_Op(ws:DM_State, op:WSD_Op)
    requires op.WK_WimpDrvsDevs_Registration_CreatePartition_Op?
{
    WK_WimpDrvsDevs_Registration_CreatePartition_PreConditions(ws)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WK_WimpDrvsDevs_Registration_CreatePartition_PostConditions(ws, t, ws', ws_d))
}

predicate P_WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op(ws:DM_State, op:WSD_Op)
    requires op.WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op?
{
    WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PreConditions(
                ws, op.to_deactivate_dev_id, op.to_assign_drv_ids, op.to_assign_dev_ids,
                op.to_assign_external_td_ids, op.to_assign_external_fd_ids, op.to_assign_external_do_ids, op.green_pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PostConditions(ws, 
                op.to_deactivate_dev_id, op.to_assign_drv_ids, op.to_assign_dev_ids,
                op.to_assign_external_td_ids, op.to_assign_external_fd_ids, op.to_assign_external_do_ids, op.green_pid, t, ws', ws_d))
}

predicate P_WK_WimpDrvsDevs_Unregistration_Op(ws:DM_State, op:WSD_Op)
    requires op.WK_WimpDrvsDevs_Unregistration_Op?
{
    WK_WimpDrvsDevs_Unregistration_PreConditions(
                ws, op.to_deactivate_drv_ids, op.to_deactivate_dev_ids, op.devs_to_activate_in_red,
                op.to_deactivate_external_td_ids, op.to_deactivate_external_fd_ids, op.to_deactivate_external_do_ids, op.green_pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WK_WimpDrvsDevs_Unregistration_PostConditions(ws, 
                op.to_deactivate_drv_ids, op.to_deactivate_dev_ids, op.devs_to_activate_in_red,
                op.to_deactivate_external_td_ids, op.to_deactivate_external_fd_ids, op.to_deactivate_external_do_ids, op.green_pid, t, ws', ws_d))
}
*/



//******** PreConditions and PostConditions of Operations ********//
predicate WSD_OSDrvRead_PreConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_RedDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
}

predicate WSD_OSDrvRead_PostConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_OSDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    (true)
}

predicate WSD_WimpDrvRead_PreConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_GreenDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
}

predicate WSD_WimpDrvRead_PostConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_WimpDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    (true)
}

predicate WSD_DevRead_PreConditions(
    ws:DM_State, dev_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_DevRead_PreConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
}

predicate WSD_DevRead_PostConditions(
    ws:DM_State, dev_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_DevRead_PreConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, dev_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device
        
    (true)
}

predicate WSD_OSDrvWrite_PreConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}

predicate WSD_OSDrvWrite_PostConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_OSDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    (true)
}

predicate WSD_WimpDrvWrite_PreConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_GreenDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}

predicate WSD_WimpDrvWrite_PostConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_WimpDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    (true)
}

predicate WSD_OSDevWrite_PreConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_RedDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}

predicate WSD_OSDevWrite_PostConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_OSDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    ((forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))) &&
        // Properties needed by the following property
    (P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device
        
    (true)
}

predicate WSD_WimpDevWrite_PreConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_GreenDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}

predicate WSD_WimpDevWrite_PostConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WSD_WimpDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    ((forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(ws.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(ws.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(ws.objects))) &&
        // Properties needed by the following property
    (P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device
        
    (true)
}

predicate WKD_EmptyPartitionCreate_PreConditions(
    ws:DM_State, new_pid:Partition_ID
)
{
    DM_IsValidState(ws) && DM_IsSecureState(ws)
}

predicate WKD_EmptyPartitionCreate_PostConditions(
    ws:DM_State, new_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_EmptyPartitionCreate_PreConditions(ws, new_pid)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WKD_EmptyPartitionDestroy_PreConditions(
    ws:DM_State, pid:Partition_ID
)
{
    DM_IsValidState(ws) && DM_IsSecureState(ws)
}

predicate WKD_EmptyPartitionDestroy_PostConditions(
    ws:DM_State, pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_EmptyPartitionDestroy_PreConditions(ws, pid)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WKD_DrvActivateToGreenPartition_PreConditions(
    ws:DM_State, drv_sid:Subject_ID, green_pid:Partition_ID
)
{
    DM_IsValidState(ws) && DM_IsSecureState(ws) &&
    Drv_ID(drv_sid) in ws.subjects.drvs &&
    green_pid != NULL &&
    green_pid != ws.red_pid
}

predicate WKD_DrvActivateToGreenPartition_PostConditions(
    ws:DM_State, drv_sid:Subject_ID, green_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_DrvActivateToGreenPartition_PreConditions(ws, drv_sid, green_pid)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WKD_GreenDrvDeactivate_PreConditions(
    ws:DM_State, drv_sid:Subject_ID
)
{
    DM_IsValidState(ws) && DM_IsSecureState(ws) &&
    Drv_ID(drv_sid) in ws.subjects.drvs &&
    DM_SubjPID(ws.subjects, drv_sid) != NULL &&
    DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
}

predicate WKD_GreenDrvDeactivate_PostConditions(
    ws:DM_State, drv_sid:Subject_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_GreenDrvDeactivate_PreConditions(ws, drv_sid)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WKD_DevActivate_PreConditions(
    ws:DM_State, dev_sid:Subject_ID, pid:Partition_ID
)
{
    DM_IsValidState(ws) && DM_IsSecureState(ws) &&
    Dev_ID(dev_sid) in ws.subjects.devs &&
    pid != NULL
}

predicate WKD_DevActivate_PostConditions(
    ws:DM_State, dev_sid:Subject_ID, pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_DevActivate_PreConditions(ws, dev_sid, pid)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WKD_DevDeactivate_PreConditions(
    ws:DM_State, dev_sid:Subject_ID
)
{
    DM_DevDeactivate_PreConditions(ws, dev_sid)
}

predicate WKD_DevDeactivate_PostConditions(
    ws:DM_State, dev_sid:Subject_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_DevDeactivate_PreConditions(ws, dev_sid)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WKD_ExternalObjsActivateToGreenPartition_PreConditions(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID
)
{
    DM_ExternalObjsActivateToGreenPartition_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)
}

predicate WKD_ExternalObjsActivateToGreenPartition_PostConditions(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_ExternalObjsActivateToGreenPartition_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WKD_ExternalObjsActivateToRedPartition_PreConditions(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
{
    DM_ExternalObjsActivateToRedPartition_PreConditions(ws, td_ids, fd_ids, do_ids)
}

predicate WKD_ExternalObjsActivateToRedPartition_PostConditions(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_ExternalObjsActivateToRedPartition_PreConditions(ws, td_ids, fd_ids, do_ids)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WKD_GreenExternalObjsDeactivate_PreConditions(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID
)
{
    DM_GreenExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)
}

predicate WKD_GreenExternalObjsDeactivate_PostConditions(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_GreenExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids, green_pid)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WKD_RedExternalObjsDeactivate_PreConditions(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
{
    DM_RedExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids)
}

predicate WKD_RedExternalObjsDeactivate_PostConditions(
    ws:DM_State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_RedExternalObjsDeactivate_PreConditions(ws, td_ids, fd_ids, do_ids)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&
        
    (true)
}

predicate WK_Access_Common_PostConditions(
    ws:DM_State, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
{
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();

    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&

    (t.ws0 == ws) &&
    (DM_IsValidTrace(t)) &&
    (ws' == SeqLastElem(DM_CalcNewStates(t))) &&

    (true)
}

predicate WKD_MultiDevs_ReturnOS_PreConditions(
    ws:DM_State, to_assign_dev_ids:seq<Dev_ID>
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (forall i, j :: 0 <= i < |to_assign_dev_ids| && 0 <= j < |to_assign_dev_ids|
                ==> (i == j <==> to_assign_dev_ids[i] == to_assign_dev_ids[j])) &&
        // Requirement: No duplicate device ID in <to_assign_dev_ids>
    (forall id :: id in to_assign_dev_ids ==> id in ws.subjects.devs) &&
    (|to_assign_dev_ids| >= 0) &&

    (true)
}

predicate WKD_MultiDevs_ReturnOS_PostConditions(
    ws:DM_State, to_assign_dev_ids:seq<Dev_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WKD_MultiDevs_ReturnOS_PreConditions(ws, to_assign_dev_ids)
{
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    (ws_d == true ==> t.ws0 == ws) &&
    (ws_d == true ==> t.ops == DevActivateMulti_ToTraceOps(to_assign_dev_ids, ws.red_pid)) &&
    (ws_d == true ==> DM_IsValidTrace(t)) &&

    (!ws_d ==> t == DM_Trace(ws, [])) &&
    (!ws_d ==> ws' == ws) &&
    (!ws_d ==> DM_IsValidTrace(t)) &&
        // Property: If returns false, then stays at the same state

    (ws' == SeqLastElem(DM_CalcNewStates(t))) &&

    (true)
}



/*
predicate WK_WimpDrvsDevs_Registration_CreatePartition_PreConditions(
    ws:DM_State
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&

    (true)
}

predicate WK_WimpDrvsDevs_Registration_CreatePartition_PostConditions(
    ws:DM_State, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Registration_CreatePartition_PreConditions(ws)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    (ws_d == true ==> t.ws0 == ws) &&
    (ws_d == true ==> DM_IsValidTrace(t)) &&

    (!ws_d ==> t == DM_Trace(ws, [])) &&
    (!ws_d ==> ws' == ws) &&
    (!ws_d ==> DM_IsValidTrace(t)) &&
        // Property: If returns false, then stays at the same state

    (ws' == SeqLastElem(DM_CalcNewStates(t))) &&

    (true)
}

predicate WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PreConditions(
    ws:DM_State, to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&

    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&

    (to_deactivate_dev_id in ws.subjects.devs) &&
    (DM_SubjPID(ws.subjects, to_deactivate_dev_id.sid) == ws.red_pid) &&
    (P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, to_deactivate_dev_id)) &&
        // Requirement: For the device to be deactivated

    (forall i, j :: 0 <= i < |to_assign_drv_ids| && 0 <= j < |to_assign_drv_ids|
                ==> (i == j <==> to_assign_drv_ids[i] == to_assign_drv_ids[j])) &&
        // Requirement: No duplicate device ID in <to_assign_drv_ids>
    (forall i, j :: 0 <= i < |to_assign_dev_ids| && 0 <= j < |to_assign_dev_ids|
                ==> (i == j <==> to_assign_dev_ids[i] == to_assign_dev_ids[j])) &&
        // Requirement: No duplicate device ID in <to_assign_dev_ids>
    (forall id :: id in to_assign_drv_ids ==> id in ws.subjects.drvs) &&
    (|to_assign_drv_ids| >= 0) &&
    (forall id :: id in to_assign_dev_ids ==> id in ws.subjects.devs) &&
    (|to_assign_dev_ids| >= 0) &&

    (to_assign_external_td_ids <= DM_AllTDIDs(ws.objects)) &&
    (to_assign_external_fd_ids <= DM_AllFDIDs(ws.objects)) &&
    (to_assign_external_do_ids <= DM_AllDOIDs(ws.objects)) &&

    (forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)) &&
        // Requirement: No subject owns these external objects

    (green_pid != NULL) &&
    (green_pid != ws.red_pid) &&
    (green_pid in ws.pids) &&
        // Requirement: We have already create a green partition

    (true)
}

predicate WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PostConditions(
    ws:DM_State, to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PreConditions(
                ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids,
                green_pid)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    (ws_d == true ==> t.ws0 == ws) &&
    (ws_d == true ==> t.ops == [DM_DevDeactivateOp(to_deactivate_dev_id.sid)] + DevActivateMulti_ToTraceOps(to_assign_dev_ids, green_pid) +
                                    WimpDrvActivateMulti_ToTraceOps(to_assign_drv_ids, green_pid) + 
                                    [DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid)]) &&
    (ws_d == true ==> DM_IsValidTrace(t)) &&

    (!ws_d ==> t == DM_Trace(ws, [])) &&
    (!ws_d ==> ws' == ws) &&
    (!ws_d ==> DM_IsValidTrace(t)) &&
        // Property: If returns false, then stays at the same state

    (ws' == SeqLastElem(DM_CalcNewStates(t))) &&

    (true)
}

predicate WK_WimpDrvsDevs_Unregistration_PreConditions(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&

    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&

    (forall i, j :: 0 <= i < |to_deactivate_drv_ids| && 0 <= j < |to_deactivate_drv_ids|
                ==> (i == j <==> to_deactivate_drv_ids[i] == to_deactivate_drv_ids[j])) &&
        // Requirement: No duplicate device ID in <to_deactivate_drv_ids>
    (forall i, j :: 0 <= i < |to_deactivate_dev_ids| && 0 <= j < |to_deactivate_dev_ids|
                ==> (i == j <==> to_deactivate_dev_ids[i] == to_deactivate_dev_ids[j])) &&
        // Requirement: No duplicate device ID in <to_deactivate_dev_ids>
    (forall id :: id in to_deactivate_drv_ids ==> id in ws.subjects.drvs) &&
    (|to_deactivate_drv_ids| >= 0) &&
    (forall id :: id in to_deactivate_dev_ids ==> id in ws.subjects.devs) &&
    (|to_deactivate_dev_ids| >= 0) &&

    (forall id :: id in to_deactivate_drv_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid) &&
    (forall id :: id in to_deactivate_dev_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid) &&
        // Requirement: Drivers and devices to be deactivated must be from the 
        // green partition

    (forall i, j :: 0 <= i < |devs_to_activate_in_red| && 0 <= j < |devs_to_activate_in_red|
                ==> (i == j <==> devs_to_activate_in_red[i] == devs_to_activate_in_red[j])) &&
        // Requirement: No duplicate device ID in <devs_to_activate_in_red>
    (forall id :: id in devs_to_activate_in_red ==> id in ws.subjects.devs) &&
    (|devs_to_activate_in_red| >= 0) &&
        // Requirement: Devices to be activated in the red partition must be 
        // existing devices

    (to_deactivate_external_td_ids <= DM_AllTDIDs(ws.objects)) &&
    (to_deactivate_external_fd_ids <= DM_AllFDIDs(ws.objects)) &&
    (to_deactivate_external_do_ids <= DM_AllDOIDs(ws.objects)) &&
    (forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_deactivate_external_td_ids) + FDIDsToObjIDs(to_deactivate_external_fd_ids) + DOIDsToObjIDs(to_deactivate_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)) &&
    (forall id :: id in to_deactivate_external_td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid) &&
    (forall id :: id in to_deactivate_external_fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid) &&
    (forall id :: id in to_deactivate_external_do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid) &&
        // Requirement: External objects to be deactivated must be from the 
        // green partition

    (green_pid != NULL) &&
    (green_pid != ws.red_pid) &&
    (green_pid in ws.pids) &&
        // Requirement: A green partition to be destroyed

    (true)
}

predicate WK_WimpDrvsDevs_Unregistration_PostConditions(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Unregistration_PreConditions(
                ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
                green_pid)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    (ws_d == true ==> t.ws0 == ws) &&
    (ws_d == true ==> t.ops == [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)] +
                                WimpDrvDeactivateMulti_ToTraceOps(to_deactivate_drv_ids) +
                                GreenDevDeactivateMulti_ToTraceOps(to_deactivate_dev_ids) +
                                DevActivateMulti_ToTraceOps(devs_to_activate_in_red, ws.red_pid) +
                                [DM_EmptyPartitionDestroyOp(green_pid)]) &&
    (ws_d == true ==> DM_IsValidTrace(t)) &&

    (!ws_d ==> t == DM_Trace(ws, [])) &&
    (!ws_d ==> ws' == ws) &&
    (!ws_d ==> DM_IsValidTrace(t)) &&
        // Property: If returns false, then stays at the same state

    (ws' == SeqLastElem(DM_CalcNewStates(t))) &&

    (true)
}

*/