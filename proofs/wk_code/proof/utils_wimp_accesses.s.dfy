include "DM_AdditionalPredicates.s.dfy"
include "DM_Operations_Stubs.s.dfy"
include "state_map_OpsSaneState.i.dfy"
include "../state_properties_OpsSaneStateSubset.s.dfy"
include "../../WK_Design/Model.dfy"

// P_WimpDrvAccess_AccessActiveObjsOnly
predicate WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s:state, drv_sid:Subject_ID, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WSM_IsWimpDrvID(s.subjects, Drv_ID(drv_sid))
{
    var globals := wkm_get_globals(s.wk_mstate);

    (forall td_id :: td_id in td_ids ==> td_id in WSM_AllTDIDs(s.objects)) &&
    (forall fd_id :: fd_id in fd_ids ==> fd_id in WSM_AllFDIDs(s.objects)) &&
    (forall do_id :: do_id in do_ids ==> do_id in WSM_AllDOIDs(s.objects)) &&

    (forall id :: id in td_ids
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) &&
    (forall id :: id in fd_ids
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) &&
    (forall id :: id in do_ids
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid))
}




/*********************** Utility Functions and Predicates ********************/
// Predicate: If a USBPDev writes to a set of FDs/DOs with some values, then the device must be able to write 
// the corresponding objects with the corresponding values in the WK design model
predicate WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(
    s:state, dev_sid:Subject_ID, 
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires WSM_IsDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    (forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(dm, dev_sid, td_id2, td_id_val_map[td_id2])) &&
    (forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(dm, dev_sid, fd_id2, fd_id_val_map[fd_id2])) &&
    (forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(dm, dev_sid, do_id2, do_id_val_map[do_id2]))
}