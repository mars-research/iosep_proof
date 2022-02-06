include "utils_wimp_accesses.s.dfy"
//include "io_accesses_ops_lemmas.i.dfy"
include "../state_properties_OpsSaneStateSubset.i.dfy"
include "../wk_partition_ops_utils.s.dfy"
include "../dev/usb2/eehci_validstate.i.dfy"
include "../dev/usb2/usb_pdev_validstate.i.dfy"
include "../dev/usb2/usb_pdev_utils.i.dfy"
include "../dev/usb2/eehci_ops_impl.gen.dfy"
include "../dev/usb2/usb_tds_ops/usb_tds_ops_impl.gen.dfy"
include "../os/os_ops_impl.gen.dfy"
//include "../os/os_ops.gen.dfy"
include "DM_AdditionalPropertiesLemmas.i.dfy"
include "io_accesses_commutative_diagram.i.dfy"

/*********************** Axioms ********************/
// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WK_EmptyPartitionCreate_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    pid_slot:uint32, new_pid:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             wk_create_partition_globalvars_relation(globals, globals', pid_slot, new_pid)
        // Requirement: WK_EmptyPartitionCreate modifies global variables correctly

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    ensures var new_pids := dm.pids + {WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid))};
            dm' == dm.(pids := new_pids)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WK_EmptyPartitionDestroy_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    pid:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             wk_destroy_partition_globalvars_relation(globals, globals', pid)
        // Requirement: WK_EmptyPartitionCreate modifies global variables correctly

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    ensures var new_pids := dm.pids - {WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(pid))};
            dm' == dm.(pids := new_pids)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WimpDrv_Activate_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    drv_slot:uint32, new_wimpdrv_idword:uint32, new_wimpdrv_pid:uint32, new_do_pbase:paddr, new_do_pend:paddr
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires new_wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword) in s.subjects.wimp_drvs 
        // Properties needed by the following requirement
    requires state_equal_except_mstate_objs(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             wimpdrv_info_newvalue(globals, globals', drv_slot, new_wimpdrv_idword, new_wimpdrv_pid, new_do_pbase, new_do_pend, WimpDrv_Slot_UpdateFlag_Complete) &&
             wimpdrv_DO_clear_non_mstate_relationship(s, s', new_wimpdrv_idword)
        // Requirement: WimpDrv_Activate modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_wimpdrv_pid));
             var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword);
             WKD_DrvActivateToGreenPartition_PreConditions(dm, wimpdrv_id.sid, dm_new_pid);
      
    ensures var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_wimpdrv_pid));
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword);

            var drv_state := dm.subjects.drvs[wimpdrv_id];
            var new_drv_state := Drv_State(dm_new_pid, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
            var new_drvs := dm.subjects.drvs[wimpdrv_id := new_drv_state];
            var new_subjects := Subjects(new_drvs, dm.subjects.devs);

            var tds_owned_by_drv:set<TD_ID> := dm.subjects.drvs[wimpdrv_id].td_ids;
            var fds_owned_by_drv:set<FD_ID> := dm.subjects.drvs[wimpdrv_id].fd_ids;
            var dos_owned_by_drv:set<DO_ID> := dm.subjects.drvs[wimpdrv_id].do_ids;
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(dm.objects, tds_owned_by_drv, dm_new_pid);
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_drv, dm_new_pid);

            (forall do_id:: do_id in dos_owned_by_drv ==> do_id in t_objs2.inactive_dos) &&
                // [NOTE] This property has been proved in <DM_DrvActivateToGreenPartition_InnerFunc> in the concrete model
            var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_drv, dm_new_pid);
            dm' == dm.(subjects := new_subjects, objects := new_objects)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_USBPDev_Activate_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    usbpdev_slot:uint32, new_pid:uint32, new_usbpdev_addr_low:paddr, new_usbpdev_addr_high:paddr
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(new_usbpdev_addr_raw) &&
             usb_is_usbpdev_addr_valid(empty_addr) &&
             usb_parse_usbpdev_addr(new_usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr)
    requires var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
             var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
             var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);
             usbpdev_id in s.subjects.usbpdevs
        // Properties needed by the following requirement
    requires state_equal_except_mstate_objs(s, s');       
    requires var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
             var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
             var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             usbpdev_info_newvalue(globals, globals', usbpdev_slot, new_usbpdev_addr_low, new_usbpdev_addr_high, new_pid, WimpUSBPDev_Slot_UpdateFlag_Complete) &&
             usbpdev_clear_non_mstate_relationship(s, s', new_usbpdev_addr);
        // Requirement: USBPDev_Activate modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
            var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);
            WKD_DevActivate_PreConditions(dm, usbpdev_id.sid, dm_pid)
      
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
            var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);

            var dev_state := dm.subjects.devs[usbpdev_id];
            var new_dev_state := Dev_State(dm_pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
            var new_devs := dm.subjects.devs[usbpdev_id := new_dev_state];
            var new_subjects := Subjects(dm.subjects.drvs, new_devs);

            var tds_owned_by_dev:set<TD_ID> := dm.subjects.devs[usbpdev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := dm.subjects.devs[usbpdev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := dm.subjects.devs[usbpdev_id].do_ids;
            var toactive_hcoded_td_id := dev_state.hcoded_td_id;
            var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};

            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(dm.objects, toclear_td_ids, dm_pid);
            (forall id:: id in fds_owned_by_dev ==> id in t_objs1.inactive_fds) &&
                // [NOTE] This property has been proved in <DM_DevActivate_InnerFunc> in the concrete model
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, dm_pid);
            (forall id:: id in dos_owned_by_dev ==> id in t_objs2.inactive_dos) &&
                // [NOTE] This property has been proved in <DM_DevActivate_InnerFunc> in the concrete model
            var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, dm_pid);
            var new_objects := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, dm_pid);
            dm' == dm.(subjects := new_subjects, objects := new_objects)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_EEHCI_Activate_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    eehci_slot:uint32, new_pid:uint32, eehci_idword:word, eehci_handle:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_idword != eEHCI_ID_INVALID
    requires var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
             eehci_id in s.subjects.eehcis
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             eechi_activate_globalvars_relation(globals, globals', eehci_slot, eehci_idword, eehci_handle, new_pid)
        // Requirement: EEHCI_Activate modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
             var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
             WKD_DevActivate_PreConditions(dm, eehci_id.sid, dm_pid)
      
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);

            var dev_state := dm.subjects.devs[eehci_id];
            var new_dev_state := Dev_State(dm_pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
            var new_devs := dm.subjects.devs[eehci_id := new_dev_state];
            var new_subjects := Subjects(dm.subjects.drvs, new_devs);

            var tds_owned_by_dev:set<TD_ID> := dm.subjects.devs[eehci_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := dm.subjects.devs[eehci_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := dm.subjects.devs[eehci_id].do_ids;
            var toactive_hcoded_td_id := dev_state.hcoded_td_id;
            var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};

            (forall id:: id in toclear_td_ids ==> id in dm.objects.inactive_non_hcoded_tds) &&
                 // [NOTE] This property has been proved in <DM_DevActivate_InnerFunc> in the concrete model
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(dm.objects, toclear_td_ids, dm_pid);
            (forall id:: id in fds_owned_by_dev ==> id in t_objs1.inactive_fds) &&
                // [NOTE] This property has been proved in <DM_DevActivate_InnerFunc> in the concrete model
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, dm_pid);
            (forall id:: id in dos_owned_by_dev ==> id in t_objs2.inactive_dos) &&
                // [NOTE] This property has been proved in <DM_DevActivate_InnerFunc> in the concrete model
            var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, dm_pid);
            var new_objects := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, dm_pid);
            dm' == dm.(subjects := new_subjects, objects := new_objects)


// [State/Ops Mapping] Axiom (well known): If no USB TD refs a wimp driver's DOs, then no green TDs ref the wimp 
// driver's DOs
lemma {:axiom} Lemma_WimpDrv_Deactivate_NoGreenTDRefsWimpDrvToBeDeactivated(
    s:state, dm:DM_State,
    drv_slot:uint32
)
    requires OpsSaneState(s)
    requires dm == WSM_MapState(s)

    requires wimpdrv_valid_slot_id(drv_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
             wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, wimpdrv_get_pid(globals, drv_slot).v)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtds_verifiedtds_do_not_associate_wimpdrv(globals, drv_slot)
        // Requirement: The condition when WimpDrv_Activate returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var todeactivate_td_ids := dm.subjects.drvs[wimpdrv_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.drvs[wimpdrv_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.drvs[wimpdrv_id].do_ids;
            todeactivate_td_ids == {} &&
            todeactivate_fd_ids == {} &&
            todeactivate_do_ids == {s.subjects.wimp_drvs[wimpdrv_id].do_id}

    requires P_DMObjectsHasUniqueIDs(dm.objects)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var todeactivate_td_ids := dm.subjects.drvs[wimpdrv_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.drvs[wimpdrv_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.drvs[wimpdrv_id].do_ids;
            var pid := DM_SubjPID(dm.subjects, wimpdrv_id.sid);
            (forall id :: id in todeactivate_do_ids
                    ==> id in DM_AllDOIDs(dm.objects)) &&
            pid != NULL &&
            pid != dm.red_pid
        // Properties needed by the following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var todeactivate_td_ids := dm.subjects.drvs[wimpdrv_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.drvs[wimpdrv_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.drvs[wimpdrv_id].do_ids;
            var pid := DM_SubjPID(dm.subjects, wimpdrv_id.sid);
            DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(dm, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WimpDrv_Deactivate_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    drv_slot:uint32
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(drv_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
             wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             wimpdrv_get_pid(globals', drv_slot) == WS_PartitionID(PID_INVALID) &&
             wimpdrv_info_newvalue(globals, globals', drv_slot, WimpDrv_ID_RESERVED_EMPTY, PID_INVALID, 0, 0, WimpDrv_Slot_UpdateFlag_Complete)
        // Requirement: WimpDrv_Deactivate modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
             var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
             WKD_GreenDrvDeactivate_PreConditions(dm, wimpdrv_id.sid)
      
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);

            var drv_state := dm.subjects.drvs[wimpdrv_id];
            var new_drv_state := Drv_State(NULL, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
            var new_drvs := dm.subjects.drvs[wimpdrv_id := new_drv_state];
            var new_subjects := Subjects(new_drvs, dm.subjects.devs);

            var tds_owned_by_drv:set<TD_ID> := dm.subjects.drvs[wimpdrv_id].td_ids;
            var fds_owned_by_drv:set<FD_ID> := dm.subjects.drvs[wimpdrv_id].fd_ids;
            var dos_owned_by_drv:set<DO_ID> := dm.subjects.drvs[wimpdrv_id].do_ids;
            (forall id:: id in tds_owned_by_drv ==> id in dm.objects.active_non_hcoded_tds) &&
                // [NOTE] This property has been proved in <DM_GreenDrvDeactivate_InnerFunc> in the concrete model
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(dm.objects, tds_owned_by_drv);
            (forall id:: id in fds_owned_by_drv ==> id in t_objs1.active_fds) &&
                // [NOTE] This property has been proved in <DM_GreenDrvDeactivate_InnerFunc> in the concrete model
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_drv);
            (forall id:: id in dos_owned_by_drv ==> id in t_objs2.active_dos) &&
                // [NOTE] This property has been proved in <DM_GreenDrvDeactivate_InnerFunc> in the concrete model
            var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_drv);
            dm' == dm.(subjects := new_subjects, objects := new_objects)


// [State/Ops Mapping] Axiom (well known): If no USB TD refs a USBPDev's objects, then no green TDs ref the USBPDev
lemma {:axiom} Lemma_USBPDev_Deactivate_NoGreenTDRefsWimpDrvToBeDeactivated(
    s:state, dm:DM_State,
    usbpdev_slot:uint32
)
    requires OpsSaneState(s)
    requires dm == WSM_MapState(s)

    requires usbpdev_valid_slot_id(usbpdev_slot)
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, usbpdev_get_pid(globals, usbpdev_slot).v)
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbpdev_get_updateflag(globals, usbpdev_slot) == WimpUSBPDev_Slot_UpdateFlag_Complete
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtds_verifiedtds_do_not_associate_usb_pdev(globals, usbpdev_slot)
        // Requirement: The condition when USBPDev_Deactivate returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var empty_addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
            usb_is_usbpdev_addr_valid(empty_addr_raw) &&
            usb_is_usbpdev_addr_valid(usbpdev_addr_raw) &&
            usb_parse_usbpdev_addr(usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr_raw)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            usbpdev_id in s.subjects.usbpdevs

    requires P_DMObjectsHasUniqueIDs(dm.objects)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            var todeactivate_td_ids := dm.subjects.devs[usbpdev_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.devs[usbpdev_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.devs[usbpdev_id].do_ids;
            var pid := DM_SubjPID(dm.subjects, usbpdev_id.sid);
            (forall id :: id in todeactivate_fd_ids
                ==> id in DM_AllFDIDs(dm.objects)) &&
            (forall id :: id in todeactivate_do_ids
                    ==> id in DM_AllDOIDs(dm.objects)) &&
            pid != NULL &&
            pid != dm.red_pid
        // Properties needed by the following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            var todeactivate_td_ids := dm.subjects.devs[usbpdev_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.devs[usbpdev_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.devs[usbpdev_id].do_ids;
            var pid := DM_SubjPID(dm.subjects, usbpdev_id.sid);
            DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(dm, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_USBPDev_Deactivate_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    usbpdev_slot:uint32
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires usbpdev_valid_slot_id(usbpdev_slot)
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             usbpdev_get_pid(globals', usbpdev_slot) == WS_PartitionID(PID_INVALID) &&
             usbpdev_info_newvalue(globals, globals', usbpdev_slot, WimpUSBPDev_ADDR_EMPTY_LOW, WimpUSBPDev_ADDR_EMPTY_HIGH, PID_INVALID, WimpUSBPDev_Slot_UpdateFlag_Complete)
        // Requirement: USBPDev_Deactivate modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var empty_addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
            usb_is_usbpdev_addr_valid(empty_addr_raw) &&
            usb_is_usbpdev_addr_valid(usbpdev_addr_raw) &&
            usb_parse_usbpdev_addr(usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr_raw)
    requires var globals := wkm_get_globals(s.wk_mstate);
             var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
             var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
             var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
             WKD_DevDeactivate_PreConditions(dm, usbpdev_id.sid)
      
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);

            var dev_state := dm.subjects.devs[usbpdev_id];
            var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
            var new_devs := dm.subjects.devs[usbpdev_id := new_dev_state];
            var new_subjects := Subjects(dm.subjects.drvs, new_devs);

            var tds_owned_by_dev:set<TD_ID> := dm.subjects.devs[usbpdev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := dm.subjects.devs[usbpdev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := dm.subjects.devs[usbpdev_id].do_ids;
            var todeactive_hcoded_td_id := dev_state.hcoded_td_id;
            var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
            (forall id:: id in todeactive_other_td_ids ==> id in dm.objects.active_non_hcoded_tds) &&
                // [NOTE] This property has been proved in <DM_DevDeactivate_InnerFunc> in the concrete model
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(dm.objects, todeactive_other_td_ids);
            (forall id:: id in fds_owned_by_dev ==> id in t_objs1.active_fds) &&
                // [NOTE] This property has been proved in <DM_DevDeactivate_InnerFunc> in the concrete model
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
            (forall id:: id in dos_owned_by_dev ==> id in t_objs2.active_dos) &&
                // [NOTE] This property has been proved in <DM_DevDeactivate_InnerFunc> in the concrete model
            var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
            var new_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);
            dm' == dm.(subjects := new_subjects, objects := new_objects)


// [State/Ops Mapping] Axiom (well known): No green TDs ref eEHCIs
lemma {:axiom} Lemma_EEHCI_Deactivate_NoGreenTDRefsWimpDrvToBeDeactivated(
    s:state, dm:DM_State,
    eehci_slot:uint32
)
    requires OpsSaneState(s)
    requires dm == WSM_MapState(s)

    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, eehci_info_get_pid(globals, eehci_slot).v)
        // Requirement: The condition when USBPDev_Deactivate returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis

    requires P_DMObjectsHasUniqueIDs(dm.objects)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            var todeactivate_td_ids := dm.subjects.devs[eehci_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.devs[eehci_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.devs[eehci_id].do_ids;
            var pid := DM_SubjPID(dm.subjects, eehci_id.sid);
            (forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(dm.objects)) &&
            (forall id :: id in todeactivate_fd_ids
                ==> id in DM_AllFDIDs(dm.objects)) &&
            (forall id :: id in todeactivate_do_ids
                    ==> id in DM_AllDOIDs(dm.objects)) &&
            pid != NULL &&
            pid != dm.red_pid
        // Properties needed by the following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            var todeactivate_td_ids := dm.subjects.devs[eehci_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.devs[eehci_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.devs[eehci_id].do_ids;
            var pid := DM_SubjPID(dm.subjects, eehci_id.sid);
            DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(dm, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_EEHCI_Deactivate_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    eehci_slot:uint32
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             eechi_deactivate_globalvars_relation(globals, globals', eehci_slot)
        // Requirement: USBPDev_Deactivate modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
             WKD_DevDeactivate_PreConditions(dm, eehci_id.sid)
      
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);

            var dev_state := dm.subjects.devs[eehci_id];
            var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
            var new_devs := dm.subjects.devs[eehci_id := new_dev_state];
            var new_subjects := Subjects(dm.subjects.drvs, new_devs);

            var tds_owned_by_dev:set<TD_ID> := dm.subjects.devs[eehci_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := dm.subjects.devs[eehci_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := dm.subjects.devs[eehci_id].do_ids;
            var todeactive_hcoded_td_id := dev_state.hcoded_td_id;
            var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
            (forall id:: id in todeactive_other_td_ids ==> id in dm.objects.active_non_hcoded_tds) &&
                // [NOTE] This property has been proved in <DM_DevDeactivate_InnerFunc> in the concrete model
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(dm.objects, todeactive_other_td_ids);
            (forall id:: id in fds_owned_by_dev ==> id in t_objs1.active_fds) &&
                // [NOTE] This property has been proved in <DM_DevDeactivate_InnerFunc> in the concrete model
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
            (forall id:: id in dos_owned_by_dev ==> id in t_objs2.active_dos) &&
                // [NOTE] This property has been proved in <DM_DevDeactivate_InnerFunc> in the concrete model
            var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
            var new_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);
            dm' == dm.(subjects := new_subjects, objects := new_objects)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WimpDrv_WriteEEHCIFDDO_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    wimpdrv_slot:word, eehci_slot:word, reg_offset:word, new_v:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || 
             reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset

    requires state_equal_except_mstate(s, s');
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + reg_offset;
             is_valid_vaddr(vaddr) &&
             globals' == global_write_word(globals, G_EEHCI_MEM(), vaddr, new_v)
        // Requirement: WimpDrv_Write modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
             wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
             var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
             var temp := F_WimpDrvWriteEEHCIFDDO_MapWritingAbstractObjsVals(s, eehci_slot, reg_offset, new_v);
             var fd_id_val_map:map<FD_ID, FD_Val> := temp.0;
             var do_id_val_map:map<DO_ID, DO_Val> := temp.1;
             WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, map[], fd_id_val_map, do_id_val_map)
      
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvWriteEEHCIFDDO_MapWritingAbstractObjsVals(s, eehci_slot, reg_offset, new_v);
            var td_id_val_map:map<TD_ID, TD_Val> := map[];
            var fd_id_val_map:map<FD_ID, FD_Val> := temp.0;
            var do_id_val_map:map<DO_ID, DO_Val> := temp.1;

            var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, td_id_val_map);
            (forall id:: id in fd_id_val_map ==> id in t_objs1.active_fds) &&
                // [NOTE] This property has been proved in <DM_GreenDrvWrite_InnerFunc> in the concrete model
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            (forall id:: id in do_id_val_map ==> id in t_objs2.active_dos) &&
                // [NOTE] This property has been proved in <DM_DevDeactivate_InnerFunc> in the concrete model
            var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
            var new_objects := t_objs3;
            dm' == dm.(objects := new_objects)


// Function: Convert wimp driver's write to eEHCIs' USBTD Regs to abstract objects and values
function {:axiom} F_WimpDrvWriteEEHCIUSBTDReg_MapWritingAbstractObjsVals(
    s:state, s':state, eehci_slot:word, usbtd_reg_id:word, new_v:word
) : (result:(map<TD_ID, TD_Val>, map<FD_ID, FD_Val>, map<DO_ID, DO_Val>))
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')
        // Requirement: In the state s' after the write, WK_EEHCI_Mem_SecureGlobalVarValues(globals') must hold.
        // That is, all eEHCIs' USB TD regs either are USBTD_SlotID_INVALID, or ref secure/verified USB TDs

    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + 
                            G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES;
             is_valid_vaddr(vaddr) &&
             globals' == global_write_word(globals, G_EEHCI_MEM(), vaddr, new_v)
        // Requirement: WimpDrv_Write modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis

    ensures new_v == USBTD_SlotID_INVALID
                ==> result == (map[], map[], map[])
        // Property: If new_v is USBTD_SlotID_INVALID, then returned maps should be empty
    ensures (forall id :: id in result.0
                ==> id in s.objects.usbtd_tds) &&
            (forall id :: id in result.1
                ==> id in s.objects.usbtd_fds) &&
            (forall id :: id in result.2
                ==> id in s.objects.usbtd_dos)
        // Property: If the returned maps are not empty, then the objects must be in usbtd_*
    ensures var globals := wkm_get_globals(s.wk_mstate);
            usbtd_map_valid_slot_id(new_v)
                ==> (
                        var usbtd_idword := usbtd_map_get_idword(globals, new_v);
                        (forall id :: id in result.0
                            ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
                        (forall id :: id in result.1
                            ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
                        (forall id :: id in result.2
                            ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword)
                )
        // Property: The objects in the result all maps to the USB TD <usbtd_idword> at the slot <new_v>

    ensures var dm := WSM_MapSecureState(s);
            var td_id_val_map := result.0;
            (forall td_id :: td_id in td_id_val_map ==> td_id in dm.objects.active_non_hcoded_tds) &&
            (forall id :: id in td_id_val_map
                ==> DM_ObjPID(dm.objects, id.oid) != NULL) &&
            DM_GreenDrvWrite_ChkNewValsOfTDs(dm, td_id_val_map)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WimpDrv_WriteEEHCIUSBTDReg_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    wimpdrv_slot:word, eehci_slot:word, usbtd_reg_id:word, usbtd_slot:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + 
                            G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES;
             is_valid_vaddr(vaddr) &&
             globals' == global_write_word(globals, G_EEHCI_MEM(), vaddr, usbtd_slot)
        // Requirement: WimpDrv_Write modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
             wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvWriteEEHCIUSBTDReg_MapWritingAbstractObjsVals(s, s', eehci_slot, usbtd_reg_id, usbtd_slot);
            var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
            var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
            var do_id_val_map:map<DO_ID, DO_Val> := temp.2;
            WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map)
      
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvWriteEEHCIUSBTDReg_MapWritingAbstractObjsVals(s, s', eehci_slot, usbtd_reg_id, usbtd_slot);
            var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
            var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
            var do_id_val_map:map<DO_ID, DO_Val> := temp.2;

            var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, td_id_val_map);
            (forall id:: id in fd_id_val_map ==> id in t_objs1.active_fds) &&
                // [NOTE] This property has been proved in <DM_GreenDrvWrite_InnerFunc> in the concrete model
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            (forall id:: id in do_id_val_map ==> id in t_objs2.active_dos) &&
                // [NOTE] This property has been proved in <DM_DevDeactivate_InnerFunc> in the concrete model
            var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
            var new_objects := t_objs3;
            dm' == dm.(objects := new_objects)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WimpDrv_ReadEEHCIFDDO_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    wimpdrv_slot:word, eehci_slot:word, reg_offset:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || 
             reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset
    
    requires state_equal_except_mstate(s, s');
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             globals' == globals
        // Requirement: WimpDrv_Read does not modify global variables
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
             wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
             var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
             var temp := F_WimpDrvReadEEHCIFDDO_MapReadingAbstractObjsVals(s, eehci_slot, reg_offset);
             var fd_ids:set<FD_ID> := temp.0;
             var do_ids:set<DO_ID> := temp.1;
             var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
             WSD_WimpDrvRead_PreConditions(dm, wimpdrv_id.sid, read_objs, map[], map[], map[])
    ensures dm' == dm


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WimpDrv_ReadEEHCIUSBTDReg_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    wimpdrv_slot:word, eehci_slot:word, usbtd_reg_slot:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires 0 <= usbtd_reg_slot < eEHCI_USBTD_SlotID_NUMS
    
    requires state_equal_except_mstate(s, s');
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             globals' == globals
        // Requirement: WimpDrv_Read does not modify global variables
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
             wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
             var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
             var td_ids := F_WimpDrvReadEEHCIUSBTDReg_MapReadingAbstractObjsVals(s, eehci_slot, usbtd_reg_slot);
             var read_objs := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs({}) + DOIDsToObjIDs({});
             WSD_WimpDrvRead_PreConditions(dm, wimpdrv_id.sid, read_objs, map[], map[], map[])
    ensures dm' == dm


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_USBTD_Allocate1Slot_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    new_td_slot:word, new_idword:word, new_td_type:word, new_pid:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires new_idword != USBTD_ID_INVALID
    requires new_idword in s.id_mappings.usbtd_to_td
    requires new_idword in s.id_mappings.usbtd_to_fd
    requires new_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires usbtd_map_valid_slot_id(new_td_slot)
    requires (new_td_type == USBTDs_TYPE_QTD32) || (new_td_type == USBTDs_TYPE_QH32) || 
        (new_td_type == USBTDs_TYPE_iTD32) || (new_td_type == USBTDs_TYPE_siTD32)
        // Requirements needed by the following requirements
    requires state_equal_except_mstate(s, s'); 
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             usbtd_slot_allocate_1slot_globals_relationship(globals, globals', new_td_slot, new_idword, new_td_type, new_pid, TRUE)
        // Requirement: USBTD_slot_allocate_1slot modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
             var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
             var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[new_idword];
             var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[new_idword];
             var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[new_idword];
             WKD_ExternalObjsActivateToGreenPartition_PreConditions(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid)
      
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));

            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[new_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[new_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[new_idword];
            var td_ids := {usbtd_td_id};
            var fd_ids := {usbtd_fd_id};
            var do_ids := {usbtd_do_id};

            (forall id:: id in td_ids ==> id in dm.objects.inactive_non_hcoded_tds) &&
                 // [NOTE] This property has been proved in <DM_ExternalObjsActivateToGreenPartition_InnerFunc> in the concrete model
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(dm.objects, td_ids, dm_pid);
            (forall id:: id in fd_ids ==> id in t_objs1.inactive_fds) &&
                // [NOTE] This property has been proved in <DM_ExternalObjsActivateToGreenPartition_InnerFunc> in the concrete model
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fd_ids, dm_pid);
            (forall id:: id in do_ids ==> id in t_objs1.inactive_dos) &&
                // [NOTE] This property has been proved in <DM_ExternalObjsActivateToGreenPartition_InnerFunc> in the concrete model
            var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, do_ids, dm_pid);
            dm' == dm.(objects := new_objects)


// [State/Ops Mapping] Axiom (well known): If no eEHCI or USB TD refs a USB TD, then no green TDs ref the USB TD
lemma {:axiom} Lemma_USBTD_Deallocate1Slot_NoGreenTDRefsWimpDrvToBeDeactivated(
    s:state, dm:DM_State,
    td_slot:word, pid:WS_PartitionID
)
    requires OpsSaneState(s)
    requires dm == WSM_MapState(s)

    requires usbtd_map_valid_slot_id(td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            usbtd_idword != USBTD_ID_INVALID &&
            usbtd_idword in s.id_mappings.usbtd_to_td &&
            usbtd_idword in s.id_mappings.usbtd_to_fd &&
            usbtd_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, usbtd_map_get_pid(globals, td_slot).v)
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_mem_no_ref_to_usbtd_slot(globals, td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtds_verifiedtds_do_not_associate_usbtd(globals, td_slot)
        // Requirement: The condition when USBTD_slot_allocate_1slot returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in s.objects.usbtd_tds &&
            usbtd_fd_id in s.objects.usbtd_fds &&
            usbtd_do_id in s.objects.usbtd_dos
        // Requirement: Mapped TDs/FDs/DOs must exist in the system

    requires pid != WS_PartitionID(PID_INVALID) &&
            pid != WS_PartitionID(PID_RESERVED_OS_PARTITION)

    requires P_DMObjectsHasUniqueIDs(dm.objects)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            (usbtd_fd_id in DM_AllFDIDs(dm.objects)) &&
            (usbtd_do_id in DM_AllDOIDs(dm.objects))
        // Properties needed by the following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(dm, 
                {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_USBTD_Deallocate1Slot_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    td_slot:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires usbtd_map_valid_slot_id(td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            usbtd_idword != USBTD_ID_INVALID &&
            usbtd_idword in s.id_mappings.usbtd_to_td &&
            usbtd_idword in s.id_mappings.usbtd_to_fd &&
            usbtd_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s')
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             usbtd_slot_deallocate_1slot_globals_relationship(globals, globals', td_slot, TRUE)
        // Requirement: USBTD_slot_deallocate_1slot modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
             var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
             var pid := usbtd_map_get_pid(globals, td_slot);
             var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
             var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
             var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
             var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
             WKD_GreenExternalObjsDeactivate_PreConditions(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid)
      
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var pid := usbtd_map_get_pid(globals, td_slot);
            var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);

            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            var td_ids := {usbtd_td_id};
            var fd_ids := {usbtd_fd_id};
            var do_ids := {usbtd_do_id};

            (forall id:: id in td_ids ==> id in dm.objects.active_non_hcoded_tds) &&
                 // [NOTE] This property has been proved in <DM_GreenExternalObjsDeactivate_InnerFunc> in the concrete model
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(dm.objects, td_ids);
            (forall id:: id in fd_ids ==> id in t_objs1.active_fds) &&
                // [NOTE] This property has been proved in <DM_GreenExternalObjsDeactivate_InnerFunc> in the concrete model
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fd_ids);
            (forall id:: id in do_ids ==> id in t_objs1.active_dos) &&
                // [NOTE] This property has been proved in <DM_GreenExternalObjsDeactivate_InnerFunc> in the concrete model
            var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, do_ids);
            dm' == dm.(objects := new_objects)


// Function: Convert wimp driver's submission of USB TDs to abstract objects and values
function {:axiom} F_WimpDrvSubmitUSBTD_MapWritingAbstractObjsVals(
    s:state, s':state, usbtd_slot:word
) : (result:(map<TD_ID, TD_Val>, map<FD_ID, FD_Val>, map<DO_ID, DO_Val>))
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')
        // Requirement: In the state s' after the write, WK_EEHCI_Mem_SecureGlobalVarValues(globals') must hold.
        // That is, all eEHCIs' USB TD regs either are USBTD_SlotID_INVALID, or ref secure/verified USB TDs

    requires usbtd_map_valid_slot_id(usbtd_slot)
        // Properties needed by the following requirement
    requires var globals' := wkm_get_globals(s'.wk_mstate);
             usbtd_map_get_flags(globals', usbtd_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
        // Requirement: The condition when USBTD_slot_submit_and_verify_* returns true

    ensures (forall id :: id in result.0
                ==> id in s.objects.usbtd_tds) &&
            (forall id :: id in result.1
                ==> id in s.objects.usbtd_fds) &&
            (forall id :: id in result.2
                ==> id in s.objects.usbtd_dos)
        // Property: If the returned maps are not empty, then the objects must be in usbtd_*
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
            (forall id :: id in result.0
                ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
            (forall id :: id in result.1
                ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
            (forall id :: id in result.2
                ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword)
        // Property: The objects in the result all maps to the USB TD <usbtd_idword> at the slot <new_v>
    ensures var dm := WSM_MapSecureState(s);
            var td_id_val_map := result.0;
            (forall td_id :: td_id in td_id_val_map ==> td_id in dm.objects.active_non_hcoded_tds) &&
            (forall id :: id in td_id_val_map
                ==> DM_ObjPID(dm.objects, id.oid) != NULL) &&
            DM_GreenDrvWrite_ChkNewValsOfTDs(dm, td_id_val_map)
        // Property: Properties of interpretation of transfers defined in secure/verified USB TDs


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_USBTD_Slot_SubmitAndVerify_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    wimpdrv_slot:word, td_slot:word, td_type:word,
    usbpdev_slot:word, input_param1:word, input_param2:word, input_param3:word, eehci_id:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires usbtd_map_valid_slot_id(td_slot)
        // Properties needed by the following requirement
    requires var globals' := wkm_get_globals(s'.wk_mstate);
             usbtd_map_get_flags(globals', td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
        // Requirement: The condition when USBTD_slot_submit_and_verify_* returns true
    requires state_equal_except_mstate(s, s')
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             p_usbtd_slot_submit_and_verify_usbtd_ret_global(globals, globals', td_slot) &&
             p_usbtd_slot_submit_modification_to_usbtd(globals', td_slot, wimpdrv_slot, usbpdev_slot, input_param1, input_param2, input_param3, td_type, eehci_id)
        // Requirement: USBTD_slot_submit_and_verify_* modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
             wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
             
    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvSubmitUSBTD_MapWritingAbstractObjsVals(s, s', td_slot);
            WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, temp.0, temp.1, temp.2)
      
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvSubmitUSBTD_MapWritingAbstractObjsVals(s, s', td_slot);
            var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
            var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
            var do_id_val_map:map<DO_ID, DO_Val> := temp.2;

            var t_objs1 := WriteActiveNonHCodedTDsVals(dm.objects, td_id_val_map);
            (forall id:: id in fd_id_val_map ==> id in t_objs1.active_fds) &&
                // [NOTE] This property has been proved in <DM_GreenDrvWrite_InnerFunc> in the concrete model
            var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
            (forall id:: id in do_id_val_map ==> id in t_objs2.active_dos) &&
                // [NOTE] This property has been proved in <DM_DevDeactivate_InnerFunc> in the concrete model
            var t_objs3 := WriteActiveDOsVals(t_objs2, do_id_val_map);
            var new_objects := t_objs3;
            dm' == dm.(objects := new_objects)


// [HW] Axiom (well known): Physical EHCIs do not define write transfers to any TDs in the hardcoded TDs
lemma {:axiom} Lemma_PEHCI_HCodedTDDoNotDefineWriteTransferToTDs(s:state, dm:DM_State, pehci_id:Dev_ID)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
        // Requirement from <WK_ValidState_DevsActivateCond>

    requires pehci_id in WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds)
    requires s.subjects.os_devs[pehci_id].hcoded_td_id in s.objects.os_tds
        // Properties needed by the following properties
    requires pehci_id in dm.subjects.devs

    ensures forall hcoded_td_id, td_id :: hcoded_td_id == dm.subjects.devs[pehci_id].hcoded_td_id &&
                    td_id in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
                ==> W !in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds[td_id].amodes


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    new_pid:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
    requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)
        // Properties specific to OS_Activate_AllReleasedPEHCIsAndUSBPDevs

    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr) in s.subjects.usbpdevs
        // Requirements needed by the following requirements
    requires state_equal_except_mstate_subjs_objs(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE(s, s', all_non_empty_addrs)
        // Requirement: OS_Activate_AllReleasedPEHCIsAndUSBPDevs modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
             var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
             var to_assign_dev_ids:seq<Dev_ID> := SetToSeq_Func(pehci_ids + usbpdev_ids);
             WKD_MultiDevs_ReturnOS_PreConditions(dm, to_assign_dev_ids)

    ensures var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            var to_assign_dev_ids:seq<Dev_ID> := SetToSeq_Func(pehci_ids + usbpdev_ids);
            WKD_MultiDevs_ReturnOS_Stub(dm, to_assign_dev_ids).0 == dm'


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_OS_Activate_MainMem_ByPAddr_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    paddr_start:word, paddr_end:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires WK_ValidPMemRegion(paddr_start, paddr_end)
        // Properties specific to OS_Activate_MainMem_ByPAddr
    requires state_equal_except_mstate_subjs_objs_memactivemap(s, s')
    requires ffi_pmem_activate_main_mem_in_os_stack_and_statevars_inner(s, paddr_start, paddr_end, TRUE, s'.subjects, s'.objects, s'.os_mem_active_map)
        // Requirement: OS_Activate_MainMem_ByPAddr modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires IsValidState_Objects_UniqueObjIDs(dm.objects)
        // Properties needed by the following properties
    ensures var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
            var td_ids := result.1;
            var fd_ids := result.2;
            var do_ids := result.3;
            
            (forall id:: id in td_ids ==> id in dm.objects.inactive_non_hcoded_tds) &&
                 // [NOTE] This property has been proved in <DM_ExternalObjsActivateToRedPartition_InnerFunc> in the concrete model
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(dm.objects, td_ids, dm.red_pid);
            (forall id:: id in fd_ids ==> id in t_objs1.inactive_fds) &&
                // [NOTE] This property has been proved in <DM_ExternalObjsActivateToRedPartition_InnerFunc> in the concrete model
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fd_ids, dm.red_pid);
            (forall id:: id in do_ids ==> id in t_objs2.inactive_dos) &&
                // [NOTE] This property has been proved in <DM_ExternalObjsActivateToRedPartition_InnerFunc> in the concrete model
            var new_objects := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, do_ids, dm.red_pid);
            dm' == dm.(objects := new_objects)


// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_OS_Deactivate_MainMem_ByPAddr_ProveOperationMapping(
    s:state, s':state, dm:DM_State, dm':DM_State,
    paddr_start:word, paddr_end:word
)
    requires OpsSaneState(s)
    requires OpsSaneStateSubset(s')

    requires WK_ValidPMemRegion(paddr_start, paddr_end)
        // Properties specific to OS_Activate_MainMem_ByPAddr
    requires state_equal_except_mstate_subjs_objs_memactivemap(s, s')
    requires ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars_inner(s, paddr_start, paddr_end, s'.subjects, s'.objects, s'.os_mem_active_map)
        // Requirement: OS_Activate_MainMem_ByPAddr modifies global variables correctly
        // Relationship between s and s'

    requires dm == WSM_MapState(s)
    requires dm' == WSM_MapState(s')

    requires IsValidState_Objects_UniqueObjIDs(dm.objects)
        // Properties needed by the following properties
    ensures var result := os_external_objs_to_be_deactivated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
            var td_ids := result.1;
            var fd_ids := result.2;
            var do_ids := result.3;
            
            (forall id:: id in td_ids ==> id in dm.objects.active_non_hcoded_tds) &&
                 // [NOTE] This property has been proved in <DM_RedExternalObjsDeactivate_InnerFunc> in the concrete model
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(dm.objects, td_ids);
            (forall id:: id in fd_ids ==> id in dm.objects.active_fds) &&
                // [NOTE] This property has been proved in <DM_RedExternalObjsDeactivate_InnerFunc> in the concrete model
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fd_ids);
            (forall id:: id in do_ids ==> id in dm.objects.active_dos) &&
                // [NOTE] This property has been proved in <DM_RedExternalObjsDeactivate_InnerFunc> in the concrete model
            var new_objects := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, do_ids);
            dm' == dm.(objects := new_objects)




/*********************** Utility Predicates (as we cannot specify "== (dm', true)" in Vale) ********************/
predicate WK_EmptyPartitionCreate_CommutativeDiagram_Property(dm:DM_State, dm':DM_State, dm_new_pid:Partition_ID, ret:word)
    requires DM_IsValidState(dm) && DM_IsSecureState(dm) 
{
    (ret == TRUE) ==> (
        WKD_EmptyPartitionCreate_PreConditions(dm, dm_new_pid) &&
        DM_EmptyPartitionCreate_InnerFunc(dm, dm_new_pid) == (dm', true)
    )
}

predicate WK_EmptyPartitionDestroy_CommutativeDiagram_Property(dm:DM_State, dm':DM_State, dm_pid:Partition_ID, ret:word)
    requires DM_IsValidState(dm) && DM_IsSecureState(dm) 
{
    (ret == TRUE) ==> (
        WKD_EmptyPartitionDestroy_PreConditions(dm, dm_pid) &&
        DM_EmptyPartitionDestroy_InnerFunc(dm, dm_pid) == (dm', true)
    )
}

predicate WK_DrvActivateToGreenPartition_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    new_wimpdrv_idword:uint32, new_wimpdrv_pid:uint32, ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires new_wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword) in s.subjects.wimp_drvs 
        // Properties needed by the following requirement
{
    var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_wimpdrv_pid));
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword);

    (ret == TRUE) ==> (
        WKD_DrvActivateToGreenPartition_PreConditions(dm, wimpdrv_id.sid, dm_new_pid) &&
        DM_DrvActivateToGreenPartition_InnerFunc(dm, wimpdrv_id.sid, dm_new_pid) == (dm', true)
    )
}

predicate WK_USBPDev_Activate_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    usbpdev_slot:uint32, new_pid:uint32, new_usbpdev_addr_low:paddr, new_usbpdev_addr_high:paddr, 
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
        var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
        usb_is_usbpdev_addr_valid(new_usbpdev_addr_raw) &&
        usb_is_usbpdev_addr_valid(empty_addr) &&
        usb_parse_usbpdev_addr(new_usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr)
    ) &&

    (ret == TRUE) ==> (
        var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
        var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
        var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);
        usbpdev_id in s.subjects.usbpdevs
    ) &&

    (ret == TRUE) ==> (
        var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
        var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
        var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
        var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);

        WKD_DevActivate_PreConditions(dm, usbpdev_id.sid, dm_pid) &&
        DM_DevActivate_InnerFunc(dm, usbpdev_id.sid, dm_pid) == (dm', true)
    )
}

predicate WK_EEHCI_Activate_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    new_pid:uint32, eehci_idword:word,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        eehci_idword != eEHCI_ID_INVALID
    ) &&

    (ret == TRUE) ==> (
        var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
        var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);

        WKD_DevActivate_PreConditions(dm, eehci_id.sid, dm_pid) &&
        DM_DevActivate_InnerFunc(dm, eehci_id.sid, dm_pid) == (dm', true)
    )
}

predicate WK_WimpDrv_Deactivate_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    drv_slot:uint32,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        wimpdrv_valid_slot_id(drv_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
        wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        WKD_GreenDrvDeactivate_PreConditions(dm, wimpdrv_id.sid) &&
        DM_GreenDrvDeactivate_InnerFunc(dm, wimpdrv_id.sid) == (dm', true)
    )
}

predicate WK_USBPDev_Deactivate_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    usbpdev_slot:uint32, 
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        usbpdev_valid_slot_id(usbpdev_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
        var empty_addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
        usb_is_usbpdev_addr_valid(empty_addr_raw) &&
        usb_is_usbpdev_addr_valid(usbpdev_addr_raw) &&
        usb_parse_usbpdev_addr(usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr_raw)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
        var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
        var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);

        WKD_DevDeactivate_PreConditions(dm, usbpdev_id.sid) &&
        DM_DevDeactivate_InnerFunc(dm, usbpdev_id.sid) == (dm', true)
    )
}

predicate WK_EEHCI_Deactivate_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    eehci_slot:uint32, 
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        eehci_valid_slot_id(eehci_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        eehci_idword != eEHCI_ID_INVALID
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);

        WKD_DevDeactivate_PreConditions(dm, eehci_id.sid) &&
        DM_DevDeactivate_InnerFunc(dm, eehci_id.sid) == (dm', true)
    )
}

predicate WK_WimpDrv_WriteEEHCIObjs_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    wimpdrv_id:Drv_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        wimpdrv_id in s.subjects.wimp_drvs
    ) &&

    (ret == TRUE) ==> (
        WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) &&
        DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (dm', true)
    )
}

predicate WK_WimpDrv_WriteEEHCIFDsDOs_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    wimpdrv_slot:word, eehci_slot:word, reg_offset:word, new_v:word,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        wimpdrv_valid_slot_id(wimpdrv_slot) &&
        eehci_valid_slot_id(eehci_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        eehci_idword != eEHCI_ID_INVALID
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        wimpdrv_id in s.subjects.wimp_drvs
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
        eehci_id in s.subjects.eehcis
    ) &&

    (ret == TRUE) ==> (
        reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || 
        reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        var temp := F_WimpDrvWriteEEHCIFDDO_MapWritingAbstractObjsVals(s, eehci_slot, reg_offset, new_v);
        var fd_id_val_map:map<FD_ID, FD_Val> := temp.0;
        var do_id_val_map:map<DO_ID, DO_Val> := temp.1;

        WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, map[], fd_id_val_map, do_id_val_map) &&
        DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, map[], fd_id_val_map, do_id_val_map) == (dm', true)
    )
}

predicate WK_WimpDrv_WriteEEHCIUSBTDReg_CommutativeDiagram_Property(
    s:state, dm:DM_State, s':state, dm':DM_State, 
    wimpdrv_slot:word, eehci_slot:word, usbtd_reg_id:word, usbtd_slot:word,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')
{
    (ret == TRUE) ==> (
        wimpdrv_valid_slot_id(wimpdrv_slot) &&
        eehci_valid_slot_id(eehci_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        eehci_idword != eEHCI_ID_INVALID
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        wimpdrv_id in s.subjects.wimp_drvs
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
        eehci_id in s.subjects.eehcis
    ) &&

    (ret == TRUE) ==> (
        eehci_valid_slot_id(eehci_slot) &&
        // Properties needed by the following requirement
        state_equal_except_mstate(s, s') &&
        0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
        (
            var globals := wkm_get_globals(s.wk_mstate);
            var globals' := wkm_get_globals(s'.wk_mstate);
            var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + 
                            G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES;
            is_valid_vaddr(vaddr) &&
            globals' == global_write_word(globals, G_EEHCI_MEM(), vaddr, usbtd_slot)
            // Requirement: WimpDrv_Write modifies global variables correctly
            // Relationship between s and s'
        )
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        var temp := F_WimpDrvWriteEEHCIUSBTDReg_MapWritingAbstractObjsVals(s, s', eehci_slot, usbtd_reg_id, usbtd_slot);
        var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
        var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
        var do_id_val_map:map<DO_ID, DO_Val> := temp.2;

        WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) &&
        DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (dm', true)
    )
}

predicate WK_WimpDrv_ReadEEHCIFDsDOs_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    wimpdrv_slot:word, eehci_slot:word, reg_offset:word,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        wimpdrv_valid_slot_id(wimpdrv_slot) &&
        eehci_valid_slot_id(eehci_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        eehci_idword != eEHCI_ID_INVALID
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        wimpdrv_id in s.subjects.wimp_drvs
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
        eehci_id in s.subjects.eehcis
    ) &&

    (ret == TRUE) ==> (
        reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || 
        reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        var temp := F_WimpDrvReadEEHCIFDDO_MapReadingAbstractObjsVals(s, eehci_slot, reg_offset);
        var fd_ids:set<FD_ID> := temp.0;
        var do_ids:set<DO_ID> := temp.1;
        var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);

        WSD_WimpDrvRead_PreConditions(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) &&
        DM_GreenDrvRead_InnerFunc(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) == (dm', true)
    )
}

predicate WK_WimpDrv_ReadEEHCIUSBTDReg_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    wimpdrv_slot:word, eehci_slot:word, usbtd_reg_slot:word,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        wimpdrv_valid_slot_id(wimpdrv_slot) &&
        eehci_valid_slot_id(eehci_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        eehci_idword != eEHCI_ID_INVALID
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        wimpdrv_id in s.subjects.wimp_drvs
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
        var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
        eehci_id in s.subjects.eehcis
    ) &&

    (ret == TRUE) ==> (
        0 <= usbtd_reg_slot < eEHCI_USBTD_SlotID_NUMS
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        var td_ids := F_WimpDrvReadEEHCIUSBTDReg_MapReadingAbstractObjsVals(s, eehci_slot, usbtd_reg_slot);
        var read_objs := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs({}) + DOIDsToObjIDs({});

        WSD_WimpDrvRead_PreConditions(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) &&
        DM_GreenDrvRead_InnerFunc(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) == (dm', true)
    )
}

predicate WK_USBTD_Allocate1Slot_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    new_idword:word, new_pid:word,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        new_idword in s.id_mappings.usbtd_to_td &&
        new_idword in s.id_mappings.usbtd_to_fd &&
        new_idword in s.id_mappings.usbtd_to_do
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
        var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[new_idword];
        var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[new_idword];
        var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[new_idword];

        WKD_ExternalObjsActivateToGreenPartition_PreConditions(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid) &&
        DM_ExternalObjsActivateToGreenPartition_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid) == (dm', true)
    )
}

predicate WK_USBTD_Deallocate1Slot_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, 
    td_slot:word, 
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        usbtd_map_valid_slot_id(td_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
        
        usbtd_idword in s.id_mappings.usbtd_to_td &&
        usbtd_idword in s.id_mappings.usbtd_to_fd &&
        usbtd_idword in s.id_mappings.usbtd_to_do
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
        var pid := usbtd_map_get_pid(globals, td_slot);
        var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
        var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
        var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
        var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];

        WKD_GreenExternalObjsDeactivate_PreConditions(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid) &&
        DM_GreenExternalObjsDeactivate_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid) == (dm', true)
    )
}

predicate WK_USBTD_Slot_SubmitAndVerify_CommutativeDiagram_Property(
    s:state, dm:DM_State, s':state, dm':DM_State, 
    wimpdrv_slot:word, td_slot:word,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')
{
    (ret == TRUE) ==> (
        wimpdrv_valid_slot_id(wimpdrv_slot) &&
        usbtd_map_valid_slot_id(td_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        wimpdrv_id in s.subjects.wimp_drvs
    ) &&

    (ret == TRUE) ==> (
        var globals' := wkm_get_globals(s'.wk_mstate);
        usbtd_map_get_flags(globals', td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        var temp := F_WimpDrvSubmitUSBTD_MapWritingAbstractObjsVals(s, s', td_slot);
        var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
        var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
        var do_id_val_map:map<DO_ID, DO_Val> := temp.2;

        WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) &&
        DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (dm', true)
    )
}

predicate WK_USBTD_Slot_SubmitAndVerify_SubjAndObjsInSamePartition(
    s:state, dm:DM_State, s':state, dm':DM_State, 
    wimpdrv_slot:word, td_slot:word,
    ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')
{
    (ret == TRUE) ==> (
        wimpdrv_valid_slot_id(wimpdrv_slot) &&
        usbtd_map_valid_slot_id(td_slot)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        wimpdrv_id in s.subjects.wimp_drvs
    ) &&

    (ret == TRUE) ==> (
        var globals' := wkm_get_globals(s'.wk_mstate);
        usbtd_map_get_flags(globals', td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    ) &&

    (ret == TRUE) ==> (
        var globals := wkm_get_globals(s.wk_mstate);
        var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
        var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        var temp := F_WimpDrvSubmitUSBTD_MapWritingAbstractObjsVals(s, s', td_slot);
        var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
        var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
        var do_id_val_map:map<DO_ID, DO_Val> := temp.2;

        WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, wimpdrv_id.sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map))
    )
}

predicate WK_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_CommutativeDiagram_Property(
    s:state, dm:DM_State, dm':DM_State, ret:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    reveal WK_ValidState_DevsActivateCond();
    var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
    var to_assign_dev_ids:seq<Dev_ID> := SetToSeq_Func(pehci_ids + usbpdev_ids);

    (ret == TRUE) ==> (
        WKD_MultiDevs_ReturnOS_PreConditions(dm, to_assign_dev_ids)
    ) &&

    (ret == TRUE) ==> (
        WKD_MultiDevs_ReturnOS_Stub(dm, to_assign_dev_ids) == (dm', true)
    )
}

predicate OS_Activate_MainMem_ByPAddr_CommutativeDiagram_Property(s:state, dm:DM_State, dm':DM_State, paddr_start:word, paddr_end:word, ret:word)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (ret == TRUE) ==> (
        WK_ValidPMemRegion(paddr_start, paddr_end)
    ) &&

    (ret == TRUE) ==> (
        var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
        var os_tds := result.1;
        var os_fds := result.2;
        var os_dos := result.3; 

        WKD_ExternalObjsActivateToRedPartition_PreConditions(dm, os_tds, os_fds, os_dos) &&
        DM_ExternalObjsActivateToRedPartition_InnerFunc(dm, os_tds, os_fds, os_dos) == (dm', true)
    )
}

predicate OS_Deactivate_MainMem_ByPAddr_CommutativeDiagram_Property(s:state, dm:DM_State, dm':DM_State, paddr_start:word, paddr_end:word)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
{
    (
        WK_ValidPMemRegion(paddr_start, paddr_end)
    ) &&

    (
        var result := os_external_objs_to_be_deactivated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
        var os_tds := result.1;
        var os_fds := result.2;
        var os_dos := result.3; 

        WKD_RedExternalObjsDeactivate_PreConditions(dm, os_tds, os_fds, os_dos) &&
        DM_RedExternalObjsDeactivate_InnerFunc(dm, os_tds, os_fds, os_dos) == (dm', true)
    )
}




/*********************** Lemmas ********************/
lemma Lemma_WK_EmptyPartitionCreate_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    pid_slot:uint32, new_pid:word,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             wk_create_partition_globalvars_relation(globals, globals', pid_slot, new_pid)
        // Requirement: WK_EmptyPartitionCreate modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             WS_PartitionID(new_pid) !in pids_parse_g_wimp_pids(globals) &&
             new_pid != PID_INVALID &&
             new_pid != PID_RESERVED_OS_PARTITION
        // Requirement: The condition when WK_EmptyPartitionCreate returns true
    
    ensures var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            WKD_EmptyPartitionCreate_PreConditions(dm, dm_new_pid)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            DM_EmptyPartitionCreate_InnerFunc(dm, dm_new_pid) == (WSM_MapState(s'), true)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove WKD_EmptyPartitionCreate_PreConditions
    var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    assert WKD_EmptyPartitionCreate_PreConditions(dm, dm_new_pid);

    // Prove DM_EmptyPartitionCreate_InnerFunc(dm, dm_new_pid).1 == true
    Lemma_WK_EmptyPartitionCreate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, new_pid);
    assert DM_EmptyPartitionCreate_InnerFunc(dm, dm_new_pid).1 == true;

    // Prove DM_EmptyPartitionCreate_InnerFunc(dm, dm_new_pid).0 == dm'
    var op_result := DM_EmptyPartitionCreate_InnerFunc(dm, dm_new_pid);
    var dm' := WSM_MapState(s');
    Lemma_WK_EmptyPartitionCreate_ProveOperationMapping(s, s', dm, dm', pid_slot, new_pid);

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WKD_EmptyPartitionCreate_Stub(dm, dm_new_pid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_WK_EmptyPartitionDestroy_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    pid:word,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             wk_destroy_partition_globalvars_relation(globals, globals', pid)
        // Requirement: WK_EmptyPartitionDestroy modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, pid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             (forall i :: eehci_valid_slot_id(i)
                    ==> eehci_info_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: usbpdev_valid_slot_id(i)
                    ==> usbpdev_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: usbtd_map_valid_slot_id(i)
                    ==> usbtd_map_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: wimpdrv_valid_slot_id(i)
                    ==> wimpdrv_get_pid(globals, i) != WS_PartitionID(pid))
        // Requirement: The condition when WK_EmptyPartitionDestroy returns true
    
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(pid));
            WKD_EmptyPartitionDestroy_PreConditions(dm, dm_pid)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(pid));
            DM_EmptyPartitionDestroy_InnerFunc(dm, dm_pid) == (WSM_MapState(s'), true)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove WKD_EmptyPartitionCreate_PreConditions
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(pid));
    assert WKD_EmptyPartitionDestroy_PreConditions(dm, dm_pid);

    // Prove DM_EmptyPartitionDestroy_InnerFunc(dm, dm_pid).1 == true
    Lemma_WK_EmptyPartitionDestroy_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, pid);
    assert DM_EmptyPartitionDestroy_InnerFunc(dm, dm_pid).1 == true;

    // Prove DM_EmptyPartitionDestroy_InnerFunc(dm, dm_pid).0 == dm'
    var op_result := DM_EmptyPartitionDestroy_InnerFunc(dm, dm_pid);
    var dm' := WSM_MapState(s');
    Lemma_WK_EmptyPartitionDestroy_ProveOperationMapping(s, s', dm, dm', pid);

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WKD_EmptyPartitionDestroy_Stub(dm, dm_pid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_WimpDrv_Activate_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    drv_slot:uint32, new_wimpdrv_idword:uint32, new_wimpdrv_pid:uint32, new_do_pbase:paddr, new_do_pend:paddr,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires new_wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword) in s.subjects.wimp_drvs 
        // Properties needed by the following requirement
    requires state_equal_except_mstate_objs(s, s');
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             wimpdrv_info_newvalue(globals, globals', drv_slot, new_wimpdrv_idword, new_wimpdrv_pid, new_do_pbase, new_do_pend, WimpDrv_Slot_UpdateFlag_Complete) &&
             wimpdrv_DO_clear_non_mstate_relationship(s, s', new_wimpdrv_idword)
        // Requirement: WimpDrv_Activate modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, new_wimpdrv_pid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: wimpdrv_valid_slot_id(i)
                ==> wimpdrv_get_id_word(globals, i) != new_wimpdrv_idword
        // Requirement: The condition when WimpDrv_Activate returns true
    
    ensures var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_wimpdrv_pid));
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword);
            WKD_DrvActivateToGreenPartition_PreConditions(dm, wimpdrv_id.sid, dm_new_pid)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_wimpdrv_pid));
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword);
            DM_DrvActivateToGreenPartition_InnerFunc(dm, wimpdrv_id.sid, dm_new_pid) == (WSM_MapState(s'), true)
    ensures WK_DrvActivateToGreenPartition_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), new_wimpdrv_idword, new_wimpdrv_pid, TRUE);
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove WKD_DrvActivateToGreenPartition_PreConditions
    var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_wimpdrv_pid));
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword);
    assert WKD_DrvActivateToGreenPartition_PreConditions(dm, wimpdrv_id.sid, dm_new_pid);

    assert wimpdrv_id in dm.subjects.drvs;
    assert dm_new_pid != NULL;
    assert dm_new_pid != dm.red_pid;

    // Prove DM_DrvActivateToGreenPartition_InnerFunc(dm, wimpdrv_id.sid, dm_new_pid).1 == true
    Lemma_WimpDrv_Activate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, drv_slot, new_wimpdrv_idword, new_wimpdrv_pid);
    assert DM_DrvActivateToGreenPartition_InnerFunc(dm, wimpdrv_id.sid, dm_new_pid).1 == true;

    // Prove DM_DrvActivateToGreenPartition_InnerFunc(dm, wimpdrv_id.sid, dm_new_pid).0 == dm'
    var op_result := DM_DrvActivateToGreenPartition_InnerFunc(dm, wimpdrv_id.sid, dm_new_pid);
    var dm' := WSM_MapState(s');
    Lemma_WimpDrv_Activate_ProveOperationMapping(s, s', dm, dm', drv_slot, new_wimpdrv_idword, new_wimpdrv_pid, new_do_pbase, new_do_pend);

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WKD_DrvActivateToGreenPartition_Stub(dm, wimpdrv_id.sid, dm_new_pid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_USBPDev_Activate_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    usbpdev_slot:uint32, new_pid:uint32, new_usbpdev_addr_low:paddr, new_usbpdev_addr_high:paddr,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
        // Properties specific to USBPDev activation
    requires var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(new_usbpdev_addr_raw) &&
             usb_is_usbpdev_addr_valid(empty_addr) &&
             usb_parse_usbpdev_addr(new_usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr)
    requires var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
             var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
             var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);
             usbpdev_id in s.subjects.usbpdevs
        // Properties needed by the following requirement
    requires state_equal_except_mstate_objs(s, s');       
    requires var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
             var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
             var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             usbpdev_info_newvalue(globals, globals', usbpdev_slot, new_usbpdev_addr_low, new_usbpdev_addr_high, new_pid, WimpUSBPDev_Slot_UpdateFlag_Complete) &&
             usbpdev_clear_non_mstate_relationship(s, s', new_usbpdev_addr);
        // Requirement: USBPDev_Activate modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, new_pid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: usbpdev_valid_slot_id(i)
                ==> !(usbpdev_get_addr_low(globals, i) == new_usbpdev_addr_low &&
                        usbpdev_get_addr_high(globals, i) == new_usbpdev_addr_high)
        // Requirement: The condition when USBPDev_Activate returns true
    
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
            var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);
            WKD_DevActivate_PreConditions(dm, usbpdev_id.sid, dm_pid)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
            var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);
            DM_DevActivate_InnerFunc(dm, usbpdev_id.sid, dm_pid) == (WSM_MapState(s'), true)
    ensures WK_USBPDev_Activate_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), usbpdev_slot, new_pid, new_usbpdev_addr_low, new_usbpdev_addr_high, TRUE)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures P_DMObjectsHasUniqueIDs(WSM_MapState(s').objects)
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove WKD_DevActivate_PreConditions
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
    var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
    var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);
    assert WKD_DevActivate_PreConditions(dm, usbpdev_id.sid, dm_pid);

    assert usbpdev_id in dm.subjects.devs;
    assert dm_pid != NULL;

    // Prove DM_DevActivate_InnerFunc(dm, usbpdev_id.sid, dm_pid).1 == true
    Lemma_USBPDev_Activate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, usbpdev_slot, new_pid, new_usbpdev_addr_low, new_usbpdev_addr_high);
    assert DM_DevActivate_InnerFunc(dm, usbpdev_id.sid, dm_pid).1 == true;

    // Prove DM_DevActivate_InnerFunc(dm, usbpdev_id.sid, dm_pid).0 == dm'
    var op_result := DM_DevActivate_InnerFunc(dm, usbpdev_id.sid, dm_pid);
    var dm' := WSM_MapState(s');
    Lemma_USBPDev_Activate_ProveOperationMapping(s, s', dm, dm', usbpdev_slot, new_pid, new_usbpdev_addr_low, new_usbpdev_addr_high);

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WKD_DevActivate_Stub(dm, usbpdev_id.sid, dm_pid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_EEHCI_Activate_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    eehci_slot:uint32, new_pid:uint32, eehci_idword:word, eehci_handle:word, 
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)
        // Properties specific to EEHCI activation
    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_idword != eEHCI_ID_INVALID
    requires var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
             eehci_id in s.subjects.eehcis
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             eechi_activate_globalvars_relation(globals, globals', eehci_slot, eehci_idword, eehci_handle, new_pid)
        // Requirement: EEHCI_Activate modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, new_pid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_mem_get_eehci_id(globals, i) != eehci_idword
        // Requirement: The condition when EEHCI_Activate returns true
    
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            WKD_DevActivate_PreConditions(dm, eehci_id.sid, dm_pid)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            DM_DevActivate_InnerFunc(dm, eehci_id.sid, dm_pid) == (WSM_MapState(s'), true)
    ensures WK_EEHCI_Activate_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), new_pid, eehci_idword, TRUE)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures P_DMObjectsHasUniqueIDs(WSM_MapState(s').objects)
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove WKD_DevActivate_PreConditions
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
    assert WKD_DevActivate_PreConditions(dm, eehci_id.sid, dm_pid);

    assert eehci_id in dm.subjects.devs;
    assert dm_pid != NULL;

    // Prove DM_DevActivate_InnerFunc(dm, eehci_id.sid, dm_pid).1 == true
    Lemma_EEHCI_Activate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, eehci_slot, new_pid, eehci_idword);
    assert DM_DevActivate_InnerFunc(dm, eehci_id.sid, dm_pid).1 == true;

    // Prove DM_DevActivate_InnerFunc(dm, eehci_id.sid, dm_pid).0 == dm'
    var op_result := DM_DevActivate_InnerFunc(dm, eehci_id.sid, dm_pid);
    var dm' := WSM_MapState(s');
    Lemma_EEHCI_Activate_ProveOperationMapping(s, s', dm, dm', eehci_slot, new_pid, eehci_idword, eehci_handle);

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WKD_DevActivate_Stub(dm, eehci_id.sid, dm_pid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_WimpDrv_Deactivate_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    drv_slot:uint32, 
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(drv_slot)
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             wimpdrv_get_pid(globals', drv_slot) == WS_PartitionID(PID_INVALID) &&
             wimpdrv_info_newvalue(globals, globals', drv_slot, WimpDrv_ID_RESERVED_EMPTY, PID_INVALID, 0, 0, WimpDrv_Slot_UpdateFlag_Complete)
        // Requirement: WimpDrv_Deactivate modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, wimpdrv_get_pid(globals, drv_slot).v)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtds_verifiedtds_do_not_associate_wimpdrv(globals, drv_slot)
        // Requirement: The condition when WimpDrv_Deactivate returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
        // Properties specific to WimpDrv_Deactivate

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            WKD_GreenDrvDeactivate_PreConditions(dm, wimpdrv_id.sid)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            DM_GreenDrvDeactivate_InnerFunc(dm, wimpdrv_id.sid) == (WSM_MapState(s'), true)
    ensures WK_WimpDrv_Deactivate_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), drv_slot, TRUE);
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    Lemma_WimpDrv_Deactivate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, drv_slot);

    // Prove WKD_GreenDrvDeactivate_PreConditions
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    assert WKD_GreenDrvDeactivate_PreConditions(dm, wimpdrv_id.sid);

    // Prove DM_GreenDrvDeactivate_InnerFunc(dm, wimpdrv_id.sid).1 == true
    assert DM_GreenDrvDeactivate_InnerFunc(dm, wimpdrv_id.sid).1 == true;

    // Prove DM_GreenDrvDeactivate_InnerFunc(dm, wimpdrv_id.sid).0 == dm'
    var op_result := DM_GreenDrvDeactivate_InnerFunc(dm, wimpdrv_id.sid);
    var dm' := WSM_MapState(s');
    Lemma_WimpDrv_Deactivate_ProveOperationMapping(s, s', dm, dm', drv_slot);

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WKD_GreenDrvDeactivate_Stub(dm, wimpdrv_id.sid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_USBPDev_Deactivate_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    usbpdev_slot:uint32,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
        // Properties specific to USBPDev activation
    requires usbpdev_valid_slot_id(usbpdev_slot)
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             usbpdev_get_pid(globals', usbpdev_slot) == WS_PartitionID(PID_INVALID) &&
             usbpdev_info_newvalue(globals, globals', usbpdev_slot, WimpUSBPDev_ADDR_EMPTY_LOW, WimpUSBPDev_ADDR_EMPTY_HIGH, PID_INVALID, WimpUSBPDev_Slot_UpdateFlag_Complete)
        // Requirement: USBPDev_Deactivate modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, usbpdev_get_pid(globals, usbpdev_slot).v)
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbpdev_get_updateflag(globals, usbpdev_slot) == WimpUSBPDev_Slot_UpdateFlag_Complete
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtds_verifiedtds_do_not_associate_usb_pdev(globals, usbpdev_slot)
        // Requirement: The condition when USBPDev_Deactivate returns true

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var empty_addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
            usb_is_usbpdev_addr_valid(empty_addr_raw) &&
            usb_parse_usbpdev_addr(usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr_raw)
        // Properties needed by the following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            WKD_DevDeactivate_PreConditions(dm, usbpdev_id.sid)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            DM_DevDeactivate_InnerFunc(dm, usbpdev_id.sid) == (WSM_MapState(s'), true)
    ensures WK_USBPDev_Deactivate_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), usbpdev_slot, TRUE)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures P_DMObjectsHasUniqueIDs(WSM_MapState(s').objects)
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove property 0
    var globals := wkm_get_globals(s.wk_mstate);
    var empty_addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
    var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

    // Prove WKD_DevActivate_PreConditions
    Lemma_USBPDev_Deactivate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, usbpdev_slot);
    var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
    assert WKD_DevDeactivate_PreConditions(dm, usbpdev_id.sid);

    // Prove DM_DevDeactivate_InnerFunc(dm, usbpdev_id.sid).1 == true
    assert DM_DevDeactivate_InnerFunc(dm, usbpdev_id.sid).1 == true;

    // Prove DM_DevDeactivate_InnerFunc(dm, usbpdev_id.sid).0 == dm'
    var op_result := DM_DevDeactivate_InnerFunc(dm, usbpdev_id.sid);
    var dm' := WSM_MapState(s');
    Lemma_USBPDev_Deactivate_ProveOperationMapping(s, s', dm, dm', usbpdev_slot);

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WKD_DevDeactivate_Stub(dm, usbpdev_id.sid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_EEHCI_Deactivate_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    eehci_slot:uint32,  
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    //requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)
        // Properties specific to EEHCI activation
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             eechi_deactivate_globalvars_relation(globals, globals', eehci_slot)
        // Requirement: EEHCI_Deactivate modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, eehci_info_get_pid(globals, eehci_slot).v)
        // Requirement: The condition when EEHCI_Deactivate returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
        // Properties specific to EEHCI_Deactivate
    
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            WKD_DevDeactivate_PreConditions(dm, eehci_id.sid)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            DM_DevDeactivate_InnerFunc(dm, eehci_id.sid) == (WSM_MapState(s'), true)
    ensures WK_EEHCI_Deactivate_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), eehci_slot, TRUE)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures P_DMObjectsHasUniqueIDs(WSM_MapState(s').objects)
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove property 0
    var globals := wkm_get_globals(s.wk_mstate);
    var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
    var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);

    // Prove WKD_DevActivate_PreConditions
    Lemma_EEHCI_Deactivate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, eehci_slot);
    assert WKD_DevDeactivate_PreConditions(dm, eehci_id.sid);

    // Prove DM_DevDeactivate_InnerFunc(dm, eehci_id.sid).1 == true
    assert DM_DevDeactivate_InnerFunc(dm, eehci_id.sid).1 == true;

    // Prove DM_DevDeactivate_InnerFunc(dm, eehci_id.sid).0 == dm'
    var op_result := DM_DevDeactivate_InnerFunc(dm, eehci_id.sid);
    var dm' := WSM_MapState(s');
    Lemma_EEHCI_Deactivate_ProveOperationMapping(s, s', dm, dm', eehci_slot);

    // Prove property 2
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WKD_DevDeactivate_Stub(dm, eehci_id.sid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_WimpDrvWriteEEHCIFDDO_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    wimpdrv_slot:word, eehci_slot:word, reg_offset:word, new_v:word,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || 
             reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset
    
    requires state_equal_except_mstate(s, s');
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + reg_offset;
             is_valid_vaddr(vaddr) &&
             globals' == global_write_word(globals, G_EEHCI_MEM(), vaddr, new_v)
        // Requirement: WimpDrv_Write modifies global variables correctly
        // Relationship between s and s'

    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
        // Requirement: The condition when WimpDrv_Write returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
        // Properties specific to WimpDrv_Write

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvWriteEEHCIFDDO_MapWritingAbstractObjsVals(s, eehci_slot, reg_offset, new_v);
            var fd_id_val_map:map<FD_ID, FD_Val> := temp.0;
            var do_id_val_map:map<DO_ID, DO_Val> := temp.1;
            WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, map[], fd_id_val_map, do_id_val_map)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvWriteEEHCIFDDO_MapWritingAbstractObjsVals(s, eehci_slot, reg_offset, new_v);
            var fd_id_val_map:map<FD_ID, FD_Val> := temp.0;
            var do_id_val_map:map<DO_ID, DO_Val> := temp.1;
            DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, map[], fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true)
    ensures WK_WimpDrv_WriteEEHCIFDsDOs_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), wimpdrv_slot, eehci_slot, reg_offset, new_v, TRUE);
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    var drv_sid := wimpdrv_id.sid;
    var temp := F_WimpDrvWriteEEHCIFDDO_MapWritingAbstractObjsVals(s, eehci_slot, reg_offset, new_v);
    var td_id_val_map:map<TD_ID, TD_Val> := map[];
    var fd_id_val_map:map<FD_ID, FD_Val> := temp.0;
    var do_id_val_map:map<DO_ID, DO_Val> := temp.1;
    
    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);

    Lemma_WimpDrv_AccessEEHCIObjs_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, wimpdrv_slot, eehci_slot, td_ids, fd_ids, do_ids);

    // Prove WSD_WimpDrvWrite_PreConditions
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_WimpDrvWrite_PreConditions(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, map[], fd_id_val_map, do_id_val_map).1 == true
    Lemma_DM_GreenDrvWrite_ChkNewValsOfTDs_ReturnTrueOnEmpty(dm);
    assert DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, map[], fd_id_val_map, do_id_val_map).1 == true;

    // Prove DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, map[], fd_id_val_map, do_id_val_map).0 == dm'
    var op_result := DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, map[], fd_id_val_map, do_id_val_map);
    var dm' := WSM_MapState(s');
    Lemma_WimpDrv_WriteEEHCIFDDO_ProveOperationMapping(s, s', dm, dm', wimpdrv_slot, eehci_slot, reg_offset, new_v);

    // Prove property 2
    assert WSD_WimpDrvWrite_Stub(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_WimpDrvWriteEEHCIUSBTDReg_ProveCommutativeDiagram_ProvePreConditions(
    eehci_slot:word, usbtd_reg_id:word
)
    requires eehci_valid_slot_id(eehci_slot)
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS

    ensures var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + 
                            G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES;
             is_valid_addr(vaddr) &&
             is_valid_vaddr(vaddr)
{
    Lemma_eehci_slot_offset_in_content_AlwaysValidGEEHCIMemAddr(eehci_slot);
    var td_addr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset;
    assert is_gvar_valid_addr(G_EEHCI_MEM(), td_addr + usbtd_reg_id * UINT32_BYTES);
}

lemma Lemma_WimpDrvWriteEEHCIUSBTDReg_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    wimpdrv_slot:word, eehci_slot:word, usbtd_reg_id:word, usbtd_slot:word,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s');
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + 
                            G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES;
             is_valid_vaddr(vaddr) &&
             globals' == global_write_word(globals, G_EEHCI_MEM(), vaddr, usbtd_slot)
        // Requirement: WimpDrv_Write modifies global variables correctly
        // Relationship between s and s'

    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires usbtd_slot == USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(usbtd_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtd_map_valid_slot_id(usbtd_slot)
                ==> eehci_info_get_pid(globals, eehci_slot) == usbtd_map_get_pid(globals, usbtd_slot)
        // Requirement: The condition when WimpDrv_Write returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
        // Properties specific to WimpDrv_Write

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvWriteEEHCIUSBTDReg_MapWritingAbstractObjsVals(s, s', eehci_slot, usbtd_reg_id, usbtd_slot);
            var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
            var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
            var do_id_val_map:map<DO_ID, DO_Val> := temp.2;
            WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvWriteEEHCIUSBTDReg_MapWritingAbstractObjsVals(s, s', eehci_slot, usbtd_reg_id, usbtd_slot);
            var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
            var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
            var do_id_val_map:map<DO_ID, DO_Val> := temp.2;
            DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (WSM_MapState(s'), true)
    ensures WK_WimpDrv_WriteEEHCIUSBTDReg_CommutativeDiagram_Property(s, dm, s', WSM_MapState(s'), wimpdrv_slot, eehci_slot, usbtd_reg_id, usbtd_slot, TRUE);
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    var drv_sid := wimpdrv_id.sid;
    var temp := F_WimpDrvWriteEEHCIUSBTDReg_MapWritingAbstractObjsVals(s, s', eehci_slot, usbtd_reg_id, usbtd_slot);
    var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
    var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
    var do_id_val_map:map<DO_ID, DO_Val> := temp.2;
    
    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);

    Lemma_WimpDrv_AccessEEHCIUSBTDReg_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, wimpdrv_slot, eehci_slot, usbtd_slot, td_ids, fd_ids, do_ids);

    // Prove WSD_WimpDrvWrite_PreConditions
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_WimpDrvWrite_PreConditions(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
    assert DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true;

    // Prove DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == dm'
    var op_result := DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var dm' := WSM_MapState(s');
    Lemma_WimpDrv_WriteEEHCIUSBTDReg_ProveOperationMapping(s, s', dm, dm', wimpdrv_slot, eehci_slot, usbtd_reg_id, usbtd_slot);

    // Prove property 2
    assert WSD_WimpDrvWrite_Stub(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_WimpDrvReadEEHCIFDDO_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    wimpdrv_slot:word, eehci_slot:word, reg_offset:word,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || 
             reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset
    
    requires state_equal_except_mstate(s, s');
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             globals' == globals
        // Requirement: WimpDrv_Read does not modify global variables
        // Relationship between s and s'

    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
        // Requirement: The condition when WimpDrv_Write returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
        // Properties specific to WimpDrv_Write

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvReadEEHCIFDDO_MapReadingAbstractObjsVals(s, eehci_slot, reg_offset);
            var fd_ids:set<FD_ID> := temp.0;
            var do_ids:set<DO_ID> := temp.1;
            var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
            WSD_WimpDrvRead_PreConditions(dm, wimpdrv_id.sid, read_objs, map[], map[], map[])
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvReadEEHCIFDDO_MapReadingAbstractObjsVals(s, eehci_slot, reg_offset);
            var fd_ids:set<FD_ID> := temp.0;
            var do_ids:set<DO_ID> := temp.1;
            var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
            DM_GreenDrvRead_InnerFunc(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) == (WSM_MapState(s'), true)
    ensures WK_WimpDrv_ReadEEHCIFDsDOs_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), wimpdrv_slot, eehci_slot, reg_offset, TRUE);
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    var drv_sid := wimpdrv_id.sid;
    var temp := F_WimpDrvReadEEHCIFDDO_MapReadingAbstractObjsVals(s, eehci_slot, reg_offset);
    var td_ids:set<TD_ID> := {};
    var fd_ids:set<FD_ID> := temp.0;
    var do_ids:set<DO_ID> := temp.1;
    var read_objs := TDIDsToObjIDs({}) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);

    Lemma_WimpDrv_AccessEEHCIObjs_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, wimpdrv_slot, eehci_slot, td_ids, fd_ids, do_ids);

    Lemma_WimpDrvRead_ProveCommutativeDiagram(s, dm, wimpdrv_id, td_ids, fd_ids, do_ids);
    assert DM_GreenDrvRead_InnerFunc(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) == (dm, true);

    // Prove WSD_WimpDrvRead_PreConditions
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();

    // Prove dm == dm'
    var dm' := WSM_MapState(s');
    Lemma_WimpDrv_ReadEEHCIFDDO_ProveOperationMapping(s, s', dm, dm', wimpdrv_slot, eehci_slot, reg_offset);
    assert dm == dm';

    // Prove property 2
    var op_result := DM_GreenDrvRead_InnerFunc(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]);
    assert WSD_WimpDrvRead_Stub(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_WimpDrvReadEEHCIUSBTDReg_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    wimpdrv_slot:word, eehci_slot:word, usbtd_reg_slot:word,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires 0 <= usbtd_reg_slot < eEHCI_USBTD_SlotID_NUMS
    
    requires state_equal_except_mstate(s, s');
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             globals' == globals
        // Requirement: WimpDrv_Read does not modify global variables
        // Relationship between s and s'

    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
        // Requirement: The condition when WimpDrv_Write returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
        // Properties specific to WimpDrv_Write

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var td_ids := F_WimpDrvReadEEHCIUSBTDReg_MapReadingAbstractObjsVals(s, eehci_slot, usbtd_reg_slot);
            var read_objs := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs({}) + DOIDsToObjIDs({});
            WSD_WimpDrvRead_PreConditions(dm, wimpdrv_id.sid, read_objs, map[], map[], map[])
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var td_ids := F_WimpDrvReadEEHCIUSBTDReg_MapReadingAbstractObjsVals(s, eehci_slot, usbtd_reg_slot);
            var read_objs := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs({}) + DOIDsToObjIDs({});
            DM_GreenDrvRead_InnerFunc(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) == (WSM_MapState(s'), true)
    ensures WK_WimpDrv_ReadEEHCIUSBTDReg_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), wimpdrv_slot, eehci_slot, usbtd_reg_slot, TRUE);
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    var drv_sid := wimpdrv_id.sid;
    var td_ids:set<TD_ID> := F_WimpDrvReadEEHCIUSBTDReg_MapReadingAbstractObjsVals(s, eehci_slot, usbtd_reg_slot);
    var fd_ids:set<FD_ID> := {};
    var do_ids:set<DO_ID> := {};
    var read_objs := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs({}) + DOIDsToObjIDs({});

    Lemma_WimpDrv_AccessEEHCIObjs_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, wimpdrv_slot, eehci_slot, td_ids, fd_ids, do_ids);

    Lemma_WimpDrvRead_ProveCommutativeDiagram(s, dm, wimpdrv_id, td_ids, fd_ids, do_ids);
    assert DM_GreenDrvRead_InnerFunc(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) == (dm, true);

    // Prove WSD_WimpDrvRead_PreConditions
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();

    // Prove dm == dm'
    var dm' := WSM_MapState(s');
    Lemma_WimpDrv_ReadEEHCIUSBTDReg_ProveOperationMapping(s, s', dm, dm', wimpdrv_slot, eehci_slot, usbtd_reg_slot);
    assert dm == dm';

    // Prove property 2
    var op_result := DM_GreenDrvRead_InnerFunc(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]);
    assert WSD_WimpDrvRead_Stub(dm, wimpdrv_id.sid, read_objs, map[], map[], map[]) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_USBTD_Allocate1Slot_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    new_td_slot:word, new_idword:word, new_td_type:word, new_pid:word, 
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires new_idword != USBTD_ID_INVALID
    requires new_idword in s.id_mappings.usbtd_to_td
    requires new_idword in s.id_mappings.usbtd_to_fd
    requires new_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires usbtd_map_valid_slot_id(new_td_slot)
    requires (new_td_type == USBTDs_TYPE_QTD32) || (new_td_type == USBTDs_TYPE_QH32) || 
        (new_td_type == USBTDs_TYPE_iTD32) || (new_td_type == USBTDs_TYPE_siTD32)
        // Requirements needed by the following requirements
    requires state_equal_except_mstate(s, s')
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             usbtd_slot_allocate_1slot_globals_relationship(globals, globals', new_td_slot, new_idword, new_td_type, new_pid, TRUE)
        // Requirement: USBTD_slot_allocate_1slot modifies global variables correctly
        // Relationship between s and s'
        
    requires var globals := wkm_get_globals(s.wk_mstate);
             WS_PartitionID(new_pid) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:uint32 :: usbtd_map_valid_slot_id(i) &&
                    usbtd_map_get_idword(globals, i) != USBTD_ID_INVALID
                ==> usbtd_map_get_idword(globals, i) != new_idword
        // Requirement: The condition when USBTD_slot_allocate_1slot returns true

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[new_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[new_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[new_idword];
            usbtd_td_id in s.objects.usbtd_tds &&
            usbtd_fd_id in s.objects.usbtd_fds &&
            usbtd_do_id in s.objects.usbtd_dos
        // Properties needed by following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[new_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[new_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[new_idword];
            WKD_ExternalObjsActivateToGreenPartition_PreConditions(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid)
        // Property 1 
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[new_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[new_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[new_idword];
            DM_ExternalObjsActivateToGreenPartition_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid) == (WSM_MapState(s'), true)
    ensures WK_USBTD_Allocate1Slot_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), new_idword, new_pid, TRUE)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures P_DMObjectsHasUniqueIDs(WSM_MapState(s').objects)
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove Pre-conditions
    var globals := wkm_get_globals(s.wk_mstate);
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[new_idword];
    var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[new_idword];
    var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[new_idword];

    var globals' := wkm_get_globals(s'.wk_mstate);
    Lemma_USBTD_ExistInSystem_IfRegisteredAndActive(s'.subjects, s'.objects, s'.id_mappings, globals', new_td_slot);

    // Prove WKD_ExternalObjsActivateToGreenPartition_PreConditions
    Lemma_USBTD_Allocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, new_idword, new_pid);
    assert WKD_ExternalObjsActivateToGreenPartition_PreConditions(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid);

    // Prove DM_ExternalObjsActivateToGreenPartition_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid).1 == true
    assert DM_ExternalObjsActivateToGreenPartition_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid).1 == true;

    // Prove DM_ExternalObjsActivateToGreenPartition_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid).0 == dm'
    var op_result := DM_ExternalObjsActivateToGreenPartition_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid);
    var dm' := WSM_MapState(s');
    Lemma_USBTD_Allocate1Slot_ProveOperationMapping(s, s', dm, dm', new_td_slot, new_idword, new_td_type, new_pid);

    // Prove property 2
    assert WKD_ExternalObjsActivateToGreenPartition_Stub(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

// [NOTE] Needs 80s to verify
lemma Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    td_slot:word, 
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires usbtd_map_valid_slot_id(td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            usbtd_idword != USBTD_ID_INVALID &&
            usbtd_idword in s.id_mappings.usbtd_to_td &&
            usbtd_idword in s.id_mappings.usbtd_to_fd &&
            usbtd_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires state_equal_except_mstate(s, s')
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             usbtd_slot_deallocate_1slot_globals_relationship(globals, globals', td_slot, TRUE)
        // Requirement: USBTD_slot_deallocate_1slot modifies global variables correctly
        // Relationship between s and s'
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, usbtd_map_get_pid(globals, td_slot).v)
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_mem_no_ref_to_usbtd_slot(globals, td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtds_verifiedtds_do_not_associate_usbtd(globals, td_slot)
        // Requirement: The condition when USBTD_slot_allocate_1slot returns true

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var pid := usbtd_map_get_pid(globals, td_slot);
            var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            WKD_GreenExternalObjsDeactivate_PreConditions(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid)
        // Property 1 
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var pid := usbtd_map_get_pid(globals, td_slot);
            var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            DM_GreenExternalObjsDeactivate_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid) == (WSM_MapState(s'), true)
    ensures WK_USBTD_Deallocate1Slot_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), td_slot, TRUE)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures P_DMObjectsHasUniqueIDs(WSM_MapState(s').objects)
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove Pre-conditions
    var globals := wkm_get_globals(s.wk_mstate);
    var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
    var pid := usbtd_map_get_pid(globals, td_slot);
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
    var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
    var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
    var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];

    Lemma_USBTD_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, globals, td_slot);
    Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition_PreConditions(s, dm, td_slot);

    // Prove WKD_GreenExternalObjsDeactivate_PreConditions
    Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, td_slot, pid);
    assert WKD_GreenExternalObjsDeactivate_PreConditions(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid);

    // Prove DM_GreenExternalObjsDeactivate_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid).1 == true
    assert DM_GreenExternalObjsDeactivate_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid).1 == true;

    // Prove DM_GreenExternalObjsDeactivate_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid).0 == dm'
    var op_result := DM_GreenExternalObjsDeactivate_InnerFunc(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid);
    var dm' := WSM_MapState(s');
    Lemma_USBTD_Deallocate1Slot_ProveOperationMapping(s, s', dm, dm', td_slot);

    // Prove property 2
    assert WKD_GreenExternalObjsDeactivate_Stub(dm, {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_USBTD_Slot_SubmitAndVerify_ProveCommutativeDiagram(
    s:state, dm:DM_State,
    wimpdrv_slot:word, td_slot:word, td_type:word,
    usbpdev_slot:word, input_param1:word, input_param2:word, input_param3:word, eehci_id:word,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires usbtd_map_valid_slot_id(td_slot)
        // Requirements needed by the following requirements

    requires (td_type == USBTDs_TYPE_QTD32) || (td_type == USBTDs_TYPE_QH32)
    requires var globals' := wkm_get_globals(s'.wk_mstate);
             td_type == usbtd_map_get_type(globals', td_slot)
        // Requirements needed by the following requirements
    requires state_equal_except_mstate(s, s')
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             p_usbtd_slot_submit_and_verify_usbtd_ret_global(globals, globals', td_slot) &&
             p_usbtd_slot_submit_modification_to_usbtd(globals', td_slot, wimpdrv_slot, usbpdev_slot, input_param1, input_param2, input_param3, td_type, eehci_id)
        // Requirement: USBTD_slot_submit_and_verify_* modifies global variables correctly
        // Relationship between s and s'
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) == usbtd_map_get_pid(globals, td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires var globals' := wkm_get_globals(s'.wk_mstate);
             usbtd_map_get_flags(globals', td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
        // Requirement: The condition when USBTD_slot_submit_and_verify_* returns true
    
    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
        // Properties specific to USBTD_slot_submit_and_verify_*

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvSubmitUSBTD_MapWritingAbstractObjsVals(s, s', td_slot);
            WSD_WimpDrvWrite_PreConditions(dm, wimpdrv_id.sid, temp.0, temp.1, temp.2)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var temp := F_WimpDrvSubmitUSBTD_MapWritingAbstractObjsVals(s, s', td_slot);
            DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, temp.0, temp.1, temp.2) == (WSM_MapState(s'), true)
    ensures WK_USBTD_Slot_SubmitAndVerify_CommutativeDiagram_Property(s, dm, s', WSM_MapState(s'), wimpdrv_slot, td_slot, TRUE)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
    ensures WK_USBTD_Slot_SubmitAndVerify_SubjAndObjsInSamePartition(s, dm, s', WSM_MapState(s'), wimpdrv_slot, td_slot, TRUE)
        // Property 5: If return true, then the subject and objects being accessed must be in the same partition
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    var drv_sid := wimpdrv_id.sid;
    var temp := F_WimpDrvSubmitUSBTD_MapWritingAbstractObjsVals(s, s', td_slot);
    var td_id_val_map:map<TD_ID, TD_Val> := temp.0;
    var fd_id_val_map:map<FD_ID, FD_Val> := temp.1;
    var do_id_val_map:map<DO_ID, DO_Val> := temp.2;
    
    var td_ids := MapGetKeys(td_id_val_map);
    var fd_ids := MapGetKeys(fd_id_val_map);
    var do_ids := MapGetKeys(do_id_val_map);

    Lemma_WimpDrv_SubmitUSBTD_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, wimpdrv_slot, td_slot, td_ids, fd_ids, do_ids);

    // Prove WSD_WimpDrvWrite_PreConditions
    Lemma_AllOpsInConcreteModel_SatisfyP_DM_OpsProperties();
    assert WSD_WimpDrvWrite_PreConditions(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    // Prove DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true
    assert DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map).1 == true;

    // Prove DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map).0 == dm'
    var op_result := DM_GreenDrvWrite_InnerFunc(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var dm' := WSM_MapState(s');
    Lemma_USBTD_Slot_SubmitAndVerify_ProveOperationMapping(s, s', dm, dm', wimpdrv_slot, td_slot, td_type,
        usbpdev_slot, input_param1, input_param2, input_param3, eehci_id);

    // Prove property 2
    assert WSD_WimpDrvWrite_Stub(dm, wimpdrv_id.sid, td_id_val_map, fd_id_val_map, do_id_val_map) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    new_pid:word,
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
    requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)
        // Properties specific to OS_Activate_AllReleasedPEHCIsAndUSBPDevs

    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr) in s.subjects.usbpdevs
        // Requirements needed by the following requirements
    requires state_equal_except_mstate_subjs_objs(s, s');       
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE(s, s', all_non_empty_addrs)
        // Requirement: OS_Activate_AllReleasedPEHCIsAndUSBPDevs modifies global variables correctly
        // Relationship between s and s'
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_info_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: usbpdev_valid_slot_id(i)
                ==> usbpdev_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
        // Requirement: The condition when OS_Activate_AllReleasedPEHCIsAndUSBPDevs returns true

    requires new_pid == PID_RESERVED_OS_PARTITION

    ensures var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            var to_assign_dev_ids:seq<Dev_ID> := SetToSeq_Func(pehci_ids + usbpdev_ids);
            WKD_MultiDevs_ReturnOS_PreConditions(dm, to_assign_dev_ids)
        // Property 1
    ensures forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    ensures var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            var to_assign_dev_ids:seq<Dev_ID> := SetToSeq_Func(pehci_ids + usbpdev_ids);
            P_WSD_DevActivate_Multi_SubjObjModifications(dm, WSM_MapState(s'), pehci_ids + usbpdev_ids, dm.red_pid)
    ensures var dm' := WSM_MapState(s');
            WK_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_CommutativeDiagram_Property(s, dm, dm', TRUE)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures P_DMObjectsHasUniqueIDs(WSM_MapState(s').objects)
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove WKD_MultiDevs_ReturnOS_PreConditions
    var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
    var to_assign_dev_ids:seq<Dev_ID> := SetToSeq_Func(pehci_ids + usbpdev_ids);
    assert WKD_MultiDevs_ReturnOS_PreConditions(dm, to_assign_dev_ids);

    // Prove WKD_MultiDevs_ReturnOS returns true
    var pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    var dev_ids := pehci_ids + usbpdev_ids;
    Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, new_pid);
    assert P_WSD_DevActivate_Multi_ConditionForReturnTrue(dm, dev_ids, pid);

    Lemma_SetToSeq_Func_Property(dev_ids);
    assert SeqToSet(SetToSeq_Func(dev_ids)) == dev_ids;
    assert SeqToSet(to_assign_dev_ids) == dev_ids;
    assert P_WSD_DevActivate_Multi_ConditionForReturnTrue(dm, SeqToSet(to_assign_dev_ids), pid);

    // Prove P_WSD_DevActivate_Multi_SubjObjModifications(dm, dm', dev_ids, dm.red_pid)
    var op_result := WKD_MultiDevs_ReturnOS_Stub(dm, to_assign_dev_ids);
    assert op_result.1 == true;

    // Prove P_WSD_DevActivate_Multi_SubjObjModifications(ws, WSM_MapState(s'), pehci_ids + usbpdev_ids, ws.red_pid)
    var dm' := WSM_MapState(s');
    Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveOperationMapping(s, s', dm, dm', new_pid);

    // Prove P_WSD_DevActivate_Multi_SubjObjModifications(dm, dm', dev_ids, dm.red_pid)
    Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveP_WSD_DevActivate_Multi_SubjObjModifications(
        dm, dm', to_assign_dev_ids, dev_ids);
    assert P_WSD_DevActivate_Multi_SubjObjModifications(dm, dm', dev_ids, dm.red_pid);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
    assert WSM_OpsSaneState_Security_SI1(s');
}

lemma Lemma_OS_Activate_MainMem_ByPAddr_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    paddr_start:word, paddr_end:word, 
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires WK_ValidPMemRegion(paddr_start, paddr_end)
        // Properties specific to OS_Activate_MainMem_ByPAddr
    requires state_equal_except_mstate_subjs_objs_memactivemap(s, s')
    requires ffi_pmem_activate_main_mem_in_os_stack_and_statevars_inner(s, paddr_start, paddr_end, TRUE, s'.subjects, s'.objects, s'.os_mem_active_map)
        // Requirement: OS_Activate_MainMem_ByPAddr modifies global variables correctly
        // Relationship between s and s'

    ensures var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
            var os_tds := result.1;
            var os_fds := result.2;
            var os_dos := result.3; 
            WKD_ExternalObjsActivateToRedPartition_PreConditions(dm, os_tds, os_fds, os_dos)
        // Property 1
    ensures var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
            var os_tds := result.1;
            var os_fds := result.2;
            var os_dos := result.3; 
            DM_ExternalObjsActivateToRedPartition_InnerFunc(dm, os_tds, os_fds, os_dos) == (WSM_MapState(s'), true)
    ensures OS_Activate_MainMem_ByPAddr_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), paddr_start, paddr_end, TRUE)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove WKD_ExternalObjsActivateToRedPartition_PreConditions
    var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
    var os_tds := result.1;
    var os_fds := result.2;
    var os_dos := result.3; 

    Lemma_OS_Activate_MainMem_ByPAddr_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, paddr_start, paddr_end, s');
    assert WKD_ExternalObjsActivateToRedPartition_PreConditions(dm, os_tds, os_fds, os_dos);

    // Prove DM_ExternalObjsActivateToRedPartition_InnerFunc(dm, os_tds, os_fds, os_dos).1 == true
    assert DM_ExternalObjsActivateToRedPartition_InnerFunc(dm, os_tds, os_fds, os_dos).1 == true;

    // Prove DM_ExternalObjsActivateToRedPartition_InnerFunc(dm, os_tds, os_fds, os_dos).0 == dm'
    var op_result := DM_ExternalObjsActivateToRedPartition_InnerFunc(dm, os_tds, os_fds, os_dos);
    var dm' := WSM_MapState(s');
    Lemma_OS_Activate_MainMem_ByPAddr_ProveOperationMapping(s, s', dm, dm', paddr_start, paddr_end);

    // Prove property 2
    assert WKD_ExternalObjsActivateToRedPartition_Stub(dm, os_tds, os_fds, os_dos) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_OS_Deactivate_MainMem_ByPAddr_ProveCommutativeDiagram(
    s:state, dm:DM_State, 
    paddr_start:word, paddr_end:word, 
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)
    requires OpsSaneStateSubset(s')

    requires WK_ValidPMemRegion(paddr_start, paddr_end)
    requires P_OS_Deactivate_MainMem_ByPAddr_AdditonalPreConditions(s, dm, paddr_start, paddr_end)
        // Properties specific to OS_Activate_MainMem_ByPAddr
    requires state_equal_except_mstate_subjs_objs_memactivemap(s, s')
    requires ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars_inner(s, paddr_start, paddr_end, s'.subjects, s'.objects, s'.os_mem_active_map)
        // Requirement: OS_Activate_MainMem_ByPAddr modifies global variables correctly
        // Relationship between s and s'

    ensures var result := os_external_objs_to_be_deactivated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
            var os_tds := result.1;
            var os_fds := result.2;
            var os_dos := result.3; 
            WKD_RedExternalObjsDeactivate_PreConditions(dm, os_tds, os_fds, os_dos)
        // Property 1
    ensures var result := os_external_objs_to_be_deactivated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
            var os_tds := result.1;
            var os_fds := result.2;
            var os_dos := result.3; 
            DM_RedExternalObjsDeactivate_InnerFunc(dm, os_tds, os_fds, os_dos) == (WSM_MapState(s'), true)
    ensures OS_Deactivate_MainMem_ByPAddr_CommutativeDiagram_Property(s, dm, WSM_MapState(s'), paddr_start, paddr_end)
        // Property 2
    ensures WSM_OpsSaneState_Security_SI1(s')
        // Property 3
    ensures DM_IsSecureOps(dm, WSM_MapState(s'))
        // Property 4
{
    // Prove WKD_RedExternalObjsDeactivate_PreConditions
    var result := os_external_objs_to_be_deactivated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
    var os_tds := result.1;
    var os_fds := result.2;
    var os_dos := result.3; 

    Lemma_OS_Deactivate_MainMem_ByPAddr_ProveCommutativeDiagram_ProveMappingOfOpsCondition(s, dm, paddr_start, paddr_end, s');
    assert WKD_RedExternalObjsDeactivate_PreConditions(dm, os_tds, os_fds, os_dos);

    // Prove DM_RedExternalObjsDeactivate_InnerFunc(dm, os_tds, os_fds, os_dos).1 == true
    assert DM_RedExternalObjsDeactivate_InnerFunc(dm, os_tds, os_fds, os_dos).1 == true;

    // Prove DM_RedExternalObjsDeactivate_InnerFunc(dm, os_tds, os_fds, os_dos).0 == dm'
    var op_result := DM_RedExternalObjsDeactivate_InnerFunc(dm, os_tds, os_fds, os_dos);
    var dm' := WSM_MapState(s');
    Lemma_OS_Deactivate_MainMem_ByPAddr_ProveOperationMapping(s, s', dm, dm', paddr_start, paddr_end);

    // Prove property 2
    assert WKD_RedExternalObjsDeactivate_Stub(dm, os_tds, os_fds, os_dos) == (op_result.0, op_result.1);

    // Prove property 3
    reveal WSM_OpsSaneState_Security_SI1();
}




/*********************** Private Lemmas ********************/
lemma Lemma_WK_EmptyPartitionCreate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    new_pid:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires var globals := wkm_get_globals(s.wk_mstate);
             WS_PartitionID(new_pid) !in pids_parse_g_wimp_pids(globals) &&
             new_pid != PID_INVALID &&
             new_pid != PID_RESERVED_OS_PARTITION
        // Requirement: The condition when WK_EmptyPartitionCreate returns true

    ensures var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            dm_new_pid != NULL &&
            dm_new_pid !in dm.pids
{
    Lemma_SaneWSMState_MapGreenPID(s, dm, WS_PartitionID(new_pid));
}

lemma Lemma_WK_EmptyPartitionDestroy_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    pid:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, pid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             (forall i :: eehci_valid_slot_id(i)
                    ==> eehci_info_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: usbpdev_valid_slot_id(i)
                    ==> usbpdev_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: usbtd_map_valid_slot_id(i)
                    ==> usbtd_map_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: wimpdrv_valid_slot_id(i)
                    ==> wimpdrv_get_pid(globals, i) != WS_PartitionID(pid))
        // Requirement: The condition when WK_EmptyPartitionDestroy returns true

    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(pid));
            dm_pid != NULL &&
            dm_pid in dm.pids &&
            (forall s_id :: s_id in DM_AllSubjsIDs(dm.subjects) ==> DM_SubjPID(dm.subjects, s_id) != dm_pid) &&
            (forall o_id :: o_id in DM_AllObjsIDs(dm.objects) ==> DM_ObjPID(dm.objects, o_id) != dm_pid) &&
            dm_pid != dm.red_pid
{
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(pid));

    Lemma_SaneWSMState_MapGreenPID(s, dm, WS_PartitionID(pid));

    Lemma_WK_EmptyPartitionDestroy_ProveCommutativeDiagram_ProveMappingOfOpsCondition_SubjPIDs(s, dm, pid);
    Lemma_WK_EmptyPartitionDestroy_ProveCommutativeDiagram_ProveMappingOfOpsCondition_ObjPIDs(s, dm, pid);
}

lemma Lemma_WimpDrv_Activate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    drv_slot:uint32, new_wimpdrv_idword:uint32, new_wimpdrv_pid:uint32
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires new_wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword) in s.subjects.wimp_drvs 
    requires wimpdrv_valid_slot_id(drv_slot)
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, new_wimpdrv_pid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: wimpdrv_valid_slot_id(i)
                ==> wimpdrv_get_id_word(globals, i) != new_wimpdrv_idword
        // Requirement: The condition when WimpDrv_Activate returns true

    ensures var dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_wimpdrv_pid));
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword);
            DM_SubjPID(dm.subjects, wimpdrv_id.sid) == NULL && 
            dm_new_pid in dm.pids
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword);

    assert WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals);

    Lemma_SubjPID_WimpDrvNotInRecord_SubjPIDEqualsToNULL(s.subjects, s.objects, s.id_mappings, globals, new_wimpdrv_idword, wimpdrv_id.sid);
    assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid) == WS_PartitionID(PID_INVALID);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm); 
}

lemma Lemma_USBPDev_Activate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    usbpdev_slot:uint32, new_pid:uint32, new_usbpdev_addr_low:word, new_usbpdev_addr_high:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
        // Properties specific to USBPDev activation
    requires var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(new_usbpdev_addr_raw) &&
             usb_is_usbpdev_addr_valid(empty_addr) &&
             usb_parse_usbpdev_addr(new_usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr)
    requires var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
             var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
             var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);
             usbpdev_id in s.subjects.usbpdevs
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, new_pid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: usbpdev_valid_slot_id(i)
                ==> !(usbpdev_get_addr_low(globals, i) == new_usbpdev_addr_low &&
                        usbpdev_get_addr_high(globals, i) == new_usbpdev_addr_high)
        // Requirement: The condition when USBPDev_Activate returns true

    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
            var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);
            DM_SubjPID(dm.subjects, usbpdev_id.sid) == NULL && 
            dm_pid in dm.pids &&
                // Property 1
            (dm_pid == dm.red_pid ==> TryActivateDevInRed(dm, usbpdev_id)) &&
            (dm_pid != dm.red_pid ==> TryActivateDevInGreen(dm, usbpdev_id)) &&
                // Property 2: If the device is an ephemeral device, the two checks decide 
                // if we can activate the device into the destination partition
            (forall hcoded_td_id, td_id :: hcoded_td_id == dm.subjects.devs[usbpdev_id].hcoded_td_id &&
                        td_id in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
                    ==> W !in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds[td_id].amodes)
                // Property 3
{
    var globals := wkm_get_globals(s.wk_mstate);
    var new_usbpdev_addr_raw := UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
    var new_usbpdev_addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw);
    var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, new_usbpdev_addr);

    assert WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals);

    // Prove Property 1
    Lemma_SubjPID_USBPDevNotInRecord_SubjPIDEqualsToNULL(s.subjects, s.objects, s.id_mappings, globals, 
        new_usbpdev_addr_low, new_usbpdev_addr_high, usbpdev_id.sid);
    assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, usbpdev_id.sid) == WS_PartitionID(PID_INVALID);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);

    // Prove Property 2
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    Lemma_USBPDev_CanBeActivatedInRedOrGreen(s, dm, usbpdev_id);

    // Prove Property 3
    Lemma_WSMStateMapping_EquivilantBuildMap_DevsToHCodedTDVals(s, dm);
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    Lemma_USBPDev_HCodedTDDoNotDefineTransferToTDs(s, usbpdev_id);
}

lemma Lemma_EEHCI_Activate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    eehci_slot:uint32, new_pid:uint32, eehci_idword:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)
        // Properties specific to EEHCI activation
    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_idword != eEHCI_ID_INVALID
    requires var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
             eehci_id in s.subjects.eehcis
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, new_pid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_mem_get_eehci_id(globals, i) != eehci_idword
        // Requirement: The condition when EEHCI_Activate returns true

    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            DM_SubjPID(dm.subjects, eehci_id.sid) == NULL && 
            dm_pid in dm.pids &&
                // Property 1
            (dm_pid == dm.red_pid ==> TryActivateDevInRed(dm, eehci_id)) &&
            (dm_pid != dm.red_pid ==> TryActivateDevInGreen(dm, eehci_id)) &&
                // Property 2: If the device is an ephemeral device, the two checks decide 
                // if we can activate the device into the destination partition
            (forall hcoded_td_id, td_id :: hcoded_td_id == dm.subjects.devs[eehci_id].hcoded_td_id &&
                        td_id in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
                    ==> W !in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds[td_id].amodes)
                // Property 3
{
    var globals := wkm_get_globals(s.wk_mstate);
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);

    assert WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals);

    // Prove Property 1
    Lemma_SubjPID_EEHCINotInRecord_SubjPIDEqualsToNULL(s.subjects, s.objects, s.id_mappings, globals, 
        eehci_idword, eehci_id.sid);
    assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid) == WS_PartitionID(PID_INVALID);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    assert dm_pid != dm.red_pid;

    // Prove Property 2
    Lemma_EEHCI_CanBeActivatedInGreen(s, dm, eehci_id);

    // Prove Property 3
    Lemma_WSMStateMapping_EquivilantBuildMap_DevsToHCodedTDVals(s, dm);
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    Lemma_EEHCI_HCodedTDDoNotDefineWriteTransferToTDs(s, eehci_id);
}

lemma Lemma_WimpDrv_Deactivate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    drv_slot:uint32
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires wimpdrv_valid_slot_id(drv_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
             wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, wimpdrv_get_pid(globals, drv_slot).v)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtds_verifiedtds_do_not_associate_wimpdrv(globals, drv_slot)
        // Requirement: The condition when WimpDrv_Activate returns true

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid);
            pid != WS_PartitionID(PID_INVALID) &&
            pid != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            DM_SubjPID(dm.subjects, wimpdrv_id.sid) != NULL && 
            DM_SubjPID(dm.subjects, wimpdrv_id.sid) != dm.red_pid
        // Property 1:
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var todeactivate_td_ids := dm.subjects.drvs[wimpdrv_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.drvs[wimpdrv_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.drvs[wimpdrv_id].do_ids;
            var pid := DM_SubjPID(dm.subjects, wimpdrv_id.sid);
            DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(dm, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);

    // Prove property 1
    Lemma_SubjPID_RegisteredWimpDrv_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, drv_slot, wimpdrv_id.sid);
    var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid);
    assert pid != WS_PartitionID(PID_INVALID);
    assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);

    // Prove property 2
    var todeactivate_td_ids := dm.subjects.drvs[wimpdrv_id].td_ids;
    var todeactivate_fd_ids := dm.subjects.drvs[wimpdrv_id].fd_ids;
    var todeactivate_do_ids := dm.subjects.drvs[wimpdrv_id].do_ids;

    assert todeactivate_td_ids == {};
    assert todeactivate_fd_ids == {};
    assert todeactivate_do_ids == {s.subjects.wimp_drvs[wimpdrv_id].do_id};

    Lemma_WimpDrv_Deactivate_NoGreenTDRefsWimpDrvToBeDeactivated(s, dm, drv_slot);
}

lemma Lemma_USBPDev_Deactivate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    usbpdev_slot:uint32
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
        // Properties specific to USBPDev

    requires usbpdev_valid_slot_id(usbpdev_slot)
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, usbpdev_get_pid(globals, usbpdev_slot).v)
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbpdev_get_updateflag(globals, usbpdev_slot) == WimpUSBPDev_Slot_UpdateFlag_Complete
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtds_verifiedtds_do_not_associate_usb_pdev(globals, usbpdev_slot)
        // Requirement: The condition when USBPDev_Deactivate returns true

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var empty_addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
            usb_is_usbpdev_addr_valid(empty_addr_raw) &&
            usb_is_usbpdev_addr_valid(usbpdev_addr_raw) &&
            usb_parse_usbpdev_addr(usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr_raw)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            usbpdev_id in s.subjects.usbpdevs
        // Properties needed by the following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, usbpdev_id.sid);
            pid != WS_PartitionID(PID_INVALID) &&
            pid != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            DM_SubjPID(dm.subjects, usbpdev_id.sid) != NULL && 
            DM_SubjPID(dm.subjects, usbpdev_id.sid) != dm.red_pid
        // Property 1:
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            var todeactivate_td_ids := dm.subjects.devs[usbpdev_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.devs[usbpdev_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.devs[usbpdev_id].do_ids;
            var pid := DM_SubjPID(dm.subjects, usbpdev_id.sid);
            DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(dm, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
    var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

    // Prove preconditions
    Lemma_USBPDevAddr_NonEmptyAddrRawParseToNonEmptyAddr(usbpdev_addr_raw);
    var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
    Lemma_USBPDevs_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, globals, usbpdev_slot);

    // Prove property 1
    Lemma_SubjPID_RegisteredUSBPDev_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, usbpdev_slot, usbpdev_id.sid);
    var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, usbpdev_id.sid);
    assert pid != WS_PartitionID(PID_INVALID);
    assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);

    // Prove property 2
    var todeactivate_td_ids := dm.subjects.devs[usbpdev_id].td_ids;
    var todeactivate_fd_ids := dm.subjects.devs[usbpdev_id].fd_ids;
    var todeactivate_do_ids := dm.subjects.devs[usbpdev_id].do_ids;

    Lemma_USBPDev_Deactivate_NoGreenTDRefsWimpDrvToBeDeactivated(s, dm, usbpdev_slot);
}

lemma Lemma_EEHCI_Deactivate_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    eehci_slot:uint32
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, eehci_info_get_pid(globals, eehci_slot).v)
        // Requirement: The condition when USBPDev_Deactivate returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid);
            pid != WS_PartitionID(PID_INVALID) &&
            pid != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            DM_SubjPID(dm.subjects, eehci_id.sid) != NULL && 
            DM_SubjPID(dm.subjects, eehci_id.sid) != dm.red_pid
        // Property 1:
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            var todeactivate_td_ids := dm.subjects.devs[eehci_id].td_ids;
            var todeactivate_fd_ids := dm.subjects.devs[eehci_id].fd_ids;
            var todeactivate_do_ids := dm.subjects.devs[eehci_id].do_ids;
            var pid := DM_SubjPID(dm.subjects, eehci_id.sid);
            DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(dm, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
    var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);

    // Prove property 1
    Lemma_SubjPID_RegisteredEEHCI_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, eehci_slot, eehci_id.sid);
    var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid);
    assert pid != WS_PartitionID(PID_INVALID);
    assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);

    // Prove property 2
    Lemma_EEHCI_Deactivate_NoGreenTDRefsWimpDrvToBeDeactivated(s, dm, eehci_slot);
}

lemma Lemma_WimpDrv_AccessEEHCIObjs_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    wimpdrv_slot:word, eehci_slot:word, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
        // Requirement: The condition when WimpDrv_Write returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
        // Properties specific to WimpDrv_Write

    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            (forall id :: id in td_ids ==> id in s.subjects.eehcis[eehci_id].td_ids) &&
            (forall id :: id in fd_ids ==> id in s.subjects.eehcis[eehci_id].fd_ids) &&
            (forall id :: id in do_ids ==> id in s.subjects.eehcis[eehci_id].do_ids) &&
            (forall id :: id in td_ids ==> id !in WSM_AllHCodedTDIDs(s.subjects))
        // Requirement: Objects to be accessed must be owned by the eEHCI <eehci_id>

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid);
            pid != WS_PartitionID(PID_INVALID) &&
            pid != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            DM_SubjPID(dm.subjects, wimpdrv_id.sid) != NULL && 
            DM_SubjPID(dm.subjects, wimpdrv_id.sid) != dm.red_pid
        // Property 1:
    ensures (forall td_id :: td_id in td_ids ==> td_id in AllTDIDs(dm.objects)) &&
            (forall fd_id :: fd_id in fd_ids ==> fd_id in AllFDIDs(dm.objects)) &&
            (forall do_id :: do_id in do_ids ==> do_id in AllDOIDs(dm.objects))
    ensures (forall dev_id :: dev_id in dm.subjects.devs
                ==> dm.subjects.devs[dev_id].hcoded_td_id !in td_ids)
        // Property 2
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
        // Property 3
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);

    // Prove property 1
    Lemma_SubjPID_RegisteredWimpDrv_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_slot, wimpdrv_id.sid);
    var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid);
    assert pid != WS_PartitionID(PID_INVALID);
    assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    // Prove property 3
    var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
    var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
    Lemma_SubjPID_RegisteredEEHCI_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, eehci_slot, eehci_id.sid);
    var eehci_pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid);
    assert pid == eehci_pid;

    Lemma_WimpDrv_AccessEEHCIObjs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property3(s, dm, wimpdrv_id, eehci_id, td_ids, fd_ids, do_ids);
}

lemma Lemma_WimpDrv_AccessEEHCIUSBTDReg_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    wimpdrv_slot:word, eehci_slot:word, usbtd_slot:word, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires eehci_valid_slot_id(eehci_slot)
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires usbtd_slot == USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(usbtd_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtd_map_valid_slot_id(usbtd_slot)
                ==> eehci_info_get_pid(globals, eehci_slot) == usbtd_map_get_pid(globals, usbtd_slot)
        // Requirement: The condition when WimpDrv_Write returns true

    requires usbtd_slot == USBTD_SlotID_INVALID
                ==> td_ids == {} && fd_ids == {} && do_ids == {}

    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis
        // Properties specific to WimpDrv_Write

    requires (forall id :: id in td_ids ==> id in s.objects.usbtd_tds) &&
            (forall id :: id in fd_ids ==> id in s.objects.usbtd_fds) &&
            (forall id :: id in do_ids ==> id in s.objects.usbtd_dos) &&
            (forall id :: id in td_ids ==> id !in WSM_AllHCodedTDIDs(s.subjects))
        // Requirement: Objects to be accessed must be usbtd_*
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtd_map_valid_slot_id(usbtd_slot)
                ==> (
                        var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
                        (forall id :: id in td_ids
                            ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
                        (forall id :: id in fd_ids
                            ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
                        (forall id :: id in do_ids
                            ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword)
                )

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid);
            pid != WS_PartitionID(PID_INVALID) &&
            pid != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            DM_SubjPID(dm.subjects, wimpdrv_id.sid) != NULL && 
            DM_SubjPID(dm.subjects, wimpdrv_id.sid) != dm.red_pid
        // Property 1:
    ensures (forall td_id :: td_id in td_ids ==> td_id in AllTDIDs(dm.objects)) &&
            (forall fd_id :: fd_id in fd_ids ==> fd_id in AllFDIDs(dm.objects)) &&
            (forall do_id :: do_id in do_ids ==> do_id in AllDOIDs(dm.objects))
    ensures (forall dev_id :: dev_id in dm.subjects.devs
                ==> dm.subjects.devs[dev_id].hcoded_td_id !in td_ids)
        // Property 2
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
        // Property 3
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);

    // Prove property 1
    Lemma_SubjPID_RegisteredWimpDrv_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_slot, wimpdrv_id.sid);
    var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid);
    assert pid != WS_PartitionID(PID_INVALID);
    assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    // Prove property 3
    var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
    var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
    Lemma_SubjPID_RegisteredEEHCI_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, eehci_slot, eehci_id.sid);
    var eehci_pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid);
    assert pid == eehci_pid;

    if(usbtd_slot == USBTD_SlotID_INVALID)
    {
        assert DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, wimpdrv_id.sid, td_ids, fd_ids, do_ids);
    }
    else
    {
        assert usbtd_map_valid_slot_id(usbtd_slot);
        Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord_TDsFDsDOs(s.subjects, s.objects, s.id_mappings, globals, usbtd_slot, td_ids, fd_ids, do_ids);

        Lemma_WimpDrv_AccessEEHCIUSBTDRegs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property3(s, dm, wimpdrv_id, eehci_id, td_ids, fd_ids, do_ids);
    }
}

lemma Lemma_USBTD_Allocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    usbtd_idword:word, new_pid:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires usbtd_idword != USBTD_ID_INVALID
    requires usbtd_idword in s.id_mappings.usbtd_to_td
    requires usbtd_idword in s.id_mappings.usbtd_to_fd
    requires usbtd_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             WS_PartitionID(new_pid) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:uint32 :: usbtd_map_valid_slot_id(i) &&
                    usbtd_map_get_idword(globals, i) != USBTD_ID_INVALID
                ==> usbtd_map_get_idword(globals, i) != usbtd_idword
        // Requirement: The condition when EEHCI_Activate returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in s.objects.usbtd_tds &&
            usbtd_fd_id in s.objects.usbtd_fds &&
            usbtd_do_id in s.objects.usbtd_dos
        // Requirement: Mapped TDs/FDs/DOs must exist in the system
    
    ensures new_pid != PID_INVALID &&
            new_pid != PID_RESERVED_OS_PARTITION
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            dm_pid != NULL && 
            dm_pid != dm.red_pid
        // Property 1: <new_pid> must be a wimp partition's PID
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in AllTDIDs(dm.objects) &&
            usbtd_fd_id in AllFDIDs(dm.objects) &&
            usbtd_do_id in AllDOIDs(dm.objects)
        // Property 2: usbtd_* must exist in the system
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            forall s_id, o_id :: s_id in DM_AllSubjsIDs(dm.subjects) &&
                    o_id in (TDIDsToObjIDs({usbtd_td_id}) + FDIDsToObjIDs({usbtd_fd_id}) + DOIDsToObjIDs({usbtd_do_id}))
                ==> !DM_DoOwnObj(dm.subjects, s_id, o_id)
        // Property 3: usbtd_* must be external objects
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            DM_ObjPID(dm.objects, usbtd_td_id.oid) == NULL &&
            DM_ObjPID(dm.objects, usbtd_fd_id.oid) == NULL &&
            DM_ObjPID(dm.objects, usbtd_do_id.oid) == NULL
        // Property 4:
{
    var globals := wkm_get_globals(s.wk_mstate);
    var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
    var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
    var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];

    // Prove property 1
    assert new_pid != PID_INVALID;
    assert new_pid != PID_RESERVED_OS_PARTITION;

    // Prove property 3
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_USBTDsAreExternalObjs(s);
    forall s_id, o_id | s_id in DM_AllSubjsIDs(dm.subjects) &&
                    o_id in (TDIDsToObjIDs({usbtd_td_id}) + FDIDsToObjIDs({usbtd_fd_id}) + DOIDsToObjIDs({usbtd_do_id}))
        ensures !DM_DoOwnObj(dm.subjects, s_id, o_id)
    {
        Lemma_TDFDDOIDsToObjIDs_Sum_Property(usbtd_td_id, usbtd_fd_id, usbtd_do_id, o_id);
        assert TD_ID(o_id) == usbtd_td_id || FD_ID(o_id) == usbtd_fd_id || DO_ID(o_id) == usbtd_do_id;

        assert !WSM_DoOwnObj(s.subjects, s_id, o_id);
        Lemma_WSMStateMapping_EquivilantObjOwnership(s, dm);
        assert !DM_DoOwnObj(dm.subjects, s_id, o_id);
    }

    // Prove property 4
    Lemma_USBTD_Allocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property4(s, dm, usbtd_idword);
}

lemma Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    td_slot:word, pid:WS_PartitionID
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires usbtd_map_valid_slot_id(td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            usbtd_idword != USBTD_ID_INVALID &&
            usbtd_idword in s.id_mappings.usbtd_to_td &&
            usbtd_idword in s.id_mappings.usbtd_to_fd &&
            usbtd_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, usbtd_map_get_pid(globals, td_slot).v)
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_mem_no_ref_to_usbtd_slot(globals, td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtds_verifiedtds_do_not_associate_usbtd(globals, td_slot)
        // Requirement: The condition when USBTD_slot_allocate_1slot returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in s.objects.usbtd_tds &&
            usbtd_fd_id in s.objects.usbtd_fds &&
            usbtd_do_id in s.objects.usbtd_dos
        // Requirement: Mapped TDs/FDs/DOs must exist in the system

    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_td_id.oid) == pid &&
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_fd_id.oid) == pid &&
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_do_id.oid) == pid
        // Requirement: Mapped TDs/FDs/DOs are in the partition <pid>
    
    ensures pid != WS_PartitionID(PID_INVALID) &&
            pid != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
            dm_pid != NULL && 
            dm_pid != dm.red_pid
        // Property 1: <new_pid> must be a wimp partition's PID
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in AllTDIDs(dm.objects) &&
            usbtd_fd_id in AllFDIDs(dm.objects) &&
            usbtd_do_id in AllDOIDs(dm.objects)
        // Property 2: usbtd_* must exist in the system
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            forall s_id, o_id :: s_id in DM_AllSubjsIDs(dm.subjects) &&
                    o_id in (TDIDsToObjIDs({usbtd_td_id}) + FDIDsToObjIDs({usbtd_fd_id}) + DOIDsToObjIDs({usbtd_do_id}))
                ==> !DM_DoOwnObj(dm.subjects, s_id, o_id)
        // Property 3: usbtd_* must be external objects
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            DM_ObjPID(dm.objects, usbtd_td_id.oid) == dm_pid &&
            DM_ObjPID(dm.objects, usbtd_fd_id.oid) == dm_pid &&
            DM_ObjPID(dm.objects, usbtd_do_id.oid) == dm_pid 
        // Property 4:
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(dm, 
                {usbtd_td_id}, {usbtd_fd_id}, {usbtd_do_id}, dm_pid)
        // Property 5:
{
    var globals := wkm_get_globals(s.wk_mstate);
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
    var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
    var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
    var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
    var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];

    // Prove property 1
    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedTD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_td_id);
    Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, td_slot, usbtd_td_id.oid);

    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedFD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_fd_id);
    Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, td_slot, usbtd_fd_id.oid);

    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedDO(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_do_id);
    Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, td_slot, usbtd_do_id.oid);
    
    assert pid in pids_parse_g_wimp_pids(globals);
    assert pid != WS_PartitionID(PID_INVALID);
    assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);

    // Prove property 4
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_td_id.oid)) == DM_ObjPID(dm.objects, usbtd_td_id.oid);
    assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_fd_id.oid)) == DM_ObjPID(dm.objects, usbtd_fd_id.oid);
    assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_do_id.oid)) == DM_ObjPID(dm.objects, usbtd_do_id.oid);

    // Prove property 3
    Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property3(s, dm, td_slot, pid);

    // Prove property 5
    Lemma_USBTD_Deallocate1Slot_NoGreenTDRefsWimpDrvToBeDeactivated(s, dm, td_slot, pid);
}

lemma Lemma_WimpDrv_SubmitUSBTD_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    wimpdrv_slot:word, td_slot:word, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires usbtd_map_valid_slot_id(td_slot)
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) in pids_parse_g_wimp_pids(globals)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_get_pid(globals, wimpdrv_slot) == usbtd_map_get_pid(globals, td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
        // Requirement: The condition when WimpDrv_Write returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            wimpdrv_id in s.subjects.wimp_drvs
        // Properties specific to WimpDrv_Write

    requires (forall id :: id in td_ids ==> id in s.objects.usbtd_tds) &&
            (forall id :: id in fd_ids ==> id in s.objects.usbtd_fds) &&
            (forall id :: id in do_ids ==> id in s.objects.usbtd_dos) &&
            (forall id :: id in td_ids ==> id !in WSM_AllHCodedTDIDs(s.subjects))
        // Requirement: Objects to be accessed must be usbtd_*
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            (forall id :: id in td_ids
                ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
            (forall id :: id in fd_ids
                ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
            (forall id :: id in do_ids
                ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword)
        // Property: The objects in the result all maps to the USB TD <usbtd_idword> at the slot <new_v>

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid);
            pid != WS_PartitionID(PID_INVALID) &&
            pid != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            DM_SubjPID(dm.subjects, wimpdrv_id.sid) != NULL && 
            DM_SubjPID(dm.subjects, wimpdrv_id.sid) != dm.red_pid
        // Property 1:
    ensures (forall td_id :: td_id in td_ids ==> td_id in AllTDIDs(dm.objects)) &&
            (forall fd_id :: fd_id in fd_ids ==> fd_id in AllFDIDs(dm.objects)) &&
            (forall do_id :: do_id in do_ids ==> do_id in AllDOIDs(dm.objects))
    ensures (forall dev_id :: dev_id in dm.subjects.devs
                ==> dm.subjects.devs[dev_id].hcoded_td_id !in td_ids)
        // Property 2
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
        // Property 3
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);

    // Prove property 1
    Lemma_SubjPID_RegisteredWimpDrv_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_slot, wimpdrv_id.sid);
    var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid);
    assert pid != WS_PartitionID(PID_INVALID);
    assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    // Prove property 3
    Lemma_WimpDrv_SubmitUSBTD_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property3(s, dm, wimpdrv_id, td_slot, td_ids, fd_ids, do_ids);
}

lemma Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    new_pid:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
    requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)
        // Properties specific to OS_Activate_AllReleasedPEHCIsAndUSBPDevs

    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr) in s.subjects.usbpdevs
        // Requirements needed by the following requirements
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_info_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: usbpdev_valid_slot_id(i)
                ==> usbpdev_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
        // Requirement: The condition when OS_Activate_AllReleasedPEHCIsAndUSBPDevs returns true

    requires new_pid == PID_RESERVED_OS_PARTITION

    ensures var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            forall id :: id in pehci_ids ==> WSM_IsOSDevID(s.subjects, id)
    ensures var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            forall id :: id in usbpdev_ids ==> WSM_IsUSBPDevID(s.subjects, id)

    ensures var pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
            var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            var dev_ids := pehci_ids + usbpdev_ids;
            P_WSD_DevActivate_Multi_ConditionForReturnTrue(dm, dev_ids, pid)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
    var dev_ids := pehci_ids + usbpdev_ids;

    assert pid == dm.red_pid;
    assert pid in dm.pids;

    // Prove all eEHCIs and USBPDevs are inactive
    Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_PEHCISAndEEHCIsAndUSBPDevsAreInactive(s, dm, new_pid);
    assert forall id :: id in dev_ids
                ==> DM_SubjPID(dm.subjects, id.sid) == NULL;

    Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_DevsCanActiveInRed(s, dm, new_pid);
    assert (pid == dm.red_pid 
                ==> (forall id :: id in dev_ids
                        ==> TryActivateDevInRed(dm, id)) 
            ) &&
            (pid != dm.red_pid 
                ==> (forall id :: id in dev_ids
                        ==> TryActivateDevInGreen(dm, id)) 
            );

    Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_HCodedTDsDoNotDefineWriteToTDs(s, dm, new_pid);
    assert (forall dev_id, hcoded_td_id, td_id :: dev_id in dev_ids &&
                    hcoded_td_id == dm.subjects.devs[dev_id].hcoded_td_id &&
                    td_id in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
                ==> W !in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds[td_id].amodes
            );

    Lemma_P_WSD_DevActivate_Multi_ConditionForReturnTrue_Prove(dm, dev_ids, pid);
}

lemma Lemma_OS_Activate_MainMem_ByPAddr_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    paddr_start:word, paddr_end:word, 
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WK_ValidPMemRegion(paddr_start, paddr_end)
        // Properties specific to OS_Activate_MainMem_ByPAddr
    requires state_equal_except_mstate_subjs_objs_memactivemap(s, s')
    requires ffi_pmem_activate_main_mem_in_os_stack_and_statevars_inner(s, paddr_start, paddr_end, TRUE, s'.subjects, s'.objects, s'.os_mem_active_map)
        // Requirement: OS_Activate_MainMem_ByPAddr modifies global variables correctly
        // Relationship between s and s'

    ensures var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
            var td_ids := result.1;
            var fd_ids := result.2;
            var do_ids := result.3; 
            DM_ExternalObjsActivateToRedPartition_PreConditions(dm, td_ids, fd_ids, do_ids)
    ensures var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
            var td_ids:set<TD_ID> := result.1;
            var fd_ids:set<FD_ID> := result.2;
            var do_ids:set<DO_ID> := result.3; 
            (forall td_id :: td_id in td_ids ==> DM_ObjPID(dm.objects, td_id.oid) == NULL) &&
           (forall fd_id :: fd_id in fd_ids ==> DM_ObjPID(dm.objects, fd_id.oid) == NULL) &&
           (forall do_id :: do_id in do_ids ==> DM_ObjPID(dm.objects, do_id.oid) == NULL)
{
    var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
    var td_ids := result.1;
    var fd_ids := result.2;
    var do_ids := result.3; 

    forall id | id in td_ids
        ensures id in AllTDIDs(dm.objects)
        ensures DM_ObjPID(dm.objects, id.oid) == NULL
    {
        assert id in WSM_AllTDIDs(s.objects);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    }

    forall id | id in fd_ids
        ensures id in AllFDIDs(dm.objects)
        ensures DM_ObjPID(dm.objects, id.oid) == NULL
    {
        assert id in WSM_AllFDIDs(s.objects);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    }

    forall id | id in do_ids
        ensures id in AllDOIDs(dm.objects)
        ensures DM_ObjPID(dm.objects, id.oid) == NULL
    {
        assert id in WSM_AllDOIDs(s.objects);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    }
    
    forall s_id, o_id | s_id in DM_AllSubjsIDs(dm.subjects) &&
                o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
        ensures !DM_DoOwnObj(dm.subjects, s_id, o_id)
    {
        assert s_id in WSM_AllSubjsIDs(s.subjects);
        assert !WSM_DoOwnObj(s.subjects, s_id, o_id);

        Lemma_WSMStateMapping_EquivilantObjOwnership(s, dm);
        assert !DM_DoOwnObj(dm.subjects, s_id, o_id);
    }
}

lemma Lemma_OS_Deactivate_MainMem_ByPAddr_ProveCommutativeDiagram_ProveMappingOfOpsCondition(
    s:state, dm:DM_State, 
    paddr_start:word, paddr_end:word, 
    s':state
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WK_ValidPMemRegion(paddr_start, paddr_end)
    requires P_OS_Deactivate_MainMem_ByPAddr_AdditonalPreConditions(s, dm, paddr_start, paddr_end)
        // Properties specific to OS_Activate_MainMem_ByPAddr
    requires state_equal_except_mstate_subjs_objs_memactivemap(s, s')
    requires ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars_inner(s, paddr_start, paddr_end, s'.subjects, s'.objects, s'.os_mem_active_map)
        // Requirement: OS_Activate_MainMem_ByPAddr modifies global variables correctly
        // Relationship between s and s'

    ensures var result := os_external_objs_to_be_deactivated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
            var td_ids := result.1;
            var fd_ids := result.2;
            var do_ids := result.3; 
            DM_RedExternalObjsDeactivate_PreConditions(dm, td_ids, fd_ids, do_ids)
{
    var result := os_external_objs_to_be_deactivated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
    var td_ids := result.1;
    var fd_ids := result.2;
    var do_ids := result.3; 

    forall id | id in td_ids
        ensures id in AllTDIDs(dm.objects)
        ensures DM_ObjPID(dm.objects, id.oid) == dm.red_pid
    {
        assert id in WSM_AllTDIDs(s.objects);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    }

    forall id | id in fd_ids
        ensures id in AllFDIDs(dm.objects)
        ensures DM_ObjPID(dm.objects, id.oid) == dm.red_pid
    {
        assert id in WSM_AllFDIDs(s.objects);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    }

    forall id | id in do_ids
        ensures id in AllDOIDs(dm.objects)
        ensures DM_ObjPID(dm.objects, id.oid) == dm.red_pid
    {
        assert id in WSM_AllDOIDs(s.objects);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    }
    
    forall s_id, o_id | s_id in DM_AllSubjsIDs(dm.subjects) &&
                o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
        ensures !DM_DoOwnObj(dm.subjects, s_id, o_id)
    {
        assert s_id in WSM_AllSubjsIDs(s.subjects);
        assert !WSM_DoOwnObj(s.subjects, s_id, o_id);

        Lemma_WSMStateMapping_EquivilantObjOwnership(s, dm);
        assert !DM_DoOwnObj(dm.subjects, s_id, o_id);
    }
}




/*********************** Private Functions/Lemmas of Private Lemmas ********************/
// Function: Convert wimp driver's read to USB TD Reg to abstract objects
function F_WimpDrvReadEEHCIUSBTDReg_MapReadingAbstractObjsVals(
    s:state, eehci_slot:word, usbtd_reg_slot:word
) : (result:set<TD_ID>)
    requires ValidState(s)

    requires eehci_valid_slot_id(eehci_slot)

    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis

    requires 0 <= usbtd_reg_slot < eEHCI_USBTD_SlotID_NUMS

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            (forall id :: id in result
                ==> id in s.subjects.eehcis[eehci_id].td_ids)
    ensures forall id :: id in result 
                ==> id !in WSM_AllHCodedTDIDs(s.subjects)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
    var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
    
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_eEHCIs();

    var offset := G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_slot * ARCH_WORD_BYTES;
    var id := s.subjects.eehcis[eehci_id].map_td_ids[offset];

    // Prove id !in WSM_AllHCodedTDIDs(s.subjects)
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_eEHCIs();
    assert id in s.objects.eehci_other_tds;

    Lemma_WSM_AllHCodedTDIDs_NotInEEHCIOtherTDs(s);
    assert id !in WSM_AllHCodedTDIDs(s.subjects);

    {id}
}

// Function: Convert wimp driver's read to FD and DO to abstract objects
function F_WimpDrvReadEEHCIFDDO_MapReadingAbstractObjsVals(
    s:state, eehci_slot:word, reg_offset:word
) : (result:(set<FD_ID>, set<DO_ID>))
    requires ValidState(s)

    requires eehci_valid_slot_id(eehci_slot)

    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis

    requires reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || 
             reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            (forall id :: id in result.0
                ==> id in s.subjects.eehcis[eehci_id].fd_ids) &&
            (forall id :: id in result.1
                ==> id in s.subjects.eehcis[eehci_id].do_ids)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
    var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
    
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_eEHCIs();
    if(reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset) then
        var id := s.subjects.eehcis[eehci_id].map_fd_ids[reg_offset];

        ({id}, {})
    else
        var id := s.subjects.eehcis[eehci_id].map_do_ids[reg_offset];

        ({}, {id})
}

// Function: Convert wimp driver's write to FD and DO to abstract objects and values
function F_WimpDrvWriteEEHCIFDDO_MapWritingAbstractObjsVals(
    s:state, eehci_slot:word, reg_offset:word, new_v:word
) : (result:(map<FD_ID, FD_Val>, map<DO_ID, DO_Val>))
    requires ValidState(s)

    requires eehci_valid_slot_id(eehci_slot)

    requires var globals := wkm_get_globals(s.wk_mstate);
             var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            eehci_id in s.subjects.eehcis

    requires reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || 
             reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
            var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
            (forall id :: id in result.0
                ==> id in s.subjects.eehcis[eehci_id].fd_ids) &&
            (forall id :: id in result.1
                ==> id in s.subjects.eehcis[eehci_id].do_ids)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
    var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
    var new_str := DevWrite_WordToString(new_v);
    
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_eEHCIs();
    if(reg_offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset) then
        var id := s.subjects.eehcis[eehci_id].map_fd_ids[reg_offset];
        var m:map<FD_ID, FD_Val> := map[id := FD_Val(new_str)];

        (m, map[])
    else
        var id := s.subjects.eehcis[eehci_id].map_do_ids[reg_offset];
        var m:map<DO_ID, DO_Val> := map[id := DO_Val(new_str)];

        (map[], m)
}

lemma Lemma_WK_EmptyPartitionDestroy_ProveCommutativeDiagram_ProveMappingOfOpsCondition_SubjPIDs(
    s:state, dm:DM_State, 
    pid:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires pid != PID_INVALID
    requires pid != PID_RESERVED_OS_PARTITION
    requires var globals := wkm_get_globals(s.wk_mstate);
             (forall i :: eehci_valid_slot_id(i)
                    ==> eehci_info_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: usbpdev_valid_slot_id(i)
                    ==> usbpdev_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: usbtd_map_valid_slot_id(i)
                    ==> usbtd_map_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: wimpdrv_valid_slot_id(i)
                    ==> wimpdrv_get_pid(globals, i) != WS_PartitionID(pid))
        // Requirement: The condition when WK_EmptyPartitionDestroy returns true

    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(pid));
            forall s_id :: s_id in DM_AllSubjsIDs(dm.subjects) ==> DM_SubjPID(dm.subjects, s_id) != dm_pid
{
    var globals := wkm_get_globals(s.wk_mstate);

    reveal WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
    forall s_id | s_id in WSM_AllSubjsIDs(s.subjects)
        ensures WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) != WS_PartitionID(pid)
    {
        if(Drv_ID(s_id) in s.subjects.os_drvs)
        {
            assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) != WS_PartitionID(pid);
        }
        else if (Dev_ID(s_id) in s.subjects.os_devs)
        {
            assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) != WS_PartitionID(pid);
        }
        else if (WSM_IsWimpDrvID(s.subjects, Drv_ID(s_id)))
        {
            assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) != WS_PartitionID(pid);
        }
        else if (WSM_IsUSBPDevID(s.subjects, Dev_ID(s_id)))
        {
            assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) != WS_PartitionID(pid);
        }
        else
        {
            assert WSM_IsEEHCIDevID(s.subjects, Dev_ID(s_id));
            assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) != WS_PartitionID(pid);
        }
    }

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
}

lemma Lemma_WK_EmptyPartitionDestroy_ProveCommutativeDiagram_ProveMappingOfOpsCondition_ObjPIDs(
    s:state, dm:DM_State, 
    pid:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires pid != PID_INVALID
    requires pid != PID_RESERVED_OS_PARTITION
    requires var globals := wkm_get_globals(s.wk_mstate);
             (forall i :: eehci_valid_slot_id(i)
                    ==> eehci_info_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: usbpdev_valid_slot_id(i)
                    ==> usbpdev_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: usbtd_map_valid_slot_id(i)
                    ==> usbtd_map_get_pid(globals, i) != WS_PartitionID(pid)) &&
             (forall i :: wimpdrv_valid_slot_id(i)
                    ==> wimpdrv_get_pid(globals, i) != WS_PartitionID(pid))
        // Requirement: The condition when WK_EmptyPartitionDestroy returns true

    ensures var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(pid));
            forall o_id :: o_id in DM_AllObjsIDs(dm.objects) ==> DM_ObjPID(dm.objects, o_id) != dm_pid
{
    var globals := wkm_get_globals(s.wk_mstate);
    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s);
    reveal WK_ValidObjs(); 

    reveal WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
    forall o_id | o_id in WSM_AllObjIDs(s.objects)
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, o_id) != WS_PartitionID(pid)
    {
        if(TD_ID(o_id) in WSM_AllTDIDs(s.objects))
        {
            assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, o_id) != WS_PartitionID(pid);
        }
        else if(FD_ID(o_id) in WSM_AllFDIDs(s.objects))
        {
            assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, o_id) != WS_PartitionID(pid);
        }
        else
        {
            assert DO_ID(o_id) in WSM_AllDOIDs(s.objects);
            assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, o_id) != WS_PartitionID(pid);
        }
    }

    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
}

// [NOTE] Needs 40s to verify
lemma Lemma_USBPDev_CanBeActivatedInRedOrGreen(s:state, dm:DM_State, usbpdev_id:Dev_ID)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires usbpdev_id in s.subjects.usbpdevs

    ensures TryActivateDevInRed(dm, usbpdev_id)
    ensures TryActivateDevInGreen(dm, usbpdev_id)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidState_DevsActivateCond(); 
}

lemma Lemma_EEHCI_CanBeActivatedInGreen(s:state, dm:DM_State, eehci_id:Dev_ID)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)

    requires eehci_id in s.subjects.eehcis

    ensures TryActivateDevInGreen(dm, eehci_id)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidState_DevsActivateCond();

    reveal WSM_physical_EHCIs_must_be_inactive();
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
}

lemma Lemma_WimpDrv_AccessEEHCIObjs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property3(
    s:state, dm:DM_State, 
    wimpdrv_id:Drv_ID, eehci_id:Dev_ID, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires wimpdrv_id in s.subjects.wimp_drvs
    requires eehci_id in s.subjects.eehcis

    requires var globals := wkm_get_globals(s.wk_mstate);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid) ==
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid)

    requires (forall id :: id in td_ids ==> id in s.subjects.eehcis[eehci_id].td_ids) &&
            (forall id :: id in fd_ids ==> id in s.subjects.eehcis[eehci_id].fd_ids) &&
            (forall id :: id in do_ids ==> id in s.subjects.eehcis[eehci_id].do_ids) &&
            (forall id :: id in td_ids ==> id !in WSM_AllHCodedTDIDs(s.subjects))

    requires (forall td_id :: td_id in td_ids ==> td_id in AllTDIDs(dm.objects)) &&
            (forall fd_id :: fd_id in fd_ids ==> fd_id in AllFDIDs(dm.objects)) &&
            (forall do_id :: do_id in do_ids ==> do_id in AllDOIDs(dm.objects))

    ensures DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
    ensures WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var eehci_pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid);

    forall id | id in td_ids
        ensures eehci_pid == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        ensures DM_SubjPID(dm.subjects, eehci_id.sid) == DM_ObjPID(dm.objects, id.oid)
    {
        Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid, id.oid);

        Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        assert DM_SubjPID(dm.subjects, eehci_id.sid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert DM_ObjPID(dm.objects, id.oid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
    }

    forall id | id in fd_ids
        ensures eehci_pid == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        ensures DM_SubjPID(dm.subjects, eehci_id.sid) == DM_ObjPID(dm.objects, id.oid)
    {
        Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid, id.oid);

        Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        assert DM_SubjPID(dm.subjects, eehci_id.sid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert DM_ObjPID(dm.objects, id.oid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
    }

    forall id | id in do_ids
        ensures eehci_pid == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        ensures DM_SubjPID(dm.subjects, eehci_id.sid) == DM_ObjPID(dm.objects, id.oid)
    {
        Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid, id.oid);

        Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        assert DM_SubjPID(dm.subjects, eehci_id.sid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert DM_ObjPID(dm.objects, id.oid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
    }
}

lemma Lemma_DM_GreenDrvWrite_ChkNewValsOfTDs_ReturnTrueOnEmpty(ws:DM_State)
    requires DM_IsValidState_Subjects(ws) && DM_IsValidState_Objects(ws)
    
    ensures DM_GreenDrvWrite_ChkNewValsOfTDs(ws, map[])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrv_AccessEEHCIUSBTDRegs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property3(
    s:state, dm:DM_State, 
    wimpdrv_id:Drv_ID, eehci_id:Dev_ID, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires wimpdrv_id in s.subjects.wimp_drvs
    requires eehci_id in s.subjects.eehcis

    requires var globals := wkm_get_globals(s.wk_mstate);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid) ==
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid)

    requires (forall td_id :: td_id in td_ids ==> td_id in AllTDIDs(dm.objects)) &&
            (forall fd_id :: fd_id in fd_ids ==> fd_id in AllFDIDs(dm.objects)) &&
            (forall do_id :: do_id in do_ids ==> do_id in AllDOIDs(dm.objects))

    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in td_ids
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in fd_ids
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall id :: id in do_ids
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid)

    ensures DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var eehci_pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid);

    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s);
    reveal WK_ValidObjs_ObjIDs();
    forall id | id in td_ids
        ensures eehci_pid == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        ensures DM_SubjPID(dm.subjects, eehci_id.sid) == DM_ObjPID(dm.objects, id.oid)
    {
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == eehci_pid;

        Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        assert DM_SubjPID(dm.subjects, eehci_id.sid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert DM_ObjPID(dm.objects, id.oid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
    }

    forall id | id in fd_ids
        ensures eehci_pid == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        ensures DM_SubjPID(dm.subjects, eehci_id.sid) == DM_ObjPID(dm.objects, id.oid)
    {
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == eehci_pid;

        Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        assert DM_SubjPID(dm.subjects, eehci_id.sid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert DM_ObjPID(dm.objects, id.oid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
    }

    forall id | id in do_ids
        ensures eehci_pid == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        ensures DM_SubjPID(dm.subjects, eehci_id.sid) == DM_ObjPID(dm.objects, id.oid)
    {
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == eehci_pid;

        Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        assert DM_SubjPID(dm.subjects, eehci_id.sid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert DM_ObjPID(dm.objects, id.oid) == WSM_MapWSParititonID_ToAbstractPartitionID(eehci_pid);
    }
}

lemma Lemma_WimpDrv_ReadObjsAreInSamePartition(
    dm:DM_State, wimpdrv_id:Drv_ID,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires P_DMSubjectsHasUniqueIDs(dm.subjects)
    requires P_DMObjectsHasUniqueIDs(dm.objects)
    
    requires DM_IsDrvID(dm.subjects, wimpdrv_id)

    requires (forall td_id :: td_id in td_ids ==> td_id in AllTDIDs(dm.objects)) &&
             (forall fd_id :: fd_id in fd_ids ==> fd_id in AllFDIDs(dm.objects)) &&
             (forall do_id :: do_id in do_ids ==> do_id in AllDOIDs(dm.objects))
        // Requirement: Driver only write existing objects

    requires DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, wimpdrv_id.sid, td_ids, fd_ids, do_ids) 

    ensures var read_objs := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
            forall o_id :: o_id in read_objs ==> 
                DM_SubjPID(dm.subjects, wimpdrv_id.sid) == DM_ObjPID(dm.objects, o_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_USBTD_Allocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property4(
    s:state, dm:DM_State, 
    usbtd_idword:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires usbtd_idword != USBTD_ID_INVALID
    requires usbtd_idword in s.id_mappings.usbtd_to_td
    requires usbtd_idword in s.id_mappings.usbtd_to_fd
    requires usbtd_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:uint32 :: usbtd_map_valid_slot_id(i) &&
                    usbtd_map_get_idword(globals, i) != USBTD_ID_INVALID
                ==> usbtd_map_get_idword(globals, i) != usbtd_idword
        // Requirement: <usbtd_idword> is not registered yet

    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in s.objects.usbtd_tds &&
            usbtd_fd_id in s.objects.usbtd_fds &&
            usbtd_do_id in s.objects.usbtd_dos
        // Requirement: Mapped TDs/FDs/DOs must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in AllTDIDs(dm.objects) &&
            usbtd_fd_id in AllFDIDs(dm.objects) &&
            usbtd_do_id in AllDOIDs(dm.objects)

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            DM_ObjPID(dm.objects, usbtd_td_id.oid) == NULL &&
            DM_ObjPID(dm.objects, usbtd_fd_id.oid) == NULL &&
            DM_ObjPID(dm.objects, usbtd_do_id.oid) == NULL
{
    var globals := wkm_get_globals(s.wk_mstate);
    var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
    var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
    var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];

    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s);

    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedTD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_td_id);
    Lemma_ObjPID_UnRegisteredUSBTD_ObjPIDEqualsToInvalid(s.subjects, s.objects, s.id_mappings, globals, usbtd_idword, usbtd_td_id.oid);

    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedFD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_fd_id);
    Lemma_ObjPID_UnRegisteredUSBTD_ObjPIDEqualsToInvalid(s.subjects, s.objects, s.id_mappings, globals, usbtd_idword, usbtd_fd_id.oid);

    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedDO(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_do_id);
    Lemma_ObjPID_UnRegisteredUSBTD_ObjPIDEqualsToInvalid(s.subjects, s.objects, s.id_mappings, globals, usbtd_idword, usbtd_do_id.oid);

    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_td_id.oid)) == DM_ObjPID(dm.objects, usbtd_td_id.oid);
    assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_fd_id.oid)) == DM_ObjPID(dm.objects, usbtd_fd_id.oid);
    assert WSM_MapWSParititonID_ToAbstractPartitionID(WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_do_id.oid)) == DM_ObjPID(dm.objects, usbtd_do_id.oid);
}

lemma Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property3(
    s:state, dm:DM_State, 
    td_slot:word, pid:WS_PartitionID
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires usbtd_map_valid_slot_id(td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            usbtd_idword != USBTD_ID_INVALID &&
            usbtd_idword in s.id_mappings.usbtd_to_td &&
            usbtd_idword in s.id_mappings.usbtd_to_fd &&
            usbtd_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, usbtd_map_get_pid(globals, td_slot).v)
        // Requirement: The condition when USBTD_slot_allocate_1slot returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in s.objects.usbtd_tds &&
            usbtd_fd_id in s.objects.usbtd_fds &&
            usbtd_do_id in s.objects.usbtd_dos
        // Requirement: Mapped TDs/FDs/DOs must exist in the system

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            forall s_id, o_id :: s_id in DM_AllSubjsIDs(dm.subjects) &&
                    o_id in (TDIDsToObjIDs({usbtd_td_id}) + FDIDsToObjIDs({usbtd_fd_id}) + DOIDsToObjIDs({usbtd_do_id}))
                ==> !DM_DoOwnObj(dm.subjects, s_id, o_id)
        // Property 3: usbtd_* must be external objects
{
    var globals := wkm_get_globals(s.wk_mstate);
    var dm_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(pid);
    var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
    var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
    var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
    var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_USBTDsAreExternalObjs(s);
    forall s_id, o_id | s_id in DM_AllSubjsIDs(dm.subjects) &&
                    o_id in (TDIDsToObjIDs({usbtd_td_id}) + FDIDsToObjIDs({usbtd_fd_id}) + DOIDsToObjIDs({usbtd_do_id}))
        ensures !DM_DoOwnObj(dm.subjects, s_id, o_id)
    {
        Lemma_TDFDDOIDsToObjIDs_Sum_Property(usbtd_td_id, usbtd_fd_id, usbtd_do_id, o_id);
        assert TD_ID(o_id) == usbtd_td_id || FD_ID(o_id) == usbtd_fd_id || DO_ID(o_id) == usbtd_do_id;

        assert !WSM_DoOwnObj(s.subjects, s_id, o_id);
        Lemma_WSMStateMapping_EquivilantObjOwnership(s, dm);
        assert !DM_DoOwnObj(dm.subjects, s_id, o_id);
    }
}

lemma Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram_ProveMappingOfOpsCondition_PreConditions(s:state, dm:DM_State, td_slot:word)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires usbtd_map_valid_slot_id(td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            usbtd_idword != USBTD_ID_INVALID &&
            usbtd_idword in s.id_mappings.usbtd_to_td &&
            usbtd_idword in s.id_mappings.usbtd_to_fd &&
            usbtd_idword in s.id_mappings.usbtd_to_do
        // Properties needed by the following requirement
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, usbtd_map_get_pid(globals, td_slot).v)
        // Requirement: The condition when USBTD_slot_allocate_1slot returns true

    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in s.objects.usbtd_tds &&
            usbtd_fd_id in s.objects.usbtd_fds &&
            usbtd_do_id in s.objects.usbtd_dos
        // Requirement: Mapped TDs/FDs/DOs must exist in the system

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var pid := usbtd_map_get_pid(globals, td_slot);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_td_id.oid) == pid &&
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_fd_id.oid) == pid &&
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_do_id.oid) == pid
        // Requirement: Mapped TDs/FDs/DOs are in the partition <pid>
{
    var globals := wkm_get_globals(s.wk_mstate);
    var pid := usbtd_map_get_pid(globals, td_slot);
    var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
    var usbtd_td_id:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
    var usbtd_fd_id:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
    var usbtd_do_id:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];

    // Prove property 1
    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedTD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_td_id);
    Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, td_slot, usbtd_td_id.oid);

    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedFD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_fd_id);
    Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, td_slot, usbtd_fd_id.oid);

    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedDO(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_do_id);
    Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, td_slot, usbtd_do_id.oid);
}

lemma Lemma_WimpDrv_SubmitUSBTD_ProveCommutativeDiagram_ProveMappingOfOpsCondition_Property3(
    s:state, dm:DM_State, 
    wimpdrv_id:Drv_ID, td_slot:word, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires wimpdrv_id in s.subjects.wimp_drvs
    requires usbtd_map_valid_slot_id(td_slot)

    requires var globals := wkm_get_globals(s.wk_mstate);
             var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
             usbtd_idword != USBTD_ID_INVALID

    requires var globals := wkm_get_globals(s.wk_mstate);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid) == usbtd_map_get_pid(globals, td_slot)

    requires (forall id :: id in td_ids ==> id in s.objects.usbtd_tds) &&
            (forall id :: id in fd_ids ==> id in s.objects.usbtd_fds) &&
            (forall id :: id in do_ids ==> id in s.objects.usbtd_dos) &&
            (forall id :: id in td_ids ==> id !in WSM_AllHCodedTDIDs(s.subjects))
        // Requirement: Objects to be accessed must be usbtd_*
    requires var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            (forall id :: id in td_ids
                ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
            (forall id :: id in fd_ids
                ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword) &&
            (forall id :: id in do_ids
                ==> USBTDMappedObj_IDToUSBTDIDWord(s.subjects, s.objects, s.id_mappings, id.oid) == usbtd_idword)
        // Property: The objects in the result all maps to the USB TD <usbtd_idword> at the slot <new_v>

    requires (forall td_id :: td_id in td_ids ==> td_id in AllTDIDs(dm.objects)) &&
            (forall fd_id :: fd_id in fd_ids ==> fd_id in AllFDIDs(dm.objects)) &&
            (forall do_id :: do_id in do_ids ==> do_id in AllDOIDs(dm.objects))

    ensures DM_DrvDevRead_ChkSubjAndObjsAreInSamePartition(dm, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
    ensures WS_WimpDrvAccess_ChkDrvAndObjsAreInSamePartition(s, wimpdrv_id.sid, td_ids, fd_ids, do_ids)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid);
    assert wimpdrv_pid == usbtd_map_get_pid(globals, td_slot);

    Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord_TDsFDsDOs(s.subjects, s.objects, s.id_mappings, globals, td_slot, td_ids, fd_ids, do_ids);

    forall id | id in td_ids
        ensures wimpdrv_pid == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        ensures DM_SubjPID(dm.subjects, wimpdrv_id.sid) == DM_ObjPID(dm.objects, id.oid)
    {
        Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        assert DM_SubjPID(dm.subjects, wimpdrv_id.sid) == WSM_MapWSParititonID_ToAbstractPartitionID(wimpdrv_pid);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert DM_ObjPID(dm.objects, id.oid) == WSM_MapWSParititonID_ToAbstractPartitionID(wimpdrv_pid);
    }

    forall id | id in fd_ids
        ensures wimpdrv_pid == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        ensures DM_SubjPID(dm.subjects, wimpdrv_id.sid) == DM_ObjPID(dm.objects, id.oid)
    {
        Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        assert DM_SubjPID(dm.subjects, wimpdrv_id.sid) == WSM_MapWSParititonID_ToAbstractPartitionID(wimpdrv_pid);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert DM_ObjPID(dm.objects, id.oid) == WSM_MapWSParititonID_ToAbstractPartitionID(wimpdrv_pid);
    }

    forall id | id in do_ids
        ensures wimpdrv_pid == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        ensures DM_SubjPID(dm.subjects, wimpdrv_id.sid) == DM_ObjPID(dm.objects, id.oid)
    {
        Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        assert DM_SubjPID(dm.subjects, wimpdrv_id.sid) == WSM_MapWSParititonID_ToAbstractPartitionID(wimpdrv_pid);
        Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
        assert DM_ObjPID(dm.objects, id.oid) == WSM_MapWSParititonID_ToAbstractPartitionID(wimpdrv_pid);
    }
}

lemma Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_PEHCISAndEEHCIsAndUSBPDevsAreInactive(
    s:state, dm:DM_State, 
    new_pid:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
    requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)
        // Properties specific to OS_Activate_AllReleasedPEHCIsAndUSBPDevs

    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr) in s.subjects.usbpdevs
        // Requirements needed by the following requirements
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_info_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: usbpdev_valid_slot_id(i)
                ==> usbpdev_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
        // Requirement: The condition when OS_Activate_AllReleasedPEHCIsAndUSBPDevs returns true

    ensures var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            forall id :: id in pehci_ids ==> WSM_IsOSDevID(s.subjects, id)
    ensures var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            forall id :: id in usbpdev_ids ==> WSM_IsUSBPDevID(s.subjects, id)
        // Property 1:
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_ids:set<Dev_ID> := MapGetKeys(s.subjects.eehcis);
            forall id :: id in eehci_ids
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            forall id :: id in pehci_ids
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            forall id :: id in usbpdev_ids
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID)
        // Property 2:
    ensures var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            var dev_ids := pehci_ids + usbpdev_ids;
            forall id :: id in dev_ids
                ==> DM_SubjPID(dm.subjects, id.sid) == NULL
    ensures var eehci_ids:set<Dev_ID> := MapGetKeys(s.subjects.eehcis);
            forall id :: id in eehci_ids
                ==> DM_SubjPID(dm.subjects, id.sid) == NULL
{
    var globals := wkm_get_globals(s.wk_mstate);
    var pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    var eehci_ids:set<Dev_ID> := MapGetKeys(s.subjects.eehcis);
    var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);

    // Prove all pEHCIs, eEHCIs and USBPDevs are inactive
    reveal WSM_physical_EHCIs_must_be_inactive();

    forall id | id in eehci_ids
        ensures WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID)
    {
        var eehci_idword:word := EEHCI_DevID_ToIDWord(s.subjects, s.objects, s.id_mappings, id);
        if(eehci_idword_in_record(globals, eehci_idword))
        {
            var eehci_slot := eehci_get_slot_by_idword(globals, eehci_idword);
            Lemma_SubjPID_RegisteredEEHCI_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, eehci_slot, id.sid);
        }
        else
        {
            reveal WK_ValidSubjs();
            reveal WK_ValidSubjs_SubjIDs();

            assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID);
        }
    }

    forall id | id in usbpdev_ids
        ensures WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID)
    {
        var usbpdev_addr:USBPDev_Addr := USBPDev_DevID_ToAddr(s.subjects, s.objects, s.id_mappings, id);
        if(usbpdev_addr_in_record(globals, usbpdev_addr))
        {
            var usbpdev_slot := usbpdev_get_slot_by_addr(globals, usbpdev_addr);
            Lemma_SubjPID_RegisteredUSBPDev_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, usbpdev_slot, id.sid);
        }
        else
        {
            reveal WK_ValidSubjs();
            reveal WK_ValidSubjs_SubjIDs();

            var pid := WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, id.sid);
            assert pid == SubjPID_USBPDev_ByAddr(s.subjects, s.objects, s.id_mappings, globals, usbpdev_addr);
            assert WSM_IsUSBPDevID(s.subjects, id);
            assert s.subjects.usbpdevs[id].active_in_os == false;
            assert !usbpdev_addr_in_record(globals, usbpdev_addr);
            assert pid == WS_PartitionID(PID_INVALID);

            assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID);
        }
    }

    // Prove property 3
    var dev_ids := pehci_ids + usbpdev_ids;
    forall dev_id | dev_id in dev_ids
        ensures DM_SubjPID(dm.subjects, dev_id.sid) == NULL
    {
        if(dev_id in pehci_ids)
        {
            Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        }
        else
        {
            assert dev_id in usbpdev_ids;
            Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
        }
    }
}

lemma Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_HCodedTDsDoNotDefineWriteToTDs(
    s:state, dm:DM_State, 
    new_pid:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
    requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)
        // Properties specific to OS_Activate_AllReleasedPEHCIsAndUSBPDevs

    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr) in s.subjects.usbpdevs
        // Requirements needed by the following requirements
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_info_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: usbpdev_valid_slot_id(i)
                ==> usbpdev_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
        // Requirement: The condition when OS_Activate_AllReleasedPEHCIsAndUSBPDevs returns true

    requires var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            forall id :: id in pehci_ids ==> WSM_IsOSDevID(s.subjects, id)
    requires var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            forall id :: id in usbpdev_ids ==> WSM_IsUSBPDevID(s.subjects, id)

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            var dev_ids := pehci_ids + usbpdev_ids; 
            forall dev_id, hcoded_td_id, td_id :: dev_id in dev_ids &&
                    hcoded_td_id == dm.subjects.devs[dev_id].hcoded_td_id &&
                    td_id in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
                ==> W !in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds[td_id].amodes
{
    var globals := wkm_get_globals(s.wk_mstate);
    var pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
    var dev_ids := pehci_ids + usbpdev_ids;

    forall dev_id, hcoded_td_id, td_id | dev_id in dev_ids &&
            hcoded_td_id == dm.subjects.devs[dev_id].hcoded_td_id &&
            td_id in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds
        ensures W !in dm.objects.hcoded_tds[hcoded_td_id].val.trans_params_tds[td_id].amodes
    {
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjInSubjsMustBeInState();
        
        if(dev_id in pehci_ids)
        {
            Lemma_PEHCI_HCodedTDDoNotDefineWriteTransferToTDs(s, dm, dev_id);
        }
        else
        {
            assert dev_id in usbpdev_ids;
            Lemma_USBPDev_HCodedTDDoNotDefineTransferToTDs(s, dev_id);
        }
    }
}

lemma Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveMappingOfOpsCondition_DevsCanActiveInRed(
    s:state, dm:DM_State, 
    new_pid:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
    requires WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds)
        // Properties specific to OS_Activate_AllReleasedPEHCIsAndUSBPDevs

    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
    requires var globals := wkm_get_globals(s.wk_mstate);
             var addrs := usbpdevlist_get_all_non_empty_addrs(globals);
             forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr) in s.subjects.usbpdevs
        // Requirements needed by the following requirements
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_info_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    requires var globals := wkm_get_globals(s.wk_mstate);
             forall i:word :: usbpdev_valid_slot_id(i)
                ==> usbpdev_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
        // Requirement: The condition when OS_Activate_AllReleasedPEHCIsAndUSBPDevs returns true

    requires var pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
             new_pid == PID_RESERVED_OS_PARTITION &&
             pid == dm.red_pid

    requires var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            forall id :: id in pehci_ids ==> WSM_IsOSDevID(s.subjects, id)
    requires var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            forall id :: id in usbpdev_ids ==> WSM_IsUSBPDevID(s.subjects, id)

    requires var eehci_ids:set<Dev_ID> := MapGetKeys(s.subjects.eehcis);
             forall id :: id in eehci_ids
                ==> DM_SubjPID(dm.subjects, id.sid) == NULL

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
            var dev_ids := pehci_ids + usbpdev_ids;
            forall id :: id in dev_ids
                ==> TryActivateDevInRed(dm, id)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidState_DevsActivateCond();

    var globals := wkm_get_globals(s.wk_mstate);
    var pehci_ids:set<Dev_ID> := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var usbpdev_ids:set<Dev_ID> := MapGetKeys(s.subjects.usbpdevs);
    var dev_ids := pehci_ids + usbpdev_ids;

    forall dev_id | dev_id in dev_ids
        ensures TryActivateDevInRed(dm, dev_id)
    {
        if(dev_id in pehci_ids)
        {
            assert TryActivateDevInRed(dm, dev_id);
        }
        else
        {
            assert dev_id in usbpdev_ids;
            assert TryActivateDevInRed(dm, dev_id);
        }
    }
}

lemma Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram_ProveP_WSD_DevActivate_Multi_SubjObjModifications(
    ws:DM_State, ws':DM_State, to_assign_dev_ids:seq<Dev_ID>, dev_ids:set<Dev_ID>
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires DM_IsValidState_Objects(ws)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    requires ws.red_pid != NULL

    requires SeqToSet(to_assign_dev_ids) == dev_ids
    requires P_WSD_DevActivate_Multi_SubjObjModifications(ws, ws', SeqToSet(to_assign_dev_ids), ws.red_pid)

    ensures P_WSD_DevActivate_Multi_SubjObjModifications(ws, ws', dev_ids, ws.red_pid)
{
    // Dafny can automatically prove this lemma
}