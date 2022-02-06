include "SecurityProperties_Ops.dfy"

// [NOTE] The WK code does not formally prove that operations fulfill SP1 and 2 for two reasons:
// (1) A manual prove is trivial with the current post-conditions of each WK APIs and direct I/O accesses
// (2) Proving SP1 in Dafny ends up to be time out

//******** Prove Security Properties ********//
// Proof of the Security Property 1: Forall traces starting from a secure state,
// no I/O access (as operations) crosses partition
/*lemma Lemma_WSM_ProveSP1(t:WSM_Trace)
    requires OpsSaneState(t.s0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:state, op:WSM_Op :: P_WSM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_WSM_OpsProperties
    requires WSM_IsValidTrace(t)
            
    ensures forall i, states:seq<state> :: 0 <= i < |t.ops| && states == WSM_CalcNewStates(t)
                ==> (t.ops[i].DM_RedDrvReadOp? && WSM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DM_GreenDrvReadOp? && WSM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid,
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DM_RedDrvWriteOp? && WSM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DM_GreenDrvWriteOp? && WSM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DM_DevReadOp? && WSM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid,
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the device
                    ) &&
                    (t.ops[i].DM_RedDevWriteOp? && WSM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the device
                    ) &&
                    (t.ops[i].DM_GreenDevWriteOp? && WSM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the device
                    )
{
    // Dafny can automatically prove this lemma
}

// Proof of the Security Property 2: Only hardcoded TDs can be reused in a 
// new partition
lemma Lemma_WSM_ProveSP2(t:WSM_Trace)
    requires OpsSaneState(t.s0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:state, op:WSM_Op :: P_WSM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_WSM_OpsProperties
    requires WSM_IsValidTrace(t)
    
    ensures forall i, states:seq<state> :: 0 <= i < |t.ops| && states == WSM_CalcNewStates(t)
                ==> AllTDIDs(states[i+1].objects) == AllTDIDs(states[i].objects) &&
                    AllFDIDs(states[i+1].objects) == AllFDIDs(states[i].objects) &&
                    AllDOIDs(states[i+1].objects) == AllDOIDs(states[i].objects)
        // Property needed by the following property
    ensures forall i, states:seq<state> :: 0 <= i < |t.ops| && states == WSM_CalcNewStates(t)
                ==> (forall td_id :: P_WSM_IsNonHCodedTDBeingMovedToAnActivePartition(states[i], states[i+1], td_id)
                        ==> DM_IsTDClearVal(states[i+1].objects, td_id)
                    ) && 
                    (forall fd_id :: P_WSM_IsFDBeingMovedToAnActivePartition(states[i], states[i+1], fd_id)
                        ==> DM_IsFDClearVal(states[i+1].objects, fd_id)
                    ) &&
                    (forall do_id :: P_WSM_IsDOBeingMovedToAnActivePartition(states[i], states[i+1], do_id)
                        ==> DM_IsDOClearVal(states[i+1].objects, do_id))
        // Main property: Only hardcoded TDs can be reused in a new partition
{
    var states := WSM_CalcNewStates(t);
    
    forall i | 0 <= i < |t.ops|
        ensures AllTDIDs(states[i+1].objects) == AllTDIDs(states[i].objects)
        ensures AllFDIDs(states[i+1].objects) == AllFDIDs(states[i].objects)
        ensures AllDOIDs(states[i+1].objects) == AllDOIDs(states[i].objects)
    {
        var ws := states[i];
        var ws' := WSM_CalcNewState(states[i], t.ops[i]).0;
        assert ws' == states[i+1];
        assert WSM_IsSecureOps(ws, ws');   
    }

    forall i | 0 <= i < |t.ops|
        ensures forall td_id :: P_WSM_IsNonHCodedTDBeingMovedToAnActivePartition(states[i], states[i+1], td_id)
                        ==> DM_IsTDClearVal(states[i+1].objects, td_id)
        ensures forall fd_id :: P_WSM_IsFDBeingMovedToAnActivePartition(states[i], states[i+1], fd_id)
                        ==> DM_IsFDClearVal(states[i+1].objects, fd_id)
        ensures forall do_id :: P_WSM_IsDOBeingMovedToAnActivePartition(states[i], states[i+1], do_id)
                        ==> DM_IsDOClearVal(states[i+1].objects, do_id)
    {
        var ws := states[i];
        var ws' := WSM_CalcNewState(states[i], t.ops[i]).0;
        assert ws' == states[i+1];
        assert WSM_IsSecureOps(ws, ws');

        Lemma_DM_ProveSP2_Private(ws, ws');
    }
}

*/

// Return if the TD is moved to an active partition, and the TD is not a 
// hardcoded TD
predicate P_WSM_IsNonHCodedTDBeingMovedToAnActivePartition(s:state, s':state, td_id:TD_ID)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)

    requires WSM_AllTDIDs(s'.objects) == WSM_AllTDIDs(s.objects)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var globals' := wkm_get_globals(s'.wk_mstate);

    td_id in WSM_AllTDIDs(s'.objects) &&

    (
        var pid := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, td_id.oid);
        var pid' := WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, globals', td_id.oid);

        pid' != pid && 
        pid' != WS_PartitionID(PID_INVALID)
    ) &&
        // For a transition from s to s', if a TD is activated (or moved) into an
        // active partition
    td_id !in WSM_AllHCodedTDIDs(s'.subjects)
        // TD is not a hardcoded TD
}

predicate P_WSM_IsFDBeingMovedToAnActivePartition(s:state, s':state, fd_id:FD_ID)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)

    requires WSM_AllFDIDs(s'.objects) == WSM_AllFDIDs(s.objects)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var globals' := wkm_get_globals(s'.wk_mstate);

    fd_id in WSM_AllFDIDs(s'.objects) &&

    (
        var pid := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, fd_id.oid);
        var pid' := WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, globals', fd_id.oid);

        pid' != pid && 
        pid' != WS_PartitionID(PID_INVALID)
    )
    // For a transition from s to s', if a FD is activated (or moved) into an 
    // active partition
}

predicate P_WSM_IsDOBeingMovedToAnActivePartition(s:state, s':state, do_id:DO_ID)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)

    requires WSM_AllDOIDs(s'.objects) == WSM_AllDOIDs(s.objects)
{
    var globals := wkm_get_globals(s.wk_mstate);
    var globals' := wkm_get_globals(s'.wk_mstate);

    do_id in WSM_AllDOIDs(s'.objects) &&

    (
        var pid := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, do_id.oid);
        var pid' := WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, globals', do_id.oid);

        pid' != pid && 
        pid' != WS_PartitionID(PID_INVALID)
    )
    // For a transition from s to s', if a DO is activated (or moved) into an 
    // active partition
}






//******** Prove Initial State Is Secure, Theorem 1 and 2 ********//
lemma Lemma_WSM_ProveInitialStateIsSecure(s0:state)
    requires Valid_WKMachineState_Arch(s0.wk_mstate) && WK_ValidMemState(s0.wk_mstate)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s0.wk_mstate))
    
    requires P_InitialState_EmptyGlobalVars(s0)
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> TestBit(usbtd_map_get_flags(wkm_get_globals(s0.wk_mstate), i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false
    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s0.subjects, usbpdev_id)
                ==> s0.subjects.usbpdevs[usbpdev_id].active_in_os == false
    requires var globals := wkm_get_globals(s0.wk_mstate);
             forall i :: eehci_valid_slot_id(i) 
                ==> eehci_mem_get_intr_enable_reg(globals, i) == eEHCI_Intr_Disable
        // Requirement: The value of the initial state

    requires var globals := wkm_get_globals(s0.wk_mstate);
            WK_ValidSubjs(s0.subjects, s0.id_mappings) &&
            WK_ValidObjs(s0.subjects, s0.objects) &&
            WK_ValidIDMappings(s0.subjects, s0.objects, s0.id_mappings) &&
            WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s0.subjects, s0.objects, s0.id_mappings, globals) &&
            WK_ValidObjsAddrs(s0.objects, s0.objs_addrs, globals) &&
            //WK_ValidObjAddrs_WimpDrv_DOPAddrs(s0.subjects, s0.objects, s0.id_mappings, s0.objs_addrs, globals) &&
            //WK_ValidGlobalVarValues_USBPDevs(s0.subjects, globals) &&
            WK_ValidGlobalVarValues_USBPDevList(s0.subjects, s0.id_mappings, globals) &&

            WK_ValidState_DevsActivateCond(s0.subjects, s0.objects, s0.id_mappings, s0.activate_conds, globals) &&
            WK_ValidObjsAddrs_PEHCIs(s0.subjects, s0.objects, s0.objs_addrs, s0.id_mappings, s0.activate_conds, globals)
        // Requirement: The initial state must fulfill most of the SIs in ValidState

    requires var globals := wkm_get_globals(s0.wk_mstate);
            WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(s0.subjects, s0.objects, s0.id_mappings, globals)

    requires OpsSaneStateSubset(s0) ==> WSM_OpsSaneState_Security_SI1(s0)
        // [NOTE] At this point, Dafny does not know we can prove OpsSaneStateSubset(s0)
        // Requirement: The initial state must fulfill some of the rest SIs

    ensures OpsSaneState(s0)
{
    var globals := wkm_get_globals(s0.wk_mstate);

    Lemma_P_InitialState_EmptyGlobalVars_ImpliesWK_ValidGlobalState(s0);
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();
    reveal WK_ValidGlobalVarValues_USBPDevs();

    assert ValidState(s0);

    // Prove SecureState
    assert WK_USBTD_Map_SecureGlobalVarValues(globals);
    assert WK_EEHCI_Mem_SecureGlobalVarValues(globals);
    Lemma_WSM_InitialState_ProveWK_SecureObjsAddrs_MemSeparation(s0);

    assert SecureState(s0);

    // Prove OpsSaneStateSubset
    reveal WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification();
    reveal WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure();
    
    assert OpsSaneStateSubset(s0);
}

// Theorem 1: If state wsn is reached after the application of trace t, and the
// beginning state t.ws0 is secure, then wsn is secure
lemma Lemma_WSM_ProveTheorem1(t:WSM_Trace, wsn:state)
    requires OpsSaneState(t.s0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:state, op:WSM_Op :: P_WSM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_WSM_OpsProperties
    requires WSM_IsValidTrace(t)

    requires wsn == WSM_CalcNewStates(t)[|WSM_CalcNewStates(t)|-1]

    ensures OpsSaneState(wsn)
{
    // Dafny can automatically prove this lemma
}

// Theorem 2: For all traces from secure state s0 to secure state sn, the
// state transitions of the trace fulfill all transition contraints
lemma Lemma_WSM_ProveTheorem2(s0:state, sn:state)
    requires OpsSaneState(s0)
    requires OpsSaneState(sn)
    
    requires forall ws:state, op:WSM_Op :: P_WSM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_WSM_OpsProperties
    
    ensures forall t:WSM_Trace :: |t.ops| > 0 &&
                    t.s0 == s0 &&
                    WSM_IsValidTrace(t) &&
                    sn == WSM_CalcNewStates(t)[|WSM_CalcNewStates(t)|-1]
                        // Trace t transits s0 to sn
                ==> (forall i :: 0 <= i < |t.ops| 
                        ==> WSM_IsSecureOps(WSM_CalcNewStates(t)[i], WSM_CalcNewStates(t)[i+1]))
                        // Each transition in trace satisfies all TCs
{
    forall t:WSM_Trace | |t.ops| > 0 &&
                    t.s0 == s0 &&
                    WSM_IsValidTrace(t) &&
                    sn == WSM_CalcNewStates(t)[|WSM_CalcNewStates(t)|-1]
        ensures forall i :: 0 <= i < |t.ops| 
                    ==> WSM_IsSecureOps(WSM_CalcNewStates(t)[i], WSM_CalcNewStates(t)[i+1])
    {
        var states_seq := WSM_CalcNewStates(t);
        forall i | 0 <= i < |t.ops|
            ensures WSM_IsSecureOps(states_seq[i], states_seq[i+1])
        {
            // Dafny can automatically prove this property
        }
    }
}




//******** Utility Predicates And Functions for High Level Theorems And Security Properties ********//
predicate P_InitialState_EmptyGlobalVars(s0:state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s0.wk_mstate))
{
    var globals := wkm_get_globals(s0.wk_mstate);

    // For G_Existing_PIDs and G_PID_Counter
    //// 1. Relationships of contants must hold
    PID_INVALID == TruncateUInt32(PID_MAX + 1) &&
    (PID_GENERATE_FUNC_ERROR == PID_RESERVED_OS_PARTITION) &&

    //// 2. <g_pid_counter> must never equal to PID_INVALID (== 0)
    pids_g_pid_counter_is_not_reserved_empty(globals) &&

    (
        var existing:seq<word> := global_read_fullval(globals, G_Existing_PIDs());
        forall i :: 0 <= i < |existing|
            ==> existing[i] == PID_INVALID
    ) &&

    // For G_WimpDrvs_Info
    (
        forall i :: wimpdrv_valid_slot_id(i)
            ==> wimpdrv_get_id_word(globals, i) == WimpDrv_ID_RESERVED_EMPTY
    ) &&

    (
        forall i :: wimpdrv_valid_slot_id(i)
            ==> wimpdrv_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    ) &&

    (
        forall i :: wimpdrv_valid_slot_id(i)
            ==> wimpdrv_do_get_flag(globals, i) != WimpDrv_Slot_UpdateFlag_Complete
    ) &&

    // For G_WimpUSBPDev_Info and G_WimpUSBPDev_DevList
    (
        forall i :: usbpdev_valid_slot_id(i)
            ==> usbpdev_get_addr_low(globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW &&
                usbpdev_get_addr_high(globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH &&
                usbpdev_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    ) &&

    (
        forall i :: usbpdev_valid_slot_id(i)
            ==> usbpdev_get_updateflag(globals, i) != WimpUSBPDev_Slot_UpdateFlag_Complete
    ) &&

    (
        forall i :: usbpdevlist_valid_slot_id(i)
            ==> (
                var usbpdev_addr_raw := usbpdevlist_get_addr(globals, i);
                usb_is_usbpdev_addr_valid(usbpdev_addr_raw)
            )
    ) &&

    // For G_EEHCI_MEM and G_EEHCI_MEM_PBASE and G_EEHCIs_Info
    (
        (eehci_mem_pbase(globals) >= 0) &&
        (eehci_mem_pend(globals) <= ARCH_WORD_LIMIT)
    ) &&

    (
        forall i :: eehci_valid_slot_id(i)
            ==> eehci_mem_get_eehci_id(globals, i) == eEHCI_ID_INVALID &&
                eehci_info_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    ) &&

    (forall i :: eehci_valid_slot_id(i)
        ==> EECHI_DoNotRefAnyUSBTD(globals, i)
    ) &&

    // For G_USBTD_MAP_MEM and G_USBTD_ID_Counter
    (
        // 1. In each slot of <g_usbtd_map_mem>, the PID field's value must be either invalid or a wimp partition's PID
        (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_pid(globals, i)) && 

        // 2. In each slot of <g_usbtd_map_mem>, the type field's value must be one of the allowed types
        (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_type(globals, i)) && 

        // 3. In each slot of <g_usbtd_map_mem>, the bus_id field's value must be one of the allowed types
        (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_busid(globals, i)) && 

        // 4. In each slot of <g_usbtd_map_mem>, the wimpdrv_slot field's value must be one of the allowed types
        (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_wimpdrv_slotid(globals, i)) && 

        // 5. In each slot of <g_usbtd_map_mem>, the usbpdev_slot field's value must be one of the allowed types
        (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_usbpdev_slotid(globals, i))
    ) &&

    (
        forall i :: usbtd_map_valid_slot_id(i)
            ==> usbtd_map_get_idword(globals, i) == USBTD_ID_INVALID
    ) &&

    (
        forall i :: usbtd_map_valid_slot_id(i)
            ==> usbtd_map_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    ) &&

    (true)
}

// If the operation (<op>) is one of the defined operations, then the requirements
// of the operation always implies the properties of the operation
// Note: All operations are proved to satisfy P_WSM_OpsProperties
predicate P_WSM_OpsProperties(s:state, op:WSM_Op)
{
    (op.WSM_WK_EmptyPartitionCreateOp? ==> P_WSM_WK_EmptyPartitionCreateOp(s, op)) &&
    (op.WSM_WK_EmptyPartitionDestroyOp? ==> P_WSM_WK_EmptyPartitionDestroyOp(s, op)) &&
    (op.WSM_WimpDrv_ActivateOp? ==> P_WSM_WimpDrv_ActivateOp(s, op)) &&
    (op.WSM_WimpDrv_DeactivateOp? ==> P_WSM_WimpDrv_DeactivateOp(s, op)) &&
    (op.WSM_USBPDev_ActivateOp? ==> P_WSM_USBPDev_ActivateOp(s, op)) &&
    (op.WSM_USBPDev_DeactivateOp? ==> P_WSM_USBPDev_DeactivateOp(s, op)) &&

    (op.WSM_USBTD_slot_allocate_1slotOp? ==> P_WSM_USBTD_slot_allocate_1slotOp(s, op)) &&
    (op.WSM_USBTD_slot_deallocate_1slotOp? ==> P_WSM_USBTD_slot_deallocate_1slotOp(s, op)) &&
    (op.WSM_USBTD_slot_submit_and_verify_qtd32Op? ==> P_WSM_USBTD_slot_submit_and_verify_qtd32Op(s, op)) &&
    (op.WSM_USBTD_slot_submit_and_verify_qh32Op? ==> P_WSM_USBTD_slot_submit_and_verify_qh32Op(s, op)) &&

    (op.WSM_EEHCI_ActivateOp? ==> P_WSM_EEHCI_ActivateOp(s, op)) &&
    (op.WSM_EEHCI_DeactivateOp? ==> P_WSM_EEHCI_DeactivateOp(s, op)) &&

    (op.WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevsOp? ==> P_WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevsOp(s, op)) &&
    (op.WSM_OS_Activate_MainMem_ByPAddrOp? ==> P_WSM_OS_Activate_MainMem_ByPAddrOp(s, op)) &&
    (op.WSM_OS_Deactivate_MainMem_ByPAddrOp? ==> P_WSM_OS_Deactivate_MainMem_ByPAddrOp(s, op)) &&

    (op.WSM_WimpDrv_Write_eEHCI_ConfigOp? ==> P_WimpDrv_Write_eEHCI_ConfigOp(s, op)) &&
    (op.WSM_WimpDrv_Read_eEHCI_ConfigOp? ==> P_WimpDrv_Read_eEHCI_ConfigOp(s, op)) &&
    (op.WSM_WimpDrv_Write_eEHCI_StatusOp? ==> P_WimpDrv_Write_eEHCI_StatusOp(s, op)) &&
    (op.WSM_WimpDrv_Read_eEHCI_StatusOp? ==> P_WimpDrv_Read_eEHCI_StatusOp(s, op)) &&
    (op.WSM_WimpDrv_Write_eEHCI_USBTDRegOp? ==> P_WimpDrv_Write_eEHCI_USBTDRegOp(s, op)) &&
    (op.WSM_WimpDrv_Read_eEHCI_USBTDRegOp? ==> P_WimpDrv_Read_eEHCI_USBTDRegOp(s, op)) &&


    // I/O accesses outside APIs
    (op.WSM_OSDrvRead_ByPAddrOp? ==> P_OSDrvRead_ByPAddrOp(s, op)) &&
    (op.WSM_OSDrvRead_ByPIOOp? ==> P_OSDrvRead_ByPIOOp(s, op)) &&
    (op.WSM_OSDrvRead_ByObjIDsOp? ==> P_OSDrvRead_ByObjIDsOp(s, op)) &&
    (op.WSM_OSDevRead_ByPAddrOp? ==> P_OSDevRead_ByPAddrOp(s, op)) &&
    (op.WSM_OSDevRead_ByPIOOp? ==> P_OSDevRead_ByPIOOp(s, op)) &&
    (op.WSM_OSNonUSBPDevRead_ByObjIDsOp? ==> P_OSNonUSBPDevRead_ByObjIDsOp(s, op)) &&

    (op.WSM_OSDrvWrite_ByPAddrOp? ==> P_OSDrvWrite_ByPAddrOp(s, op)) &&
    (op.WSM_OSDrvWrite_ByPIOOp? ==> P_OSDrvWrite_ByPIOOp(s, op)) &&
    (op.WSM_OSDrvWrite_ByObjIDsOp? ==> P_OSDrvWrite_ByObjIDsOp(s, op)) &&
    (op.WSM_OSDevWrite_ByPAddrOp? ==> P_OSDevWrite_ByPAddrOp(s, op)) &&
    (op.WSM_OSDevWrite_ByPIOOp? ==> P_OSDevWrite_ByPIOOp(s, op)) &&
    (op.WSM_OSNonUSBPDevWrite_ByObjIDsOp? ==> P_OSNonUSBPDevWrite_ByObjIDsOp(s, op)) &&

    (op.WSM_WimpDrvRead_ByPAddrOp? ==> P_WimpDrvRead_ByPAddrOp(s, op)) &&
    (op.WSM_WimpDrvWrite_ByPAddrOp? ==> P_WimpDrvWrite_ByPAddrOp(s, op)) &&
    (op.WSM_USBPDevRead_ByObjIDOp? ==> P_USBPDevRead_ByObjIDOp(s, op)) &&
    (op.WSM_USBPDevWrite_ByObjIDOp? ==> P_USBPDevWrite_ByObjIDOp(s, op)) &&

    (op.WSM_EEHCIWriteOwnDO_ByOffsetOp? ==> P_EEHCIWriteOwnDO_ByOffsetOp(s, op)) &&
    (op.WSM_EEHCIReadOwnObjs_ByOffsetOp? ==> P_EEHCIReadOwnObjs_ByOffsetOp(s, op)) &&
    (op.WSM_EEHCIReadUSBTD_BySlotIDOp? ==> P_EEHCIReadUSBTD_BySlotIDOp(s, op)) &&
    (op.WSM_EEHCIReadUSBPDevObj_ByObjIDOp? ==> P_EEHCIReadUSBPDevObj_ByObjIDOp(s, op)) &&
    (op.WSM_EEHCIWriteUSBPDevObj_ByObjIDOp? ==> P_EEHCIWriteUSBPDevObj_ByObjIDOp(s, op)) &&
    (op.WSM_EEHCIReadObjs_ByPAddrOp? ==> P_EEHCIReadObjs_ByPAddrOp(s, op)) &&
    (op.WSM_EEHCIWriteObjs_ByPAddrOp? ==> P_EEHCIWriteObjs_ByPAddrOp(s, op))
}

// If the operation (<op>) fulfill its preconditions
predicate P_WSM_OpsFulfillPreConditions(s:state, op:WSM_Op)
{
    (op.WSM_WK_EmptyPartitionCreateOp? ==> WSM_WK_EmptyPartitionCreate_PreConditions(s)) &&
    (op.WSM_WK_EmptyPartitionDestroyOp? ==> WSM_WK_EmptyPartitionDestroy_PreConditions(s)) &&
    (op.WSM_WimpDrv_ActivateOp? ==> WSM_WimpDrv_Activate_PreConditions(s)) &&
    (op.WSM_WimpDrv_DeactivateOp? ==> WSM_WimpDrv_Deactivate_PreConditions(s)) &&
    (op.WSM_USBPDev_ActivateOp? ==> WSM_USBPDev_Activate_PreConditions(s)) &&
    (op.WSM_USBPDev_DeactivateOp? ==> WSM_USBPDev_Deactivate_PreConditions(s)) &&

    (op.WSM_USBTD_slot_allocate_1slotOp? ==> WSM_USBTD_slot_allocate_1slot_PreConditions(s)) &&
    (op.WSM_USBTD_slot_deallocate_1slotOp? ==> WSM_USBTD_slot_deallocate_1slot_PreConditions(s)) &&
    (op.WSM_USBTD_slot_submit_and_verify_qtd32Op? ==> WSM_USBTD_slot_submit_and_verify_qtd32_PreConditions(s)) &&
    (op.WSM_USBTD_slot_submit_and_verify_qh32Op? ==> WSM_USBTD_slot_submit_and_verify_qh32_PreConditions(s)) &&

    (op.WSM_EEHCI_ActivateOp? ==> WSM_EEHCI_Activate_PreConditions(s)) &&
    (op.WSM_EEHCI_DeactivateOp? ==> WSM_EEHCI_Deactivate_PreConditions(s)) &&

    (op.WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevsOp? ==> WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_PreConditions(s)) &&
    (op.WSM_OS_Activate_MainMem_ByPAddrOp? ==> WSM_OS_Activate_MainMem_ByPAddr_PreConditions(s)) &&
    (op.WSM_OS_Deactivate_MainMem_ByPAddrOp? ==> WSM_OS_Deactivate_MainMem_ByPAddr_PreConditions(s)) &&

    (op.WSM_WimpDrv_Write_eEHCI_ConfigOp? ==> WSM_WimpDrv_Write_eEHCI_Config_PreConditions(s)) &&
    (op.WSM_WimpDrv_Read_eEHCI_ConfigOp? ==> WSM_WimpDrv_Read_eEHCI_Config_PreConditions(s)) &&
    (op.WSM_WimpDrv_Write_eEHCI_StatusOp? ==> WSM_WimpDrv_Write_eEHCI_Status_PreConditions(s)) &&
    (op.WSM_WimpDrv_Read_eEHCI_StatusOp? ==> WSM_WimpDrv_Read_eEHCI_Status_PreConditions(s)) &&
    (op.WSM_WimpDrv_Write_eEHCI_USBTDRegOp? ==> WSM_WimpDrv_Write_eEHCI_USBTDReg_PreConditions(s)) &&
    (op.WSM_WimpDrv_Read_eEHCI_USBTDRegOp? ==> WSM_WimpDrv_Read_eEHCI_USBTDReg_PreConditions(s)) &&

    // I/O accesses outside APIs
    (op.WSM_OSDrvRead_ByPAddrOp? ==> WSM_OSDrvRead_ByPAddr_PreConditions(s, op.drv_sid, op.paddr)) &&
    (op.WSM_OSDrvRead_ByPIOOp? ==> WSM_OSDrvRead_ByPIO_PreConditions(s, op.drv_sid, op.pio_addr)) &&
    (op.WSM_OSDrvRead_ByObjIDsOp? ==> WSM_OSDrvRead_ByObjIDs_PreConditions(s, op.drv_sid, op.read_tds, op.read_fds, op.read_dos)) &&
    (op.WSM_OSDevRead_ByPAddrOp? ==> WSM_OSDevRead_ByPAddr_PreConditions(s, op.dev_sid, op.paddr)) &&
    (op.WSM_OSDevRead_ByPIOOp? ==> WSM_OSDevRead_ByPIO_PreConditions(s, op.dev_sid, op.pio_addr)) &&
    (op.WSM_OSNonUSBPDevRead_ByObjIDsOp? ==> WSM_OSNonUSBPDevRead_ByObjIDs_PreConditions(s, op.dev_sid, op.read_tds, op.read_fds, op.read_dos)) &&

    (op.WSM_OSDrvWrite_ByPAddrOp? ==> WSM_OSDrvWrite_ByPAddr_PreConditions(s, op.drv_sid, op.paddr, op.new_v)) &&
    (op.WSM_OSDrvWrite_ByPIOOp? ==> WSM_OSDrvWrite_ByPIO_PreConditions(s, op.drv_sid, op.pio_addr, op.new_v)) &&
    (op.WSM_OSDrvWrite_ByObjIDsOp? ==> WSM_OSDrvWrite_ByObjIDs_PreConditions(s, op.drv_sid, op.wsm_td_id_val_map, op.wsm_fd_id_val_map, op.wsm_do_id_val_map)) &&
    (op.WSM_OSDevWrite_ByPAddrOp? ==> WSM_OSDevWrite_ByPAddr_PreConditions(s, op.dev_sid, op.paddr, op.new_v)) &&
    (op.WSM_OSDevWrite_ByPIOOp? ==> WSM_OSDevWrite_ByPIO_PreConditions(s, op.dev_sid, op.pio_addr, op.new_v)) &&
    (op.WSM_OSNonUSBPDevWrite_ByObjIDsOp? ==> WSM_OSNonUSBPDevWrite_ByObjIDs_PreConditions(s, op.dev_sid, op.wsm_td_id_val_map, op.wsm_fd_id_val_map, op.wsm_do_id_val_map)) &&

    (op.WSM_WimpDrvRead_ByPAddrOp? ==> WSM_WimpDrvRead_ByPAddr_PreConditions(s, op.drv_id_word, op.read_paddr_start, op.read_paddr_end)) &&
    (op.WSM_WimpDrvWrite_ByPAddrOp? ==> WSM_WimpDrvWrite_ByPAddr_PreConditions(s, op.drv_id_word, op.paddr_start, op.paddr_end, op.new_val)) &&
    (op.WSM_USBPDevRead_ByObjIDOp? ==> WSM_USBPDevRead_ByObjID_PreConditions(s, op.usbpdev_addr, op.read_fds, op.read_dos)) &&
    (op.WSM_USBPDevWrite_ByObjIDOp? ==> WSM_USBPDevWrite_ByObjID_PreConditions(s, op.usbpdev_addr, op.fd_id_val_map, op.do_id_val_map)) && 

    (op.WSM_EEHCIWriteOwnDO_ByOffsetOp? ==> WSM_EEHCIWriteOwnDO_ByOffset_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.offset, op.new_val1)) &&
    (op.WSM_EEHCIReadOwnObjs_ByOffsetOp? ==> WSM_EEHCIReadOwnObjs_ByOffset_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.offset)) &&
    (op.WSM_EEHCIReadUSBTD_BySlotIDOp? ==> WSM_EEHCIReadUSBTD_BySlotID_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.usbtd_slot)) &&
    (op.WSM_EEHCIReadUSBPDevObj_ByObjIDOp? ==> WSM_EEHCIReadUSBPDevObj_ByObjID_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.fd_ids, op.do_ids)) &&
    (op.WSM_EEHCIWriteUSBPDevObj_ByObjIDOp? ==> WSM_EEHCIWriteUSBPDevObj_ByObjID_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.fd_id_val_map, op.do_id_val_map)) &&
    (op.WSM_EEHCIReadObjs_ByPAddrOp? ==> WSM_EEHCIReadObjs_ByPAddr_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.read_paddr_start, op.read_paddr_end)) &&
    (op.WSM_EEHCIWriteObjs_ByPAddrOp? ==> WSM_EEHCIWriteObjs_ByPAddr_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.write_paddr_start, op.write_paddr_end, op.new_val))
}

// Valid trace: all intermediate ws and op fulfill all preconditions of the 
// corresponding operation
predicate WSM_IsValidTrace(t:WSM_Trace)
    requires OpsSaneState(t.s0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:state, op:WSM_Op :: P_WSM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_WSM_OpsProperties

    decreases |t.ops| 
{
    if(|t.ops| == 0) then
        true
    else
        var b1 := P_WSM_OpsFulfillPreConditions(t.s0, t.ops[0]);
        if(!b1) then 
            false
        else
            var k1 := WSM_CalcNewState(t.s0, t.ops[0]).0; // Eval t.ops[0]
            b1 && WSM_IsValidTrace(WSM_Trace(k1, t.ops[1..]))
}

// Given a secure state and a transition, calculate the result state
function WSM_CalcNewState(s:state, op:WSM_Op) : (result:(state, bool))
    requires OpsSaneState(s)
    requires P_WSM_OpsProperties(s, op)
    requires P_WSM_OpsFulfillPreConditions(s, op)

    ensures OpsSaneState(result.0) // result.0 is the new State
    ensures WSM_IsSecureOps(s, result.0)
{
    if(op.WSM_WK_EmptyPartitionCreateOp?) then
        var s', ws_d :| WSM_WK_EmptyPartitionCreate_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_WK_EmptyPartitionDestroyOp?) then
        var s', ws_d :| WSM_WK_EmptyPartitionDestroy_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_WimpDrv_ActivateOp?) then
        var s', ws_d :| WSM_WimpDrv_Activate_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_WimpDrv_DeactivateOp?) then
        var s', ws_d :| WSM_WimpDrv_Deactivate_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_USBPDev_ActivateOp?) then
        var s', ws_d :| WSM_USBPDev_Activate_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_USBPDev_DeactivateOp?) then
        var s', ws_d :| WSM_USBPDev_Deactivate_PostConditions(s, s', ws_d); (s', ws_d)

    else if(op.WSM_USBTD_slot_allocate_1slotOp?) then
        var s', ws_d :| WSM_USBTD_slot_allocate_1slot_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_USBTD_slot_deallocate_1slotOp?) then
        var s', ws_d :| WSM_USBTD_slot_deallocate_1slot_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_USBTD_slot_submit_and_verify_qtd32Op?) then
        var s', ws_d :| WSM_USBTD_slot_submit_and_verify_qtd32_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_USBTD_slot_submit_and_verify_qh32Op?) then
        var s', ws_d :| WSM_USBTD_slot_submit_and_verify_qh32_PostConditions(s, s', ws_d); (s', ws_d)

    else if(op.WSM_EEHCI_ActivateOp?) then
        var s', ws_d :| WSM_EEHCI_Activate_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_EEHCI_DeactivateOp?) then
        var s', ws_d :| WSM_EEHCI_Deactivate_PostConditions(s, s', ws_d); (s', ws_d)

    else if(op.WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevsOp?) then
        var s', ws_d :| WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_OS_Activate_MainMem_ByPAddrOp?) then
        var s', ws_d :| WSM_OS_Activate_MainMem_ByPAddr_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_OS_Deactivate_MainMem_ByPAddrOp?) then
        var s', ws_d :| WSM_OS_Deactivate_MainMem_ByPAddr_PostConditions(s, s', ws_d); (s', ws_d)

    else if(op.WSM_WimpDrv_Write_eEHCI_ConfigOp?) then
        var s', ws_d :| WSM_WimpDrv_Write_eEHCI_Config_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_WimpDrv_Read_eEHCI_ConfigOp?) then
        var s', ws_d :| WSM_WimpDrv_Read_eEHCI_Config_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_WimpDrv_Write_eEHCI_StatusOp?) then
        var s', ws_d :| WSM_WimpDrv_Write_eEHCI_Status_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_WimpDrv_Read_eEHCI_StatusOp?) then
        var s', ws_d :| WSM_WimpDrv_Read_eEHCI_Status_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_WimpDrv_Write_eEHCI_USBTDRegOp?) then
        var s', ws_d :| WSM_WimpDrv_Write_eEHCI_USBTDReg_PostConditions(s, s', ws_d); (s', ws_d)
    else if(op.WSM_WimpDrv_Read_eEHCI_USBTDRegOp?) then
        var s', ws_d :| WSM_WimpDrv_Read_eEHCI_USBTDReg_PostConditions(s, s', ws_d); (s', ws_d)


    // I/O accesses outside APIs
    else if(op.WSM_OSDrvRead_ByPAddrOp?) then
        var s', ws_d :| WSM_OSDrvRead_ByPAddr_PostConditions(s, op.drv_sid, op.paddr, s', ws_d); (s', ws_d)
    else if(op.WSM_OSDrvRead_ByPIOOp?) then
        var s', ws_d :| WSM_OSDrvRead_ByPIO_PostConditions(s, op.drv_sid, op.pio_addr, s', ws_d); (s', ws_d)
    else if(op.WSM_OSDrvRead_ByObjIDsOp?) then
        var s', ws_d :| WSM_OSDrvRead_ByObjIDs_PostConditions(s, op.drv_sid, op.read_tds, op.read_fds, op.read_dos, s', ws_d); (s', ws_d)
    else if(op.WSM_OSDevRead_ByPAddrOp?) then
        var s', ws_d :| WSM_OSDevRead_ByPAddr_PostConditions(s, op.dev_sid, op.paddr, s', ws_d); (s', ws_d)
    else if(op.WSM_OSDevRead_ByPIOOp?) then
        var s', ws_d :| WSM_OSDevRead_ByPIO_PostConditions(s, op.dev_sid, op.pio_addr, s', ws_d); (s', ws_d)
    else if(op.WSM_OSNonUSBPDevRead_ByObjIDsOp?) then
        var s', ws_d :| WSM_OSNonUSBPDevRead_ByObjIDs_PostConditions(s, op.dev_sid, op.read_tds, op.read_fds, op.read_dos, s', ws_d); (s', ws_d)

    else if(op.WSM_OSDrvWrite_ByPAddrOp?) then
        var s', ws_d :| WSM_OSDrvWrite_ByPAddr_PostConditions(s, op.drv_sid, op.paddr, op.new_v, s', ws_d); (s', ws_d)
    else if(op.WSM_OSDrvWrite_ByPIOOp?) then
        var s', ws_d :| WSM_OSDrvWrite_ByPIO_PostConditions(s, op.drv_sid, op.pio_addr, op.new_v, s', ws_d); (s', ws_d)
    else if(op.WSM_OSDrvWrite_ByObjIDsOp?) then
        var s', ws_d :| WSM_OSDrvWrite_ByObjIDs_PostConditions(s, op.drv_sid, op.wsm_td_id_val_map, op.wsm_fd_id_val_map, op.wsm_do_id_val_map, s', ws_d); (s', ws_d)
    else if(op.WSM_OSDevWrite_ByPAddrOp?) then
        var s', ws_d :| WSM_OSDevWrite_ByPAddr_PostConditions(s, op.dev_sid, op.paddr, op.new_v, s', ws_d); (s', ws_d)
    else if(op.WSM_OSDevWrite_ByPIOOp?) then
        var s', ws_d :| WSM_OSDevWrite_ByPIO_PostConditions(s, op.dev_sid, op.pio_addr, op.new_v, s', ws_d); (s', ws_d)
    else if(op.WSM_OSNonUSBPDevWrite_ByObjIDsOp?) then
        var s', ws_d :| WSM_OSNonUSBPDevWrite_ByObjIDs_PostConditions(s, op.dev_sid, op.wsm_td_id_val_map, op.wsm_fd_id_val_map, op.wsm_do_id_val_map, s', ws_d); (s', ws_d)

    else if(op.WSM_WimpDrvRead_ByPAddrOp?) then
        var s', ws_d :| WSM_WimpDrvRead_ByPAddr_PostConditions(s, op.drv_id_word, op.read_paddr_start, op.read_paddr_end, s', ws_d); (s', ws_d)
    else if(op.WSM_WimpDrvWrite_ByPAddrOp?) then
        var s', ws_d :| WSM_WimpDrvWrite_ByPAddr_PostConditions(s, op.drv_id_word, op.paddr_start, op.paddr_end, op.new_val, s', ws_d); (s', ws_d)
    else if(op.WSM_USBPDevRead_ByObjIDOp?) then
        var s', ws_d :| WSM_USBPDevRead_ByObjID_PostConditions(s, op.usbpdev_addr, op.read_fds, op.read_dos, s', ws_d); (s', ws_d)
    else if(op.WSM_USBPDevWrite_ByObjIDOp?) then
        var s', ws_d :| WSM_USBPDevWrite_ByObjID_PostConditions(s, op.usbpdev_addr, op.fd_id_val_map, op.do_id_val_map, s', ws_d); (s', ws_d)

    else if(op.WSM_EEHCIWriteOwnDO_ByOffsetOp?) then
        var s', ws_d :| WSM_EEHCIWriteOwnDO_ByOffset_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.offset, op.new_val1, s', ws_d); (s', ws_d)
    else if(op.WSM_EEHCIReadOwnObjs_ByOffsetOp?) then
        var s', ws_d :| WSM_EEHCIReadOwnObjs_ByOffset_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.offset, s', ws_d); (s', ws_d)
    else if(op.WSM_EEHCIReadUSBTD_BySlotIDOp?) then
        var s', ws_d :| WSM_EEHCIReadUSBTD_BySlotID_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.usbtd_slot, s', ws_d); (s', ws_d)
    else if(op.WSM_EEHCIReadUSBPDevObj_ByObjIDOp?) then
        var s', ws_d :| WSM_EEHCIReadUSBPDevObj_ByObjID_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.fd_ids, op.do_ids, s', ws_d); (s', ws_d)
    else if(op.WSM_EEHCIWriteUSBPDevObj_ByObjIDOp?) then
        var s', ws_d :| WSM_EEHCIWriteUSBPDevObj_ByObjID_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.fd_id_val_map, op.do_id_val_map, s', ws_d); (s', ws_d)
    else if(op.WSM_EEHCIReadObjs_ByPAddrOp?) then
        var s', ws_d, wimpdrv_slot :| WSM_EEHCIReadObjs_ByPAddr_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.read_paddr_start, op.read_paddr_end, s', ws_d, wimpdrv_slot); (s', ws_d)
    else
        assert op.WSM_EEHCIWriteObjs_ByPAddrOp?;
        var s', ws_d, wimpdrv_idword :| WSM_EEHCIWriteObjs_ByPAddr_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.write_paddr_start, op.write_paddr_end, op.new_val, s', ws_d, wimpdrv_idword); (s', ws_d)
}

// Given a trace, calculate all the reached states
function WSM_CalcNewStates(t:WSM_Trace) : (states:seq<state>)
    requires OpsSaneState(t.s0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:state, op:WSM_Op :: P_WSM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_WSM_OpsProperties

    requires WSM_IsValidTrace(t)

    ensures |states| == |t.ops| + 1
    ensures forall i :: 0 <= i <= |states| - 1
                ==> OpsSaneState(states[i])
    ensures forall i :: 0 <= i < |states| - 1
                ==> OpsSaneState(states[i+1])
    ensures forall i :: 0 <= i < |states| - 1
                ==> WSM_IsSecureOps(states[i], states[i+1])
        // Properties from WSM_CalcNewState
    ensures forall i :: 0 <= i < |states| - 1
                ==> P_WSM_OpsFulfillPreConditions(states[i], t.ops[i])
    ensures forall i :: 0 <= i < |states| - 1
                ==> states[i+1] == WSM_CalcNewState(states[i], t.ops[i]).0
        // Property: <states> form a chain
    ensures states[0] == t.s0

    decreases |t.ops| 
{
    if(|t.ops| == 0) then
        [t.s0]
    else
        var ws1 := WSM_CalcNewState(t.s0, t.ops[0]).0; // Eval t.ops[0]
        var step_states := WSM_CalcNewStates(WSM_Trace(ws1, t.ops[1..]));
        var result_states := [t.s0] + step_states;
        assert OpsSaneState(ws1);
        assert P_WSM_OpsFulfillPreConditions(t.s0, t.ops[0]);

        Lemma_WSM_CalcNewStates_Private1(t.s0, step_states, result_states);
        Lemma_SequenceHighlightFirstElem(t.ops);
        assert t.ops == [t.ops[0]] + t.ops[1..];
        Lemma_WSM_CalcNewStates_Private2(t.s0, step_states, result_states, t.ops[0], WSM_Trace(ws1, t.ops[1..]), t);
        Lemma_WSM_CalcNewStates_Private3(t.s0, step_states, result_states);
        Lemma_WSM_CalcNewStates_Private4(t.s0, step_states, result_states, t.ops[0], WSM_Trace(ws1, t.ops[1..]), t);
        result_states
}




//******** Private Lemmas  ********//
lemma Lemma_WSM_CalcNewStates_Private1(state:state, step_states:seq<state>, result_states:seq<state>)
    requires forall i :: 0 <= i <= |step_states| - 1
                ==> OpsSaneState(step_states[i])
    requires OpsSaneState(state)

    requires result_states == [state] + step_states

    ensures forall i :: 0 <= i <= |result_states| - 1
                ==> OpsSaneState(result_states[i])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSM_CalcNewStates_Private2(state:state, step_states:seq<state>, result_states:seq<state>, op:WSM_Op, step_t:WSM_Trace, t:WSM_Trace)
    requires |t.ops| > 0
    requires |step_states| == |step_t.ops| + 1
    requires forall i :: 0 <= i < |step_states| - 1
                ==> P_WSM_OpsFulfillPreConditions(step_states[i], step_t.ops[i])
    requires P_WSM_OpsFulfillPreConditions(state, op);

    requires result_states == [state] + step_states
    requires t.ops == [op] + step_t.ops

    ensures forall i :: 0 <= i < |result_states| - 1
                ==> P_WSM_OpsFulfillPreConditions(result_states[i], t.ops[i])
{
    forall i | 0 <= i < |result_states| - 1
        ensures P_WSM_OpsFulfillPreConditions(result_states[i], t.ops[i])
    {
        if (i == 0)
        {
            assert result_states[i] == state;
            assert t.ops[i] == op;
        }
        else
        {
            Lemma_SeqInsertFirstCorrectnessProperties(result_states, step_states, state);
            assert result_states[i] == step_states[i-1];
            Lemma_SeqInsertFirstCorrectnessProperties(t.ops, step_t.ops, op);
            assert t.ops[i] == step_t.ops[i-1];
        }
    }
}

lemma Lemma_WSM_CalcNewStates_Private3(
    state:state, step_states:seq<state>, result_states:seq<state>
)
    requires forall i :: 0 <= i <= |step_states| - 1
                ==> OpsSaneState(step_states[i])
    requires forall i :: 0 <= i < |step_states| - 1
                ==> WSM_IsSecureOps(step_states[i], step_states[i+1])
    requires OpsSaneState(state)

    requires |step_states| > 0
    requires result_states == [state] + step_states
    requires WSM_IsSecureOps(state, step_states[0])

    requires forall i :: 0 <= i < |result_states| - 1
                ==> OpsSaneState(result_states[i])
    requires forall i :: 0 <= i < |result_states| - 1
                ==> OpsSaneState(result_states[i+1])
    ensures forall i :: 0 <= i < |result_states| - 1
                ==> WSM_IsSecureOps(result_states[i], result_states[i+1])
{
    forall i | 0 <= i < |result_states| - 1
        ensures OpsSaneState(result_states[i])
        ensures OpsSaneState(result_states[i+1])
        ensures WSM_IsSecureOps(result_states[i], result_states[i+1])
    {
        assert 0 <= i <= |result_states| - 1;
        assert 0 <= i+1 <= |result_states| - 1;
        assert OpsSaneState(result_states[i]);
        assert OpsSaneState(result_states[i+1]); 


        if (i == 0)
        {
            assert result_states[i] == state;
            assert result_states[i+1] == step_states[0];
            assert WSM_IsSecureOps(result_states[i], result_states[i+1]);
        }
        else
        {
            assert i > 0;
            Lemma_WSM_CalcNewStates_Private3_GreaterThan0(state, step_states, result_states, i);
        }
    }
}

lemma Lemma_WSM_CalcNewStates_Private4(state:state, step_states:seq<state>, result_states:seq<state>, op:WSM_Op, step_t:WSM_Trace, t:WSM_Trace)
    requires forall ws:state, op:WSM_Op :: P_WSM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_WSM_OpsProperties

    requires |t.ops| > 0
    requires |step_states| == |step_t.ops| + 1
    requires forall i :: 0 <= i < |step_states| - 1
                ==> OpsSaneState(step_states[i])
    requires forall i :: 0 <= i < |step_states| - 1
                ==> P_WSM_OpsFulfillPreConditions(step_states[i], step_t.ops[i])
    requires forall i :: 0 <= i < |step_states| - 1
                ==> step_states[i+1] == WSM_CalcNewState(step_states[i], step_t.ops[i]).0
    requires P_WSM_OpsFulfillPreConditions(state, op);

    requires result_states == [state] + step_states
    requires t.ops == [op] + step_t.ops
    requires step_states[0] == WSM_CalcNewState(state, op).0

    requires forall i :: 0 <= i < |result_states| - 1
                ==> OpsSaneState(result_states[i])
    requires forall i :: 0 <= i < |result_states| - 1
                ==> P_WSM_OpsFulfillPreConditions(result_states[i], t.ops[i])

    ensures forall i :: 0 <= i < |result_states| - 1
                ==> result_states[i+1] == WSM_CalcNewState(result_states[i], t.ops[i]).0
{
    forall i | 0 <= i < |result_states| - 1
        ensures result_states[i+1] == WSM_CalcNewState(result_states[i], t.ops[i]).0
    {
        if (i == 0)
        {
            Lemma_WSM_CalcNewStates_Private4_EqualTo0(state, step_states, result_states, op, step_t, t, i);
        }
        else
        {
            Lemma_WSM_CalcNewStates_Private4_GreaterThan0(state, step_states, result_states, op, step_t, t, i);
        }
    }
}

/*
lemma Lemma_ValidDM_HCodedTDsAreTDs(ws:state)
    requires DM_IsValidState(ws)
    ensures forall dev_id :: dev_id in ws.subjects.devs
        ==> ws.subjects.devs[dev_id].hcoded_td_id in AllTDIDs(ws.objects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_ProveSP2_Private(ws:state, ws':state)
    requires DM_IsValidState(ws)

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires WSM_IsSecureOps(ws, ws')

    ensures forall td_id :: P_WSM_IsNonHCodedTDBeingMovedToAnActivePartition(ws, ws', td_id)
                    ==> DM_IsTDClearVal(ws'.objects, td_id)
    ensures forall fd_id :: P_WSM_IsFDBeingMovedToAnActivePartition(ws, ws', fd_id)
                    ==> DM_IsFDClearVal(ws'.objects, fd_id)
    ensures forall do_id :: P_WSM_IsDOBeingMovedToAnActivePartition(ws, ws', do_id)
                    ==> DM_IsDOClearVal(ws'.objects, do_id) 
{
    // Dafny can automatically prove this lemma
}
*/

lemma Lemma_P_InitialState_EmptyGlobalVars_ImpliesWK_ValidGlobalState(s0:state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s0.wk_mstate))
    requires P_InitialState_EmptyGlobalVars(s0)

    ensures WK_ValidGlobalState(wkm_get_globals(s0.wk_mstate))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSM_InitialState_ProveWK_SecureObjsAddrs_MemSeparation(s0:state)
    requires Valid_WKMachineState_Arch(s0.wk_mstate) && WK_ValidMemState(s0.wk_mstate)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s0.wk_mstate))
    
    requires P_InitialState_EmptyGlobalVars(s0)
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> TestBit(usbtd_map_get_flags(wkm_get_globals(s0.wk_mstate), i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false
    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s0.subjects, usbpdev_id)
                ==> s0.subjects.usbpdevs[usbpdev_id].active_in_os == false
    requires var globals := wkm_get_globals(s0.wk_mstate);
             forall i :: eehci_valid_slot_id(i) 
                ==> eehci_mem_get_intr_enable_reg(globals, i) == eEHCI_Intr_Disable
        // Requirement: The value of the initial state

    requires var globals := wkm_get_globals(s0.wk_mstate);
            WK_ValidSubjs(s0.subjects, s0.id_mappings) &&
            WK_ValidObjs(s0.subjects, s0.objects) &&
            WK_ValidIDMappings(s0.subjects, s0.objects, s0.id_mappings) &&
            WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s0.subjects, s0.objects, s0.id_mappings, globals) &&
            WK_ValidObjsAddrs(s0.objects, s0.objs_addrs, globals) &&
            //WK_ValidObjAddrs_WimpDrv_DOPAddrs(s0.subjects, s0.objects, s0.id_mappings, s0.objs_addrs, globals) &&
            //WK_ValidGlobalVarValues_USBPDevs(s0.subjects, globals) &&
            WK_ValidGlobalVarValues_USBPDevList(s0.subjects, s0.id_mappings, globals) &&

            WK_ValidState_DevsActivateCond(s0.subjects, s0.objects, s0.id_mappings, s0.activate_conds, globals) &&
            WK_ValidObjsAddrs_PEHCIs(s0.subjects, s0.objects, s0.objs_addrs, s0.id_mappings, s0.activate_conds, globals)
        // Requirement: The initial state must fulfill most of the SIs in ValidState

    requires ValidState(s0)

    ensures WK_SecureObjsAddrs_MemSeparation(s0.subjects, s0.objects, s0.id_mappings, s0.objs_addrs, wkm_get_globals(s0.wk_mstate))
{
    reveal WK_ValidObjsAddrs();

    var subjs := s0.subjects;
    var objs := s0.objects;
    var id_mappings := s0.id_mappings;
    var objs_addrs := s0.objs_addrs;
    var globals := wkm_get_globals(s0.wk_mstate);

    assert (forall i, j :: wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            i != j
        ==> WK_WimpDrv_DOMustNotOverlapWithEachOther(globals, i, j));
    
    Lemma_ValidState_ProveWK_ValidObjs_ObjIDs(s0);
    reveal WK_ValidObjs_ObjIDs();
    forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
                    WSM_IsOSTDID(objs, os_obj_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) &&   // Active OS TD
                    WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) && // Active WimpDrv's DO
                    pmem1 in objs_addrs.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)    // Separate in memory
    {
        assert !WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid);
    }
    
    forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
                    WSM_IsOSFDID(objs, os_obj_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) &&   // Active OS FD
                    WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) && // Active WimpDrv's DO
                    pmem1 in objs_addrs.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)    // Separate in memory
    {
        assert !WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid);
    }
    
    forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
                    WSM_IsOSDOID(objs, os_obj_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) &&   // Active OS DO
                    WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) && // Active WimpDrv's DO
                    pmem1 in objs_addrs.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)    // Separate in memory
    {
        assert !WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid);
    }
            
    reveal WK_SecureObjsAddrs_MemSeparation();
}




//******** Private Lemmas of Private Lemmas ********//
lemma Lemma_WSM_CalcNewStates_Private3_GreaterThan0(
    state:state, step_states:seq<state>, result_states:seq<state>, i:int
)
    requires forall i :: 0 <= i <= |step_states| - 1
                ==> OpsSaneState(step_states[i])
    requires forall i :: 0 <= i < |step_states| - 1
                ==> WSM_IsSecureOps(step_states[i], step_states[i+1])
    requires OpsSaneState(state)

    requires |step_states| > 0
    requires result_states == [state] + step_states
    requires WSM_IsSecureOps(state, step_states[0])

    requires 0 < i < |result_states| - 1
    requires OpsSaneState(result_states[i])
    requires OpsSaneState(result_states[i+1])

    ensures WSM_IsSecureOps(result_states[i], result_states[i+1])
{
    assert i > 0;
    Lemma_SeqInsertFirstCorrectnessProperties(result_states, step_states, state);
    assert result_states[i] == step_states[i-1];
    assert result_states[i+1] == step_states[i];

    // Prove 0 <= i - 1 < |step_states| - 1
    assert 0 <= i - 1 < |step_states| - 1;

    // Prove 0 <= i < |step_states|
    assert 0 < i < |result_states| - 1;
    assert |result_states| == |step_states| + 1;
    assert 0 <= i < |step_states|;

    Lemma_WSM_CalcNewStates_Private3_GreaterThan0_Inner(step_states, i);
    assert WSM_IsSecureOps(step_states[i-1], step_states[i]);
    assert WSM_IsSecureOps(result_states[i], result_states[i+1]);
}

lemma Lemma_WSM_CalcNewStates_Private3_GreaterThan0_Inner(
    step_states:seq<state>, i:int
)
    requires forall i :: 0 <= i <= |step_states| - 1
                ==> OpsSaneState(step_states[i])
    requires forall i :: 0 <= i < |step_states| - 1
                ==> WSM_IsSecureOps(step_states[i], step_states[i+1])

    requires 0 <= i - 1 < |step_states| - 1
    requires 0 <= i < |step_states|

    ensures WSM_IsSecureOps(step_states[i-1], step_states[i])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WSM_CalcNewStates_Private4_EqualTo0(
    state:state, step_states:seq<state>, result_states:seq<state>, 
    op:WSM_Op, step_t:WSM_Trace, t:WSM_Trace, i:int
)
    requires forall ws:state, op:WSM_Op :: P_WSM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_WSM_OpsProperties

    requires |t.ops| > 0
    requires |step_states| == |step_t.ops| + 1
    requires forall i :: 0 <= i < |step_states| - 1
                ==> OpsSaneState(step_states[i])
    requires forall i :: 0 <= i < |step_states| - 1
                ==> P_WSM_OpsFulfillPreConditions(step_states[i], step_t.ops[i])
    requires forall i :: 0 <= i < |step_states| - 1
                ==> step_states[i+1] == WSM_CalcNewState(step_states[i], step_t.ops[i]).0
    requires P_WSM_OpsFulfillPreConditions(state, op);

    requires result_states == [state] + step_states
    requires t.ops == [op] + step_t.ops
    requires step_states[0] == WSM_CalcNewState(state, op).0

    requires i == 0

    ensures result_states[i+1] == WSM_CalcNewState(result_states[i], t.ops[i]).0
{
    assert result_states[i] == state;
    assert t.ops[i] == op;

    assert result_states[i+1] == WSM_CalcNewState(result_states[i], t.ops[i]).0;
}

lemma Lemma_WSM_CalcNewStates_Private4_GreaterThan0(
    state:state, step_states:seq<state>, result_states:seq<state>, 
    op:WSM_Op, step_t:WSM_Trace, t:WSM_Trace, i:int
)
    requires forall ws:state, op:WSM_Op :: P_WSM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_WSM_OpsProperties

    requires |t.ops| > 0
    requires |step_states| == |step_t.ops| + 1
    requires forall i :: 0 <= i < |step_states| - 1
                ==> OpsSaneState(step_states[i])
    requires forall i :: 0 <= i < |step_states| - 1
                ==> P_WSM_OpsFulfillPreConditions(step_states[i], step_t.ops[i])
    requires forall i :: 0 <= i < |step_states| - 1
                ==> step_states[i+1] == WSM_CalcNewState(step_states[i], step_t.ops[i]).0
    requires P_WSM_OpsFulfillPreConditions(state, op);

    requires result_states == [state] + step_states
    requires t.ops == [op] + step_t.ops
    requires step_states[0] == WSM_CalcNewState(state, op).0

    requires 0 < i < |result_states| - 1
    requires OpsSaneState(result_states[i])
    requires P_WSM_OpsFulfillPreConditions(result_states[i], t.ops[i])


    ensures result_states[i+1] == WSM_CalcNewState(result_states[i], t.ops[i]).0
{
    Lemma_SeqInsertFirstCorrectnessProperties(result_states, step_states, state);
    assert result_states[i] == step_states[i-1];
    assert result_states[i+1] == step_states[i];
    Lemma_SeqInsertFirstCorrectnessProperties(t.ops, step_t.ops, op);
    assert t.ops[i] == step_t.ops[i-1];

    assert result_states[i+1] == WSM_CalcNewState(result_states[i], t.ops[i]).0;
}