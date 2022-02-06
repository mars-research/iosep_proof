include "../mm/wk_globals.dfy"
include "../state_properties_OpsSaneStateSubset.s.dfy"
include "drv.s.dfy"
include "public/wimpdrv_util_predicates.s.dfy"
include "../ins/x86/ins_eval.s.dfy"
include "../partition_id.i.dfy"
include "../utils/model/utils_subjs_objs.i.dfy"

/*********************** Lemma for <g_wimpdrvs_info> Modification  ********************/
// Lemma: After writting <wimp driver ID> field a slot to be not WimpDrv_ID_RESERVED_EMPTY, the new global variable  
// satisfies WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDrvIDField_NonEmptyWimpDrvID(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires new_v != WimpDrv_ID_RESERVED_EMPTY
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | wimpdrv_valid_slot_id(i)
        ensures (wimpdrv_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                wimpdrv_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert wimpdrv_get_pid(new_globals, i) == wimpdrv_get_pid(old_globals, i);
    }
}

// Lemma: After writting <wimp driver ID> field a slot (which has PID_Invalid), the new global variable satisfies 
// WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDrvIDField_PIDIsAlreadyInvalid(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires wimpdrv_get_pid(old_globals, slot) == WS_PartitionID(PID_INVALID)
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | wimpdrv_valid_slot_id(i)
        ensures (wimpdrv_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                wimpdrv_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert wimpdrv_get_pid(new_globals, i) == wimpdrv_get_pid(old_globals, i);
    }
}

// Lemma: After writting <wimp driver ID> field a slot, the new global variable satisfies 
// WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingDrvIDField(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(new_globals)
{
    forall i | wimpdrv_valid_slot_id(i) &&
                wimpdrv_do_get_flag(new_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ensures WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(new_globals, i), wimpdrv_do_get_paddr_end(new_globals, i))
    {
        assert wimpdrv_do_get_paddr_base(new_globals, i) == wimpdrv_do_get_paddr_base(old_globals, i);
        assert wimpdrv_do_get_paddr_end(new_globals, i) == wimpdrv_do_get_paddr_end(old_globals, i);
    }
}

// Lemma: After writting <wimp driver ID> field of a slot, the new global variable satisfies 
// WK_ValidObjAddrs_WimpDrv_DOPAddrs
lemma Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingDrvIDField(
    s:state, s':state, new_globals:globalsmap, slot:word, new_v:word
)
    requires ValidState(s)
    
    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
            new_globals == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info(), vaddr1, new_v)
        // Requirement: Only the wimp driver's id_word is changing
    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), slot) == WimpDrv_Slot_UpdateFlag_Updating
        // Requirement: The flag of the wimp driver is WimpDrv_Slot_UpdateFlag_Updating at current

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, new_globals)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall i | wimpdrv_valid_slot_id(i) && 
            wimpdrv_do_get_flag(globals', i) == WimpDrv_Slot_UpdateFlag_Complete &&
            wimpdrv_get_pid(globals', i) != WS_PartitionID(PID_INVALID)
        ensures (
                var drv_id_word:word := wimpdrv_get_id_word(globals', i);
                var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);
                WSM_IsWimpDrvID(subjs', drv_id) &&
                    // Such active wimp driver must exist in the system
                var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
                var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;
                pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))}
                    // And its address stored in the global variable must match its spec in <objs_addrs'>
            )
    {
        var drv_id_word:word := wimpdrv_get_id_word(globals', i);
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);

        if(i != slot)
        {
            assert WSM_IsWimpDrvID(subjs', drv_id);

            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
            var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;

            assert pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))};
        }
    }
}

// Lemma: After writting <pid> field of a slot (which wimp driver ID is not WimpDrv_ID_RESERVED_EMPTY), the new global 
// variable satisfies WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingPIDField_WimpDrvAlreadyNotEmpty(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    //requires WimpDrv_Slot_UpdateFlag_Updating == wimpdrv_do_get_flag(old_globals, slot)
    requires wimpdrv_get_id_word(old_globals, slot) != WimpDrv_ID_RESERVED_EMPTY
    requires WS_PartitionID(new_v) in pids_parse_g_wimp_pids(old_globals)
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES
        ensures (wimpdrv_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                wimpdrv_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert wimpdrv_get_pid(new_globals, i) == wimpdrv_get_pid(old_globals, i) ||
               wimpdrv_get_pid(new_globals, i) == WS_PartitionID(new_v);
    }
}

// Lemma: After writting <pid> field of a slot to be PID_INVALID, the new global variable satisfies 
// WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingPIDField_NewPIDIsInvalid(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires new_v == PID_INVALID
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES
        ensures (wimpdrv_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                wimpdrv_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert wimpdrv_get_pid(new_globals, i) == wimpdrv_get_pid(old_globals, i) ||
               wimpdrv_get_pid(new_globals, i) == WS_PartitionID(new_v);
    }
}

// Lemma: After writting <pid> field a slot, the new global variable satisfies 
// WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingPIDField(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires wimpdrv_do_get_flag(old_globals, slot) == WimpDrv_Slot_UpdateFlag_Updating
    requires WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES &&
                wimpdrv_do_get_flag(new_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ensures WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(new_globals, i), wimpdrv_do_get_paddr_end(new_globals, i))
    {
        assert wimpdrv_do_get_paddr_base(new_globals, i) == wimpdrv_do_get_paddr_base(old_globals, i);
        assert wimpdrv_do_get_paddr_end(new_globals, i) == wimpdrv_do_get_paddr_end(old_globals, i);
    }
}

// Lemma: After writting <pid> field of a slot, the new global variable satisfies 
// WK_ValidObjAddrs_WimpDrv_DOPAddrs
lemma Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingPIDField(
    s:state, s':state, new_globals:globalsmap, slot:word, new_v:word
)
    requires ValidState(s)
    
    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info(), vaddr1, new_v)
        // Requirement: Only the wimp driver's pid is changing
    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), slot) == WimpDrv_Slot_UpdateFlag_Updating
        // Requirement: The flag of the wimp driver is WimpDrv_Slot_UpdateFlag_Updating at current

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, new_globals)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall i | wimpdrv_valid_slot_id(i) && 
            wimpdrv_do_get_flag(globals', i) == WimpDrv_Slot_UpdateFlag_Complete &&
            wimpdrv_get_pid(globals', i) != WS_PartitionID(PID_INVALID)
        ensures (
                var drv_id_word:word := wimpdrv_get_id_word(globals', i);
                var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);
                WSM_IsWimpDrvID(subjs', drv_id) &&
                    // Such active wimp driver must exist in the system
                var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
                var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;
                pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))}
                    // And its address stored in the global variable must match its spec in <objs_addrs'>
            )
    {
        var drv_id_word:word := wimpdrv_get_id_word(globals', i);
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);

        if(i != slot)
        {
            assert WSM_IsWimpDrvID(subjs', drv_id);

            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
            var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;

            assert pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))};
        }
    }
}

// Lemma: After writting <update_flag> field of a slot, the new global variable satisfies 
// WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingUpdateFlagField(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires new_v == WimpDrv_Slot_UpdateFlag_Complete && wimpdrv_get_id_word(old_globals, slot) == WimpDrv_ID_RESERVED_EMPTY
                ==> wimpdrv_get_pid(old_globals, slot) == WS_PartitionID(PID_INVALID)
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES
        ensures (wimpdrv_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                wimpdrv_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert wimpdrv_get_pid(new_globals, i) == wimpdrv_get_pid(old_globals, i);
    }
}

// Lemma: After writting <update_flag> field of a slot, the new global variable satisfies 
// WK_WimpDrvs_ValidGlobalVarValues_IDWords
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_HoldIfWrittingUpdateFlagField(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_val:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_val)
    requires WK_WimpDrvs_ValidGlobalVarValues_IDWords(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_IDWords(new_globals)
{
    forall i, j | wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            wimpdrv_get_id_word(new_globals, i) != WimpDrv_ID_RESERVED_EMPTY && wimpdrv_get_id_word(new_globals, j) != WimpDrv_ID_RESERVED_EMPTY
        ensures (wimpdrv_get_id_word(new_globals, i) == wimpdrv_get_id_word(new_globals, j) <==> i == j)
    {
        assert wimpdrv_do_get_paddr_base(new_globals, i) == wimpdrv_do_get_paddr_base(old_globals, i);
        assert wimpdrv_do_get_paddr_end(new_globals, i) == wimpdrv_do_get_paddr_end(old_globals, i);
    }
}

// Lemma: After writting <update_flag> field of a slot to be WimpDrv_Slot_UpdateFlag_Updating, the new global variable  
// satisfies WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToUpdating(
    old_globals:globalsmap, new_globals:globalsmap, slot:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Updating)
    requires WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES &&
                wimpdrv_do_get_flag(new_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ensures WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(new_globals, i), wimpdrv_do_get_paddr_end(new_globals, i))
    {
        assert wimpdrv_do_get_paddr_base(new_globals, i) == wimpdrv_do_get_paddr_base(old_globals, i);
        assert wimpdrv_do_get_paddr_end(new_globals, i) == wimpdrv_do_get_paddr_end(old_globals, i);
    }
}

// Lemma: After writting <update_flag> field of a slot to be WimpDrv_Slot_UpdateFlag_Updating, the new global variable  
// satisfies WK_ValidObjAddrs_WimpDrv_DOPAddrs
lemma Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToUpdating(
    s:state, s':state, new_globals:globalsmap, slot:word
)
    requires ValidState(s)
    
    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Updating)

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, new_globals)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();
}

lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToComplete(
    old_globals:globalsmap, new_globals:globalsmap, slot:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Complete)
    requires WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(old_globals)

    requires WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(old_globals, slot), wimpdrv_do_get_paddr_end(old_globals, slot))
    requires forall i :: wimpdrv_valid_slot_id(i) && i != slot &&
            wimpdrv_get_pid(old_globals, i) != WS_PartitionID(PID_INVALID) && wimpdrv_get_pid(old_globals, slot) != WS_PartitionID(PID_INVALID) &&
            wimpdrv_do_get_flag(old_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ==> !is_mem_region_overlap(wimpdrv_do_get_paddr_base(old_globals, i), wimpdrv_do_get_paddr_end(old_globals, i), 
                wimpdrv_do_get_paddr_base(old_globals, slot), wimpdrv_do_get_paddr_end(old_globals, slot))
        // Requirement: The DO paddr region of the new wimp driver (if active) does not overlap with existing submitted wimp drivers.
        // In other words, DOs of active wimp drivers do not overlap with each other

    ensures WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES &&
                wimpdrv_do_get_flag(new_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ensures WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(new_globals, i), wimpdrv_do_get_paddr_end(new_globals, i))
    {
        assert wimpdrv_do_get_paddr_base(new_globals, i) == wimpdrv_do_get_paddr_base(old_globals, i);
        assert wimpdrv_do_get_paddr_end(new_globals, i) == wimpdrv_do_get_paddr_end(old_globals, i);
    }

    assert forall i :: wimpdrv_valid_slot_id(i) &&
                wimpdrv_do_get_flag(new_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
            ==> WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(new_globals, i), wimpdrv_do_get_paddr_end(new_globals, i));
}

lemma Lemma__wimpdrv_update_slot_pid_to_invalid_Prove_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToComplete(
    old_globals:globalsmap, new_globals:globalsmap, slot:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Complete)
    requires WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(old_globals)
    
    requires wimpdrv_get_pid(old_globals, slot) == WS_PartitionID(PID_INVALID)
        // Requirement: The wimp driver must be set to inactive already
    requires WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(old_globals, slot), wimpdrv_do_get_paddr_end(old_globals, slot))
        // Requirement: The result DO paddr region must satisfy WK_ValidPMemRegion

    ensures WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES &&
                wimpdrv_do_get_flag(new_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ensures WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(new_globals, i), wimpdrv_do_get_paddr_end(new_globals, i))
    {
        assert wimpdrv_do_get_paddr_base(new_globals, i) == wimpdrv_do_get_paddr_base(old_globals, i);
        assert wimpdrv_do_get_paddr_end(new_globals, i) == wimpdrv_do_get_paddr_end(old_globals, i);
    }

    assert forall i :: wimpdrv_valid_slot_id(i) &&
                wimpdrv_do_get_flag(new_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
            ==> WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(new_globals, i), wimpdrv_do_get_paddr_end(new_globals, i));
}

// Lemma: After writting <do_paddr_base> field of a slot, the new global variable satisfies 
// WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDOPAddrBaseField(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES
        ensures (wimpdrv_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                wimpdrv_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert wimpdrv_get_pid(new_globals, i) == wimpdrv_get_pid(old_globals, i);
    }
}

// Lemma: After writting <do_paddr_base> field of a slot, the new global variable satisfies 
// WK_ValidObjAddrs_WimpDrv_DOPAddrs
lemma Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingDOPAddrBaseField(
    s:state, s':state, new_globals:globalsmap, slot:word, new_v:word
)
    requires ValidState(s)
    
    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info(), vaddr1, new_v)
        // Requirement: Only the wimp driver's do_paddr_base is changing
    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), slot) == WimpDrv_Slot_UpdateFlag_Updating
        // Requirement: The flag of the wimp driver is WimpDrv_Slot_UpdateFlag_Updating at current

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, new_globals)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall i | wimpdrv_valid_slot_id(i) && 
            wimpdrv_do_get_flag(globals', i) == WimpDrv_Slot_UpdateFlag_Complete &&
            wimpdrv_get_pid(globals', i) != WS_PartitionID(PID_INVALID)
        ensures (
                var drv_id_word:word := wimpdrv_get_id_word(globals', i);
                var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);
                WSM_IsWimpDrvID(subjs', drv_id) &&
                    // Such active wimp driver must exist in the system
                var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
                var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;
                pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))}
                    // And its address stored in the global variable must match its spec in <objs_addrs'>
            )
    {
        var drv_id_word:word := wimpdrv_get_id_word(globals', i);
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);

        if(i != slot)
        {
            assert WSM_IsWimpDrvID(subjs', drv_id);

            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
            var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;

            assert pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))};
        }
    }
}

// Lemma: After writting <do_paddr_base> field of a slot when the slot has the flag WimpDrv_Slot_UpdateFlag_Updating, 
// the new global variable satisfies WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingDOPAddrBaseField_UnderFlagUpdating(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            WimpDrv_Slot_UpdateFlag_Updating == global_read_word(old_globals, G_WimpDrvs_Info(), vaddr1)
        // Requirement: The slot is under the flag WimpDrv_Slot_UpdateFlag_Updating
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES &&
                wimpdrv_do_get_flag(new_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ensures WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(new_globals, i), wimpdrv_do_get_paddr_end(new_globals, i))
    {
        assert wimpdrv_do_get_paddr_base(new_globals, i) == wimpdrv_do_get_paddr_base(old_globals, i);
        assert wimpdrv_do_get_paddr_end(new_globals, i) == wimpdrv_do_get_paddr_end(old_globals, i);
    }
}

// Lemma: After writting <do_paddr_end> field of a slot, the new global variable satisfies 
// WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDOPAddrEndField(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES
        ensures (wimpdrv_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                wimpdrv_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert wimpdrv_get_pid(new_globals, i) == wimpdrv_get_pid(old_globals, i);
    }
}

// Lemma: After writting <do_paddr_end> field of a slot, the new global variable satisfies 
// WK_ValidObjAddrs_WimpDrv_DOPAddrs
lemma Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingDOPAddrEndField(
    s:state, s':state, new_globals:globalsmap, slot:word, new_v:word
)
    requires ValidState(s)
    
    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info(), vaddr1, new_v)
        // Requirement: Only the wimp driver's do_paddr_end is changing
    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), slot) == WimpDrv_Slot_UpdateFlag_Updating
        // Requirement: The flag of the wimp driver is WimpDrv_Slot_UpdateFlag_Updating at current

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, new_globals)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall i | wimpdrv_valid_slot_id(i) && 
            wimpdrv_do_get_flag(globals', i) == WimpDrv_Slot_UpdateFlag_Complete &&
            wimpdrv_get_pid(globals', i) != WS_PartitionID(PID_INVALID)
        ensures (
                var drv_id_word:word := wimpdrv_get_id_word(globals', i);
                var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);
                WSM_IsWimpDrvID(subjs', drv_id) &&
                    // Such active wimp driver must exist in the system
                var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
                var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;
                pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))}
                    // And its address stored in the global variable must match its spec in <objs_addrs'>
            )
    {
        var drv_id_word:word := wimpdrv_get_id_word(globals', i);
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);

        if(i != slot)
        {
            assert WSM_IsWimpDrvID(subjs', drv_id);

            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
            var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;

            assert pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))};
        }
    }
}

// Lemma: After writting <do_paddr_end> field of a slot when the slot has the flag WimpDrv_Slot_UpdateFlag_Updating, 
// the new global variable satisfies WK_WimpDrvs_ValidGlobalVarValues_PIDs
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingDOPAddrEndField_UnderFlagUpdating(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            WimpDrv_Slot_UpdateFlag_Updating == global_read_word(old_globals, G_WimpDrvs_Info(), vaddr1)
        // Requirement: The slot is under the flag WimpDrv_Slot_UpdateFlag_Updating
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_v)
    requires WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(old_globals)

    ensures WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(new_globals)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES &&
                wimpdrv_do_get_flag(new_globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ensures WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(new_globals, i), wimpdrv_do_get_paddr_end(new_globals, i))
    {
        assert wimpdrv_do_get_paddr_base(new_globals, i) == wimpdrv_do_get_paddr_base(old_globals, i);
        assert wimpdrv_do_get_paddr_end(new_globals, i) == wimpdrv_do_get_paddr_end(old_globals, i);
    }
}

// Lemma: If an operation updates all fields of a slot in <g_wimpdrvs_info> correctly, then that operation satisfies
// wimpdrv_info_newvalue
lemma Lemma_WK_WimpDrvs_UpdateAllFieldsMustSatisfy_wimpdrv_info_newvalue1(
    old_globals:globalsmap, new_globals:globalsmap, 
    slot:uint32, new_wimpdrv_id:uint32, new_pid:uint32, new_do_pbase:paddr, new_do_pend:paddr, 
    globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, globals4:globalsmap, globals5:globalsmap, globals6:globalsmap
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)
    requires WK_ValidGlobalVars_Decls(globals4)
    requires WK_ValidGlobalVars_Decls(globals5)
    requires WK_ValidGlobalVars_Decls(globals6)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) 

    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            globals1 == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Updating)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
            globals2 == global_write_word(globals1, G_WimpDrvs_Info(), vaddr1, new_wimpdrv_id)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
            globals3 == global_write_word(globals2, G_WimpDrvs_Info(), vaddr1, new_pid)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
            globals4 == global_write_word(globals3, G_WimpDrvs_Info(), vaddr1, new_do_pbase)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
            globals5 == global_write_word(globals4, G_WimpDrvs_Info(), vaddr1, new_do_pend)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            globals6 == global_write_word(globals5, G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Complete)

    requires new_globals == globals6

    ensures wimpdrv_info_newvalue(old_globals, new_globals, slot, new_wimpdrv_id, new_pid, new_do_pbase, new_do_pend, WimpDrv_Slot_UpdateFlag_Complete)
{
    lemma_DistinctGlobals();

    // Prove global_read_fullval(check_globals5, G_WimpDrvs_Info()) == global_read_fullval(check_globals5, G_WimpDrvs_Info())
    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
    var vaddr3 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
    var vaddr4 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
    var vaddr5 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;

    var check_globals1 := global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_wimpdrv_id);
    var check_globals2 := global_write_word(check_globals1, G_WimpDrvs_Info(), vaddr2, new_pid);
    var check_globals3 := global_write_word(check_globals2, G_WimpDrvs_Info(), vaddr3, new_do_pbase);
    var check_globals4 := global_write_word(check_globals3, G_WimpDrvs_Info(), vaddr4, new_do_pend);
    var check_globals5 := global_write_word(check_globals4, G_WimpDrvs_Info(), vaddr5, WimpDrv_Slot_UpdateFlag_Complete);

    assert wimpdrv_get_slot(check_globals5, slot) == wimpdrv_get_slot(new_globals, slot);
    assert forall i :: 0 <= i < WimpDrv_Info_ENTRIES
            ==> wimpdrv_get_slot(check_globals5, i) == wimpdrv_get_slot(new_globals, i);

    assert global_read_fullval(new_globals, G_WimpDrvs_Info()) == global_read_fullval(check_globals5, G_WimpDrvs_Info());

    // Prove equivilant
    assert new_globals == check_globals5;
}

// Lemma: If an operation updates all fields of a slot in <g_wimpdrvs_info> correctly, then that operation satisfies
// wimpdrv_info_newvalue
lemma Lemma_WK_WimpDrvs_UpdateAllFieldsMustSatisfy_wimpdrv_info_newvalue2(
    old_globals:globalsmap, new_globals:globalsmap, 
    slot:uint32, new_wimpdrv_id:uint32, new_pid:uint32, new_do_pbase:paddr, new_do_pend:paddr, 
    globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, globals4:globalsmap, globals5:globalsmap, globals6:globalsmap
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)
    requires WK_ValidGlobalVars_Decls(globals4)
    requires WK_ValidGlobalVars_Decls(globals5)
    requires WK_ValidGlobalVars_Decls(globals6)

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) 

    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            globals1 == global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Updating)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
            globals2 == global_write_word(globals1, G_WimpDrvs_Info(), vaddr1, new_pid)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
            globals3 == global_write_word(globals2, G_WimpDrvs_Info(), vaddr1, new_wimpdrv_id)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
            globals4 == global_write_word(globals3, G_WimpDrvs_Info(), vaddr1, new_do_pbase)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
            globals5 == global_write_word(globals4, G_WimpDrvs_Info(), vaddr1, new_do_pend)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            globals6 == global_write_word(globals5, G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Complete)

    requires new_globals == globals6

    ensures wimpdrv_info_newvalue(old_globals, new_globals, slot, new_wimpdrv_id, new_pid, new_do_pbase, new_do_pend, WimpDrv_Slot_UpdateFlag_Complete)
{
    lemma_DistinctGlobals();

    // Prove global_read_fullval(check_globals5, G_WimpDrvs_Info()) == global_read_fullval(check_globals5, G_WimpDrvs_Info())
    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
    var vaddr3 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
    var vaddr4 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
    var vaddr5 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;

    var check_globals1 := global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_wimpdrv_id);
    var check_globals2 := global_write_word(check_globals1, G_WimpDrvs_Info(), vaddr2, new_pid);
    var check_globals3 := global_write_word(check_globals2, G_WimpDrvs_Info(), vaddr3, new_do_pbase);
    var check_globals4 := global_write_word(check_globals3, G_WimpDrvs_Info(), vaddr4, new_do_pend);
    var check_globals5 := global_write_word(check_globals4, G_WimpDrvs_Info(), vaddr5, WimpDrv_Slot_UpdateFlag_Complete);

    assert wimpdrv_get_slot(check_globals5, slot) == wimpdrv_get_slot(new_globals, slot);
    assert forall i :: 0 <= i < WimpDrv_Info_ENTRIES
            ==> wimpdrv_get_slot(check_globals5, i) == wimpdrv_get_slot(new_globals, i);

    assert global_read_fullval(new_globals, G_WimpDrvs_Info()) == global_read_fullval(check_globals5, G_WimpDrvs_Info());

    // Prove equivilant
    assert new_globals == check_globals5;
}

lemma Lemma_wimpdrv_info_newvalue_ProveOtherWimpDrvSlotsAreUnmodified(
    old_globals:globalsmap, new_globals:globalsmap, slot:uint32, new_wimpdrv_id:uint32, new_wimpdrv_pid:uint32, new_do_pbase:paddr, new_do_pend:paddr, new_flag:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    
    requires wimpdrv_info_newvalue(old_globals, new_globals, slot, new_wimpdrv_id, new_wimpdrv_pid, new_do_pbase, new_do_pend, new_flag)

    ensures forall i :: wimpdrv_valid_slot_id(i) && i != slot
                ==> p_wimpdrv_slot_equal(old_globals, new_globals, i)
        // Requirement: Other wimp driver slots are unmodified
{
    reveal p_wimpdrv_slot_equal();

    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
    var vaddr3 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
    var vaddr4 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
    var vaddr5 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;

    var globals1 := global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_wimpdrv_id);
    var globals2 := global_write_word(globals1, G_WimpDrvs_Info(), vaddr2, new_wimpdrv_pid);
    var globals3 := global_write_word(globals2, G_WimpDrvs_Info(), vaddr3, new_do_pbase);
    var globals4 := global_write_word(globals3, G_WimpDrvs_Info(), vaddr4, new_do_pend);
    var globals5 := global_write_word(globals4, G_WimpDrvs_Info(), vaddr5, new_flag);

    assert new_globals == globals5;
}

lemma Lemma_wimpdrv_info_newvalue_ProveOtherGVarsAreUnmodified(
    old_globals:globalsmap, new_globals:globalsmap, slot:uint32, new_wimpdrv_id:uint32, new_wimpdrv_pid:uint32, new_do_pbase:paddr, new_do_pend:paddr, new_flag:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    
    requires wimpdrv_info_newvalue(old_globals, new_globals, slot, new_wimpdrv_id, new_wimpdrv_pid, new_do_pbase, new_do_pend, new_flag)

    ensures globals_other_gvar_unchanged(old_globals, new_globals, G_WimpDrvs_Info())
        // Requirement: Other global variables are unchanged
{
    reveal p_wimpdrv_slot_equal();

    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
    var vaddr3 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
    var vaddr4 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
    var vaddr5 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;

    var globals1 := global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_wimpdrv_id);
    var globals2 := global_write_word(globals1, G_WimpDrvs_Info(), vaddr2, new_wimpdrv_pid);
    var globals3 := global_write_word(globals2, G_WimpDrvs_Info(), vaddr3, new_do_pbase);
    var globals4 := global_write_word(globals3, G_WimpDrvs_Info(), vaddr4, new_do_pend);
    var globals5 := global_write_word(globals4, G_WimpDrvs_Info(), vaddr5, new_flag);

    assert new_globals == globals5;
}

// Lemma: After writting <do_paddr_end> field of a slot, the new global variable satisfies 
// WK_ValidObjAddrs_WimpDrv_DOPAddrs
lemma Lemma__wimpdrv_update_slot_pid_to_valid_Prove_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToComplete(
    s:state, s':state, new_globals:globalsmap, slot:word, new_do_pbase:word, new_do_pend:uint
)
    requires ValidState(s)
    
    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Complete)
        // Requirement: Only the wimp driver's do_paddr_end is changing
    requires wimpdrv_get_pid(wkm_get_globals(s'.wk_mstate), slot) != WS_PartitionID(PID_INVALID)
    requires wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), slot) != WimpDrv_ID_RESERVED_EMPTY
        // Requirement: The given wimp driver slot is being modified to a ID word not equal to WimpDrv_ID_RESERVED_EMPTY
    requires wimpdrv_do_get_paddr_base(wkm_get_globals(s'.wk_mstate), slot) == new_do_pbase
    requires wimpdrv_do_get_paddr_end(wkm_get_globals(s'.wk_mstate), slot) == new_do_pend

    requires var registered_drv_idword := wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), slot);
             var registered_drv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, registered_drv_idword);
             registered_drv_id in s.subjects.wimp_drvs

    requires var registered_drv_idword := wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), slot);
             var registered_drv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, registered_drv_idword);
             var wimpdrv_do_id := s'.subjects.wimp_drvs[registered_drv_id].do_id;
             WSM_IsWimpDrvDOID(s'.objects, wimpdrv_do_id) &&
             (forall pmem :: pmem in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                    ==> (new_do_pbase == pmem.paddr_start && new_do_pend == pmem.paddr_end))
        // Requirement: As <this.subjects> and <this.objects> have given all wimp drivers to be loaded and their DO's
        // information, <new_do_pbase> and <new_do_pend> must match these information

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, new_globals)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall i | wimpdrv_valid_slot_id(i) && 
            wimpdrv_do_get_flag(globals', i) == WimpDrv_Slot_UpdateFlag_Complete &&
            wimpdrv_get_pid(globals', i) != WS_PartitionID(PID_INVALID)
        ensures (
                var drv_id_word:word := wimpdrv_get_id_word(globals', i);
                var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);
                WSM_IsWimpDrvID(subjs', drv_id) &&
                    // Such active wimp driver must exist in the system
                var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
                var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;
                pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))}
                    // And its address stored in the global variable must match its spec in <objs_addrs'>
            )
    {
        var drv_id_word:word := wimpdrv_get_id_word(globals', i);
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);

        if(i != slot)
        {
            assert WSM_IsWimpDrvID(subjs', drv_id);

            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
            var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;

            assert pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))};
        }
        else
        {
            assert i == slot;
            assert wimpdrv_do_get_paddr_base(globals', slot) == new_do_pbase;
            assert wimpdrv_do_get_paddr_end(globals', slot) == new_do_pend;

            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
            var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;

            // Prove |objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs| == 1
            reveal WK_ValidObjsAddrs();
            assert |objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs| == 1;

            assert pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))};
        }
    }
}

// Lemma: After writting <do_paddr_end> field of a slot, the new global variable satisfies 
// WK_ValidObjAddrs_WimpDrv_DOPAddrs
lemma Lemma__wimpdrv_update_slot_pid_to_invalid_Prove_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToComplete(
    s:state, s':state, new_globals:globalsmap, slot:word
)
    requires ValidState(s)
    
    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires s' == s.(wk_mstate := s.wk_mstate.(globals := new_globals))

    requires wimpdrv_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1) &&
            new_globals == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info(), vaddr1, WimpDrv_Slot_UpdateFlag_Complete)
        // Requirement: Only the wimp driver's do_paddr_end is changing
    requires wimpdrv_get_pid(wkm_get_globals(s'.wk_mstate), slot) == WS_PartitionID(PID_INVALID)
        // Requirement: The given wimp driver slot is being modified to be inactive

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, new_globals)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall i | wimpdrv_valid_slot_id(i) && 
            wimpdrv_do_get_flag(globals', i) == WimpDrv_Slot_UpdateFlag_Complete &&
            wimpdrv_get_pid(globals', i) != WS_PartitionID(PID_INVALID)
        ensures (
                var drv_id_word:word := wimpdrv_get_id_word(globals', i);
                var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);
                WSM_IsWimpDrvID(subjs', drv_id) &&
                    // Such active wimp driver must exist in the system
                var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
                var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;
                pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))}
                    // And its address stored in the global variable must match its spec in <objs_addrs'>
            )
    {
        var drv_id_word:word := wimpdrv_get_id_word(globals', i);
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', drv_id_word);

        if(i != slot)
        {
            assert WSM_IsWimpDrvID(subjs', drv_id);

            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs', objs', id_mappings', drv_id_word);
            var pmem := objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs;

            assert pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals', i), wimpdrv_do_get_paddr_end(globals', i))};
        }
        else
        {
            assert i == slot;
        }
    }
}

// Lemma: For the function <_wimpdrv_update_slot_pid_to_valid>, Prove the result state satisfies
// WK_SecureObjsAddrs_MemSeparation
lemma Lemma__wimpdrv_update_slot_pid_to_valid_Prove_WK_SecureObjsAddrs_MemSeparation(
    s:state, s':state, wimpdrv_slot:uint32, new_do_pbase:word, new_do_pend:uint
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: OS objects have unchanged PID
    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires forall i:uint32 :: wimpdrv_valid_slot_id(i) && i != wimpdrv_slot
        ==> p_wimpdrv_slot_equal(wkm_get_globals(s.wk_mstate), wkm_get_globals(s'.wk_mstate), i)
        // Requirement: Other wimp driver slots are unchanged
    requires WK_ValidPMemRegion(new_do_pbase, new_do_pend)
    requires WimpDrvDO_MemRegionSeparateFromAllActiveOSObjs(s.objects, s.objs_addrs, new_do_pbase, new_do_pend)
        // Requirement: The given memory region [do_pbase, do_pend) is not overlap with any active OS objects
    requires wimpdrv_get_pid(wkm_get_globals(s'.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
    requires wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot) == WimpDrv_ID_RESERVED_EMPTY
    requires wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), wimpdrv_slot) != WimpDrv_ID_RESERVED_EMPTY
        // Requirement: The given wimp driver slot contains WimpDrv_ID_RESERVED_EMPTY before, and is being modified to a 
        // ID word not equal to WimpDrv_ID_RESERVED_EMPTY
    requires wimpdrv_do_get_paddr_base(wkm_get_globals(s'.wk_mstate), wimpdrv_slot) == new_do_pbase
    requires wimpdrv_do_get_paddr_end(wkm_get_globals(s'.wk_mstate), wimpdrv_slot) == new_do_pend

    requires var registered_drv_idword := wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), wimpdrv_slot);
             var registered_drv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, registered_drv_idword);
             registered_drv_id in s.subjects.wimp_drvs

    requires var registered_drv_idword := wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), wimpdrv_slot);
             var registered_drv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, registered_drv_idword);
             var wimpdrv_do_id := s'.subjects.wimp_drvs[registered_drv_id].do_id;
             WSM_IsWimpDrvDOID(s'.objects, wimpdrv_do_id) &&
             (forall pmem :: pmem in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                    ==> (new_do_pbase == pmem.paddr_start && new_do_pend == pmem.paddr_end))
        // Requirement: As <this.subjects> and <this.objects> have given all wimp drivers to be loaded and their DO's
        // information, <new_do_pbase> and <new_do_pend> must match these information

    requires forall i:uint32 :: wimpdrv_valid_slot_id(i) && i != wimpdrv_slot && 
                wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), i) == WimpDrv_Slot_UpdateFlag_Complete &&
                wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), i) != WS_PartitionID(PID_INVALID)
            ==> !is_mem_region_overlap(wimpdrv_do_get_paddr_base(wkm_get_globals(s.wk_mstate), i), wimpdrv_do_get_paddr_end(wkm_get_globals(s.wk_mstate), i), 
                    new_do_pbase, new_do_pend)
        // Requirement: The DO paddr region of the new wimp driver does not overlap with existing submitted wimp drivers.
        // In other words, DOs of active wimp drivers do not overlap with each other

    ensures WK_SecureObjsAddrs_MemSeparation(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_SecureObjsAddrs_MemSeparation();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    var registered_drv_idword := wimpdrv_get_id_word(globals', wimpdrv_slot);
    var registered_drv_id := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, registered_drv_idword);

    assert registered_drv_id == WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', registered_drv_idword);

    // Prove all wimp drivers' PID except the wimp drivers <registered_drv_id> are unchanged
    Lemma__wimpdrv_update_slot_pid_to_valid_Prove_WK_SecureObjsAddrs_MemSeparation_ProveOtherWimpDrvPIDIsUnchanged(
        s, s', wimpdrv_slot, new_do_pbase, new_do_pend);
    
    forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSTDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS TD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsWimpDrvDO(s'.objects, wimpdrv_do_id.oid);
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, wimpdrv_do_id.oid);

        assert WSM_IsOSTDID(objs, os_obj_id) == WSM_IsOSTDID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);

        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, wimpdrv_do_id.oid);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, wimpdrv_do_id.oid);

        if(drv_id != registered_drv_id)
        {
            reveal p_wimpdrv_slot_equal();
            assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
        else
        {
            assert pmem2.paddr_start == new_do_pbase;
            assert pmem2.paddr_end == new_do_pend;
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
    }

    forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSFDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsWimpDrvDO(s'.objects, wimpdrv_do_id.oid);
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, wimpdrv_do_id.oid);

        assert WSM_IsOSFDID(objs, os_obj_id) == WSM_IsOSFDID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);

        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, wimpdrv_do_id.oid);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, wimpdrv_do_id.oid);

        if(drv_id != registered_drv_id)
        {
            reveal p_wimpdrv_slot_equal();
            assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
        else
        {
            assert pmem2.paddr_start == new_do_pbase;
            assert pmem2.paddr_end == new_do_pend;
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
    }

    forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSDOID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsWimpDrvDO(s'.objects, wimpdrv_do_id.oid);
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, wimpdrv_do_id.oid);

        assert WSM_IsOSDOID(objs, os_obj_id) == WSM_IsOSDOID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);

        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, wimpdrv_do_id.oid);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, wimpdrv_do_id.oid);

        if(drv_id != registered_drv_id)
        {
            reveal p_wimpdrv_slot_equal();
            assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
        else
        {
            assert pmem2.paddr_start == new_do_pbase;
            assert pmem2.paddr_end == new_do_pend;
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
    }

    forall i, j | wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            i != j
        ensures WK_WimpDrv_DOMustNotOverlapWithEachOther(globals', i, j)
    {
        if(i == wimpdrv_slot && j != wimpdrv_slot)
        {
            assert p_wimpdrv_slot_equal(globals, globals', j);
            reveal p_wimpdrv_slot_equal();
            assert WK_WimpDrv_DOMustNotOverlapWithEachOther(globals', i, j);
        }
        else if (j == wimpdrv_slot && i != wimpdrv_slot)
        {
            assert p_wimpdrv_slot_equal(globals, globals', i);
            reveal p_wimpdrv_slot_equal();
            assert WK_WimpDrv_DOMustNotOverlapWithEachOther(globals', i, j);
        }
        else
        {
            assert p_wimpdrv_slot_equal(globals, globals', i);
            assert p_wimpdrv_slot_equal(globals, globals', j);
            reveal p_wimpdrv_slot_equal();

            assert wimpdrv_do_get_paddr_base(globals, i) == wimpdrv_do_get_paddr_base(globals', i);
            assert wimpdrv_do_get_paddr_end(globals, i) == wimpdrv_do_get_paddr_end(globals', i);
            assert wimpdrv_do_get_paddr_base(globals, j) == wimpdrv_do_get_paddr_base(globals', j);
            assert wimpdrv_do_get_paddr_end(globals, j) == wimpdrv_do_get_paddr_end(globals', j);

            assert wimpdrv_get_pid(globals, i) == wimpdrv_get_pid(globals', i);
            assert wimpdrv_get_pid(globals, j) == wimpdrv_get_pid(globals', j);
            assert wimpdrv_do_get_flag(globals, i) == wimpdrv_do_get_flag(globals', i);
            assert wimpdrv_do_get_flag(globals, j) == wimpdrv_do_get_flag(globals', j);

            assert WK_WimpDrv_DOMustNotOverlapWithEachOther(globals, i, j);
        }
    }
}

// Lemma: For the function <_wimpdrv_update_slot_pid_to_invalid>, Prove the result state satisfies
// WK_SecureObjsAddrs_MemSeparation
lemma Lemma__wimpdrv_update_slot_pid_to_invalid_Prove_WK_SecureObjsAddrs_MemSeparation(
    s:state, s':state, wimpdrv_slot:uint32
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires s.objects == s'.objects
        // Requirement: These state variables are unchanged
    requires forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: OS objects have unchanged PID
    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires forall i:uint32 :: wimpdrv_valid_slot_id(i) && i != wimpdrv_slot
        ==> p_wimpdrv_slot_equal(wkm_get_globals(s.wk_mstate), wkm_get_globals(s'.wk_mstate), i)
        // Requirement: Other wimp driver slots are unchanged
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
    requires wimpdrv_get_pid(wkm_get_globals(s'.wk_mstate), wimpdrv_slot) == WS_PartitionID(PID_INVALID)
    requires wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), wimpdrv_slot) == WimpDrv_ID_RESERVED_EMPTY
    requires wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WimpDrv_ID_RESERVED_EMPTY
        // Requirement: The given wimp driver slot contains WimpDrv_ID_RESERVED_EMPTY before, and is being modified to a 
        // ID word not equal to WimpDrv_ID_RESERVED_EMPTY

    requires var unregistered_drv_idword := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             var unregistered_drv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, unregistered_drv_idword);
             unregistered_drv_id in s.subjects.wimp_drvs

    ensures WK_SecureObjsAddrs_MemSeparation(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    var unregistered_drv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var unregistered_drv_id := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, unregistered_drv_idword);

    assert unregistered_drv_id in subjs.wimp_drvs;
    assert unregistered_drv_id == WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', unregistered_drv_idword);

    // Prove WSM_SubjPID(subjs', objs', id_mappings', globals', unregistered_drv_id.sid) == WS_PartitionID(PID_INVALID)
    assert WK_WimpDrvs_ValidGlobalVarValues_IDWords(globals');
    if(wimpdrv_idword_in_record(globals', unregistered_drv_idword))
    {
        reveal p_wimpdrv_slot_equal();
        assert false;
    }
    assert !wimpdrv_idword_in_record(globals', unregistered_drv_idword);

    Lemma_WimpDrv_DrvID_ToIDWord_ProveCorrectness(subjs', objs', id_mappings', unregistered_drv_idword, unregistered_drv_id);
    assert WSM_SubjPID(subjs', objs', id_mappings', globals', unregistered_drv_id.sid) == WS_PartitionID(PID_INVALID);

    // Prove all wimp drivers' PID except the wimp drivers <unregistered_drv_id> are unchanged
    Lemma__wimpdrv_update_slot_pid_to_invalid_Prove_WK_SecureObjsAddrs_MemSeparation_ProveOtherWimpDrvPIDIsUnchanged(
        s, s', wimpdrv_slot);
    
    forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSTDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS TD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsWimpDrvDO(s'.objects, wimpdrv_do_id.oid);
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, wimpdrv_do_id.oid);

        assert WSM_IsOSTDID(objs, os_obj_id) == WSM_IsOSTDID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);

        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, wimpdrv_do_id.oid);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, wimpdrv_do_id.oid);
        
        assert WSM_SubjPID(subjs', objs', id_mappings', globals', drv_id.sid) != WS_PartitionID(PID_INVALID);

        // So drv_id != unregistered_drv_id
        assert drv_id != unregistered_drv_id;
        reveal p_wimpdrv_slot_equal();
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
        assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

    } 

    forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSFDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsWimpDrvDO(s'.objects, wimpdrv_do_id.oid);
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, wimpdrv_do_id.oid);

        assert WSM_IsOSFDID(objs, os_obj_id) == WSM_IsOSFDID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);

        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, wimpdrv_do_id.oid);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, wimpdrv_do_id.oid);

        // So drv_id != unregistered_drv_id
        assert drv_id != unregistered_drv_id;
        reveal p_wimpdrv_slot_equal();
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
        assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
    }

    forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSDOID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsWimpDrvDO(s'.objects, wimpdrv_do_id.oid);
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, wimpdrv_do_id.oid);

        assert WSM_IsOSDOID(objs, os_obj_id) == WSM_IsOSDOID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);

        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, wimpdrv_do_id.oid);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, wimpdrv_do_id.oid);

        // So drv_id != unregistered_drv_id
        assert drv_id != unregistered_drv_id;
        reveal p_wimpdrv_slot_equal();
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
        assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
    }

    forall i, j | wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            i != j
        ensures WK_WimpDrv_DOMustNotOverlapWithEachOther(globals', i, j)
    {
        if(i == wimpdrv_slot && j != wimpdrv_slot)
        {
            assert p_wimpdrv_slot_equal(globals, globals', j);
            reveal p_wimpdrv_slot_equal();
            assert WK_WimpDrv_DOMustNotOverlapWithEachOther(globals', i, j);
        }
        else if (j == wimpdrv_slot && i != wimpdrv_slot)
        {
            assert p_wimpdrv_slot_equal(globals, globals', i);
            reveal p_wimpdrv_slot_equal();
            assert WK_WimpDrv_DOMustNotOverlapWithEachOther(globals', i, j);
        }
        else
        {
            assert p_wimpdrv_slot_equal(globals, globals', i);
            assert p_wimpdrv_slot_equal(globals, globals', j);
            reveal p_wimpdrv_slot_equal();
        }
    }
}




/*********************** Lemma for <g_existing_pids> Modification  ********************/
// Lemma: When replacing partition ID in <g_existing_pids>, if the old partition has no wimp drivers, and 
// WK_WimpDrvs_ValidGlobalVarValues_PIDs(old_globals), Then WK_WimpDrvs_ValidGlobalVarValues_PIDs(new_globals)
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfOverwritePIDOfPartitionHavingNoWimpDrvs(
    old_globals:globalsmap, new_globals:globalsmap, pid_vaddr:vaddr, old_pid:word, new_pid:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires is_valid_vaddr(pid_vaddr)
    requires is_gvar_valid_vaddr(G_Existing_PIDs(), pid_vaddr)
    requires !pids_is_os_pid(new_pid)
        // Requirement: <new_pid> must not be the OS partition's PID
    requires forall pid:WS_PartitionID :: pid in pids_parse_g_wimp_pids(old_globals)
            ==> (pid.v != new_pid)
        // Requirement: <new_pid> is new
    requires forall i:int :: (0 <= i < WimpDrv_Info_ENTRIES)
            ==> (wimpdrv_get_pid(old_globals, i) == WS_PartitionID(PID_INVALID) ||
                wimpdrv_get_pid(old_globals, i) != WS_PartitionID(old_pid));
        // Requirement: The partition of the overwritten PID must do not contain any wimp driver

    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(old_globals)
    requires new_globals == global_write_word(old_globals, G_Existing_PIDs(), pid_vaddr, new_pid)
    requires old_pid == global_read_word(old_globals, G_Existing_PIDs(), pid_vaddr)
    
    ensures WK_WimpDrvs_ValidGlobalVarValues_PIDs(new_globals)
{
    assert forall i :: 0 <= i < WimpDrv_Info_ENTRIES
        ==> wimpdrv_get_pid(old_globals, i) == wimpdrv_get_pid(new_globals, i);

    forall i | 0 <= i < WimpDrv_Info_ENTRIES
        ensures wimpdrv_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) ||
                wimpdrv_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals)
    {
        var old_pid_i := wimpdrv_get_pid(old_globals, i);
        var new_pid_i := wimpdrv_get_pid(new_globals, i);

        assert old_pid_i == new_pid_i;

        if(new_pid_i != WS_PartitionID(PID_INVALID))
        {
            Lemma_pids_parse_g_wimp_pids_CorrectnessOfSetChange(old_globals, new_globals, pid_vaddr, old_pid, new_pid);
            assert pids_parse_g_wimp_pids(new_globals) == pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)} + {WS_PartitionID(new_pid)} ||
                   pids_parse_g_wimp_pids(new_globals) == pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)};

            assert old_pid_i in pids_parse_g_wimp_pids(new_globals);
        }
    }
}




/*********************** Other Lemmas  ********************/
lemma Lemma_wimpdrv_info_slot_in_range_must_be_valid_vaddr(base:addr, i:int) 
    requires base == AddressOfGlobal(G_WimpDrvs_Info())
    requires 0 <= i < WimpDrv_Info_ENTRIES

    ensures is_valid_addr(base + i * WimpDrv_Info_ENTRY_SZ)
    ensures is_valid_vaddr(base + i * WimpDrv_Info_ENTRY_SZ)
    ensures is_gvar_valid_vaddr(G_WimpDrvs_Info(), base + i * WimpDrv_Info_ENTRY_SZ)
    ensures ValidGlobalOffset(G_WimpDrvs_Info(), i * WimpDrv_Info_ENTRY_SZ)
{
    Lemma_NatMul_Ineq_4var(i, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
    assert isUInt32(i * WimpDrv_Info_ENTRY_SZ);

    assert 0 <= i < WimpDrv_Info_ENTRIES;
    var offset := i * WimpDrv_Info_ENTRY_SZ;
    Lemma_NatMul_Ineq_NoEqualRight(i, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
    assert 0 <= offset < WimpDrv_Info_ENTRIES * WimpDrv_Info_ENTRY_SZ;

    Lemma_NTimesUInt32IsStillAligned(i, WimpDrv_Info_ENTRY_SZ);
    assert WordAligned(i * WimpDrv_Info_ENTRY_SZ);
    
    lemma_DistinctGlobals();
    assert ValidGlobalOffset(G_WimpDrvs_Info(), offset);
}

// Lemma: When modifying one WimpDrv slot, other slots are unmodified
lemma Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires wimpdrv_valid_slot_id(slot)
    requires 0 <= offset < WimpDrv_Info_ENTRY_SZ
    requires var vaddr := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_WimpDrvs_Info(), vaddr) &&
            globals2 == global_write_word(globals1, G_WimpDrvs_Info(), vaddr, new_v)

    ensures forall i:uint32 :: wimpdrv_valid_slot_id(i) && i != slot
        ==> p_wimpdrv_slot_equal(globals1, globals2, i)
{
    reveal p_wimpdrv_slot_equal();

    forall i | 0 <= i < WimpDrv_Info_ENTRIES && i != slot
        ensures p_wimpdrv_slot_equal(globals1, globals2, i)
    {    
        if(wimpdrv_get_id_word(globals1, i) != wimpdrv_get_id_word(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + i * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
            assert global_read_word(globals1, G_WimpDrvs_Info(), vaddr1) != global_read_word(globals2, G_WimpDrvs_Info(), vaddr1);
            assert i * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset == slot * WimpDrv_Info_ENTRY_SZ + offset;
            assert false;
        }
        assert wimpdrv_get_id_word(globals1, i) == wimpdrv_get_id_word(globals2, i);
    }
}

// Lemma: If G_USBTD_MAP_MEM, G_WimpUSBPDev_Info are unchanged, and no USB TD is associated with the given <wimpdrv_slot>,  
// then <WK_USBTD_Map_SecureGlobalVarValues> holds
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingWimpDrvNotAssociatedWithAnyUSBTD(globals1:globalsmap, globals2:globalsmap, wimpdrv_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires usbtds_verifiedtds_do_not_associate_wimpdrv(globals1, wimpdrv_slot)
        // Requirement: No USB TD is associated with the given <wimpdrv_slot>
    
    requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    requires forall i:uint32 :: wimpdrv_valid_slot_id(i) && i != wimpdrv_slot
        ==> p_wimpdrv_slot_equal(globals1, globals2, i)
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(globals2)
{
    reveal usbtds_verifiedtds_do_not_associate_wimpdrv();
    reveal p_wimpdrv_slot_equal();
    
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, i);


        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qTD32_Properties(globals1, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, i);
        assert wimpdrv_valid_slot_id(drv_slot);
        assert p_wimpdrv_slot_equal(globals1, globals2, drv_slot);

        Lemma_SameUSBTDMem_Property(globals1, globals2);
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(globals1, globals2, i);
    }

    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QH32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, i);


        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qh32_Properties(globals1, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, i);
        assert wimpdrv_valid_slot_id(drv_slot);
        assert p_wimpdrv_slot_equal(globals1, globals2, drv_slot);

        Lemma_SameUSBTDMem_Property(globals1, globals2);
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(globals1, globals2, i);
    }

    // [TODO] Not support iTD and siTD yet
    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_iTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_iTD32(globals2, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_iTD32(globals1, i);


        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_iTD32_Properties(globals1, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_iTD32(globals1, i);
        assert wimpdrv_valid_slot_id(drv_slot);
        assert p_wimpdrv_slot_equal(globals1, globals2, drv_slot);
    }

    // [TODO] Not support iTD and siTD yet
    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_siTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_siTD32(globals2, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_siTD32(globals1, i);


        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_siTD32_Properties(globals1, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_siTD32(globals1, i);
        assert wimpdrv_valid_slot_id(drv_slot);
        assert p_wimpdrv_slot_equal(globals1, globals2, drv_slot);
    }
}

// Lemma: In a valid state, if a wimp driver is registered and active, then the driver must exist in 
// <s.subjects.wimp_drvs>
lemma Lemma_wimpdrv_registed_and_active_must_exist_in_system(s:state, wimpdrv_slot:word)
    requires ValidState(s)
    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete &&
             wimpdrv_get_pid(globals, wimpdrv_slot) != WS_PartitionID(PID_INVALID)

    ensures var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
        // Requirement: The wimp driver being accessed must exist in the system
{
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();
}




/*********************** Private Lemmas  ********************/
// Lemma: After <_wimpdrv_update_slot_pid_to_valid> is done, all wimp drivers' PIDs (except the new registed driver) is
// unchanged
lemma Lemma__wimpdrv_update_slot_pid_to_valid_Prove_WK_SecureObjsAddrs_MemSeparation_ProveOtherWimpDrvPIDIsUnchanged(
    s:state, s':state, wimpdrv_slot:uint32, new_do_pbase:word, new_do_pend:uint
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: OS objects have unchanged PID
    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires forall i:uint32 :: wimpdrv_valid_slot_id(i) && i != wimpdrv_slot
        ==> p_wimpdrv_slot_equal(wkm_get_globals(s.wk_mstate), wkm_get_globals(s'.wk_mstate), i)
        // Requirement: Other wimp driver slots are unchanged
    requires WK_ValidPMemRegion(new_do_pbase, new_do_pend)
    requires WimpDrvDO_MemRegionSeparateFromAllActiveOSObjs(s.objects, s.objs_addrs, new_do_pbase, new_do_pend)
        // Requirement: The given memory region [do_pbase, do_pend) is not overlap with any active OS objects
    requires wimpdrv_get_pid(wkm_get_globals(s'.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
    requires wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot) == WimpDrv_ID_RESERVED_EMPTY
    requires wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), wimpdrv_slot) != WimpDrv_ID_RESERVED_EMPTY
        // Requirement: The given wimp driver slot contains WimpDrv_ID_RESERVED_EMPTY before, and is being modified to a 
        // ID word not equal to WimpDrv_ID_RESERVED_EMPTY

    ensures var registered_drv_idword := wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), wimpdrv_slot);
            var registered_drv_id := WimpDrv_IDWord_ToDrvID(s'.subjects, s'.objects, s'.id_mappings, registered_drv_idword);
            forall id:Drv_ID :: WSM_IsWimpDrvID(s.subjects, id) && id != registered_drv_id
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid) == 
                    WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.sid)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    var registered_drv_idword := wimpdrv_get_id_word(globals', wimpdrv_slot);
    var registered_drv_id := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, registered_drv_idword);

    assert registered_drv_id == WimpDrv_IDWord_ToDrvID(subjs', objs', id_mappings', registered_drv_idword);

    // Prove all wimp drivers' PID except the wimp drivers <unregistered_drv_id> and <registered_drv_id> are unchanged
    forall id:Drv_ID | WSM_IsWimpDrvID(subjs, id) && id != registered_drv_id
        ensures WSM_SubjPID(subjs, objs, id_mappings, globals, id.sid) == WSM_SubjPID(subjs', objs', id_mappings', globals', id.sid)
    {
        var drv_id_word := WimpDrv_DrvID_ToIDWord(subjs, objs, id_mappings, id);
        reveal p_wimpdrv_slot_equal();

        if(wimpdrv_idword_in_record(globals, drv_id_word))
        {
            var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);

            // Prove p_wimpdrv_slot_equal(globals, globals', dev_slot)
            assert drv_slot != wimpdrv_slot;
            assert p_wimpdrv_slot_equal(globals, globals', drv_slot);
        }
        else
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID);

            // Prove !wimpdrv_idword_in_record(globals', drv_id_word)
            assert !wimpdrv_idword_in_record(globals', drv_id_word);
            assert WSM_SubjPID(subjs', objs', id_mappings', globals', id.sid) == WS_PartitionID(PID_INVALID);
        }
    }
}

// Lemma: After <_wimpdrv_update_slot_pid_to_invalid> is done, all wimp drivers' PIDs (except the unregisted driver) is
// unchanged
lemma Lemma__wimpdrv_update_slot_pid_to_invalid_Prove_WK_SecureObjsAddrs_MemSeparation_ProveOtherWimpDrvPIDIsUnchanged(
    s:state, s':state, wimpdrv_slot:uint32
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: OS objects have unchanged PID
    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires forall i:uint32 :: wimpdrv_valid_slot_id(i) && i != wimpdrv_slot
        ==> p_wimpdrv_slot_equal(wkm_get_globals(s.wk_mstate), wkm_get_globals(s'.wk_mstate), i)
        // Requirement: Other wimp driver slots are unchanged
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
    requires wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), wimpdrv_slot) == WimpDrv_ID_RESERVED_EMPTY
    requires wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WimpDrv_ID_RESERVED_EMPTY
        // Requirement: The given wimp driver slot contains WimpDrv_ID_RESERVED_EMPTY before, and is being modified to a 
        // ID word not equal to WimpDrv_ID_RESERVED_EMPTY

    ensures var unregistered_drv_idword := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var unregistered_drv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, unregistered_drv_idword);
            forall id:Drv_ID :: WSM_IsWimpDrvID(s.subjects, id) && id != unregistered_drv_id
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid) == 
                    WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.sid)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    var unregistered_drv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var unregistered_drv_id := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, unregistered_drv_idword);

    // Prove all wimp drivers' PID except the wimp drivers <unregistered_drv_id> are unchanged
    forall id:Drv_ID | WSM_IsWimpDrvID(subjs, id) && id != unregistered_drv_id
        ensures WSM_SubjPID(subjs, objs, id_mappings, globals, id.sid) == WSM_SubjPID(subjs', objs', id_mappings', globals', id.sid)
    {
        var drv_id_word := WimpDrv_DrvID_ToIDWord(subjs, objs, id_mappings, id);
        reveal p_wimpdrv_slot_equal();

        if(wimpdrv_idword_in_record(globals, drv_id_word))
        {
            var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);

            // Prove p_wimpdrv_slot_equal(globals, globals', dev_slot)
            assert drv_slot != wimpdrv_slot;
            assert p_wimpdrv_slot_equal(globals, globals', drv_slot);
        }
        else
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID);

            // Prove !wimpdrv_idword_in_record(globals', drv_id_word)
            assert !wimpdrv_idword_in_record(globals', drv_id_word);
            assert WSM_SubjPID(subjs', objs', id_mappings', globals', id.sid) == WS_PartitionID(PID_INVALID);
        }
    }
}