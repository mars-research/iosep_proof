include "../arch/headers.dfy"
include "../mm/wk_globals.dfy"
include "../partition_id.s.dfy"

const WimpDrv_ID_RESERVED_EMPTY:uint32 := 0xFFFFFFFF;
const WimpDrv_SlotID_EMPTY:int := 0xFFFFFFFF;


const WimpDrv_Slot_UpdateFlag_Complete:int := 0; // Modifications to the slot is done. Now the slot takes effect.
const WimpDrv_Slot_UpdateFlag_Updating:int := 1; // We are in the middle of updating this slot




/*********************** State Invariants and Related Predicates ********************/
predicate WK_WimpDrvs_ValidGlobalVarValues(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    WK_WimpDrvs_ValidGlobalVarValues_IDWords(globals) &&
    WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals) &&
    WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(globals) &&
    
    (true)
}

predicate WK_WimpDrvs_ValidGlobalVarValues_IDWords(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // Each slot must map to a unique WimpDrv_ID_word, unless it is WimpDrv_ID_RESERVED_EMPTY
    forall i, j :: wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            wimpdrv_get_id_word(globals, i) != WimpDrv_ID_RESERVED_EMPTY && wimpdrv_get_id_word(globals, j) != WimpDrv_ID_RESERVED_EMPTY
        ==> (wimpdrv_get_id_word(globals, i) == wimpdrv_get_id_word(globals, j) <==> i == j)
}

predicate WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // 1. In each slot of WimpDrv info, the PID is either empty or must be a wimp partition's PID
    (forall i :: wimpdrv_valid_slot_id(i)
        ==> (wimpdrv_get_pid(globals, i) == WS_PartitionID(PID_INVALID) || 
            wimpdrv_get_pid(globals, i) in pids_parse_g_wimp_pids(globals))
    ) && 

    // 2. If a WimpDrv has the empty ID, then its PID must be invalid
    (forall i :: wimpdrv_valid_slot_id(i) &&
            wimpdrv_get_id_word(globals, i) == WimpDrv_ID_RESERVED_EMPTY
        ==> wimpdrv_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    ) &&

    (true)
}

predicate WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // 1. In each slot of WimpDrv info, <do_paddr_base> must equal or less than <do_paddr_end>
    (forall i :: wimpdrv_valid_slot_id(i) && 
            wimpdrv_do_get_flag(globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ==> WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(globals, i), wimpdrv_do_get_paddr_end(globals, i))
    ) && 

    (true)
}

predicate WK_ValidPMemRegion(paddr_base:paddr, paddr_end:uint)
{
    paddr_base <= paddr_end
}

// Predicate: DOs of different wimp drivers must not overlap with each other
predicate WK_WimpDrv_DOMustNotOverlapWithEachOther(globals:globalsmap, i:uint32, j:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires (forall i :: wimpdrv_valid_slot_id(i) && 
            wimpdrv_do_get_flag(globals, i) == WimpDrv_Slot_UpdateFlag_Complete
        ==> WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(globals, i), wimpdrv_do_get_paddr_end(globals, i)))

    requires wimpdrv_valid_slot_id(i)
    requires wimpdrv_valid_slot_id(j)
    requires i != j
{
    var do_paddr_base_i := wimpdrv_do_get_paddr_base(globals, i);
    var do_paddr_end_i := wimpdrv_do_get_paddr_end(globals, i);
    var do_paddr_base_j := wimpdrv_do_get_paddr_base(globals, j);
    var do_paddr_end_j := wimpdrv_do_get_paddr_end(globals, j);

    (wimpdrv_get_pid(globals, i) != WS_PartitionID(PID_INVALID) && wimpdrv_get_pid(globals, j) != WS_PartitionID(PID_INVALID) &&
        wimpdrv_do_get_flag(globals, i) == WimpDrv_Slot_UpdateFlag_Complete && (wimpdrv_do_get_flag(globals, j) == WimpDrv_Slot_UpdateFlag_Complete))
        ==> !is_mem_region_overlap(do_paddr_base_i, do_paddr_end_i, do_paddr_base_j, do_paddr_end_j)
}




/*********************** Predicates of Functions and Operations ********************/
// Predicate The wimp driver refered by <slot> must be in <g_usbtd_map_mem>
predicate wimpdrv_valid_slot_id(slot:uint32)
{
    0 <= slot < WimpDrv_Info_ENTRIES
}


// Predicate: Modification to <g_wimpdrvs_info> change the given slot only, care about the new values only
predicate wimpdrv_info_newvalue(
    old_globals:globalsmap, new_globals:globalsmap, slot:uint32, new_wimpdrv_id:uint32, new_wimpdrv_pid:uint32, new_do_pbase:paddr, new_do_pend:paddr, new_flag:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
{
    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
    var vaddr3 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
    var vaddr4 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
    var vaddr5 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;

    var d1 := is_valid_addr(vaddr1) &&
                is_valid_vaddr(vaddr1) &&   
                    // <vaddr1> must be a valid vaddr
                is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1);
                    // <vaddr1> is a valid vaddr in <g_wimpdrvs_info>

    if(d1) then
        var globals1 := global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_wimpdrv_id);
        var globals2 := global_write_word(globals1, G_WimpDrvs_Info(), vaddr2, new_wimpdrv_pid);
        var globals3 := global_write_word(globals2, G_WimpDrvs_Info(), vaddr3, new_do_pbase);
        var globals4 := global_write_word(globals3, G_WimpDrvs_Info(), vaddr4, new_do_pend);
        var globals5 := global_write_word(globals4, G_WimpDrvs_Info(), vaddr5, new_flag);

        new_globals == globals5
    else
        false
}

// Predicate: Modification to <g_wimpdrvs_info> change the given slot only, care about both the old values and new values
predicate wimpdrv_info_oldandnewvalue(
    old_globals:globalsmap, new_globals:globalsmap, slot:uint32, 
    old_wimpdrv_id:uint32, old_wimpdrv_pid:uint32, old_do_pbase:paddr, old_do_pend:paddr, old_flag:word,
    new_wimpdrv_id:uint32, new_wimpdrv_pid:uint32, new_do_pbase:paddr, new_do_pend:paddr, new_flag:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    ensures wimpdrv_info_oldandnewvalue(old_globals, new_globals, slot, 
                old_wimpdrv_id, old_wimpdrv_pid, old_do_pbase, old_do_pend, old_flag,
                new_wimpdrv_id, new_wimpdrv_pid, new_do_pbase, new_do_pend, new_flag)
                ==> wimpdrv_info_newvalue(old_globals, new_globals, slot, new_wimpdrv_id, new_wimpdrv_pid, new_do_pbase, new_do_pend, new_flag)
    ensures wimpdrv_info_oldandnewvalue(old_globals, new_globals, slot, 
                old_wimpdrv_id, old_wimpdrv_pid, old_do_pbase, old_do_pend, old_flag, 
                new_wimpdrv_id, new_wimpdrv_pid, new_do_pbase, new_do_pend, new_flag)
                ==> (wimpdrv_get_id_word(old_globals, slot) == old_wimpdrv_id && wimpdrv_get_pid(old_globals, slot) == WS_PartitionID(old_wimpdrv_pid))
{
    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
    var vaddr3 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
    var vaddr4 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
    var vaddr5 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;

    var d1 := is_valid_addr(vaddr1) &&
                is_valid_vaddr(vaddr1) &&   
                    // <vaddr1> must be a valid vaddr
                is_gvar_valid_vaddr(G_WimpDrvs_Info(), vaddr1);
                    // <vaddr1> is a valid vaddr in <G_WimpDrvs_Info>

    if(d1) then
        var globals1 := global_write_word(old_globals, G_WimpDrvs_Info(), vaddr1, new_wimpdrv_id);
        var globals2 := global_write_word(globals1, G_WimpDrvs_Info(), vaddr2, new_wimpdrv_pid);
        var globals3 := global_write_word(globals2, G_WimpDrvs_Info(), vaddr3, new_do_pbase);
        var globals4 := global_write_word(globals3, G_WimpDrvs_Info(), vaddr4, new_do_pend);
        var globals5 := global_write_word(globals4, G_WimpDrvs_Info(), vaddr5, new_flag);

        new_globals == globals5 &&
        old_wimpdrv_id == global_read_word(old_globals, G_WimpDrvs_Info(), vaddr1) &&
        old_wimpdrv_pid == global_read_word(old_globals, G_WimpDrvs_Info(), vaddr2) &&
        old_do_pbase == global_read_word(old_globals, G_WimpDrvs_Info(), vaddr3) &&
        old_do_pend == global_read_word(old_globals, G_WimpDrvs_Info(), vaddr4) &&
        old_flag == global_read_word(old_globals, G_WimpDrvs_Info(), vaddr5)
    else
        false
}




/*********************** Util Functions ********************/
// Return the <wimp drv ID> field of the given WimpDrv_Info slot in <g_wimpdrvs_info>
function wimpdrv_get_id_word(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires wimpdrv_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
    var drv_id := global_read_word(globals, G_WimpDrvs_Info(), vaddr1);

    drv_id
}

// Return the <pid> field of the given WimpDrv_Info slot in <g_wimpdrvs_info>
function wimpdrv_get_pid(globals:globalsmap, slot:uint32) : WS_PartitionID 
    requires WK_ValidGlobalVars_Decls(globals)
    requires wimpdrv_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
    var pid := global_read_word(globals, G_WimpDrvs_Info(), vaddr1);

    WS_PartitionID(pid)
}

// Return the <do_paddr_base> field of the given WimpDrv_Info slot in <g_wimpdrvs_info>
function wimpdrv_do_get_paddr_base(globals:globalsmap, slot:uint32) : paddr // do_paddr_base:paddr and do_paddr_end:paddr
    requires WK_ValidGlobalVars_Decls(globals)
    requires wimpdrv_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
    var do_pbase := global_read_word(globals, G_WimpDrvs_Info(), vaddr1);

    (do_pbase)
}

// Return the <do_paddr_end> field of the given WimpDrv_Info slot in <g_wimpdrvs_info>
function wimpdrv_do_get_paddr_end(globals:globalsmap, slot:uint32) : paddr // do_paddr_base:paddr and do_paddr_end:paddr
    requires WK_ValidGlobalVars_Decls(globals)
    requires wimpdrv_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr2 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
    var do_pend := global_read_word(globals, G_WimpDrvs_Info(), vaddr2);

    (do_pend)
}

// Return the <pid> field of the given WimpDrv_Info slot in <g_wimpdrvs_info>
function wimpdrv_do_get_flag(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires wimpdrv_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;
    var v := global_read_word(globals, G_WimpDrvs_Info(), vaddr1);

    v
}

// Return all information in the wimp driver slot
function wimpdrv_get_slot(globals:globalsmap, slot:uint32) : (word, word, paddr, paddr, word)
    requires WK_ValidGlobalVars_Decls(globals)
    requires ValidGlobalOffset(G_WimpDrvs_Info(), slot * WimpDrv_Info_ENTRY_SZ)
{
    lemma_DistinctGlobals();
    
    var vaddr1 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_PID_BytesOffset;
    var vaddr3 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset;
    var vaddr4 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset;
    var vaddr5 := AddressOfGlobal(G_WimpDrvs_Info()) + slot * WimpDrv_Info_ENTRY_SZ + G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset;

    (
        global_read_word(globals, G_WimpDrvs_Info(), vaddr1),
        global_read_word(globals, G_WimpDrvs_Info(), vaddr2),
        global_read_word(globals, G_WimpDrvs_Info(), vaddr3),
        global_read_word(globals, G_WimpDrvs_Info(), vaddr4),
        global_read_word(globals, G_WimpDrvs_Info(), vaddr5)
    )
}

// Predicate: The given WimpDrv slot is unmodified between <old_globals> and <new_globals>
predicate {:opaque} p_wimpdrv_slot_equal(old_globals:globalsmap, new_globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires wimpdrv_valid_slot_id(slot)
{
    wimpdrv_get_id_word(old_globals, slot) == wimpdrv_get_id_word(new_globals, slot) &&
    wimpdrv_get_pid(old_globals, slot) == wimpdrv_get_pid(new_globals, slot) &&
    wimpdrv_do_get_paddr_base(old_globals, slot) == wimpdrv_do_get_paddr_base(new_globals, slot) &&
    wimpdrv_do_get_paddr_end(old_globals, slot) == wimpdrv_do_get_paddr_end(new_globals, slot) &&
    wimpdrv_do_get_flag(old_globals, slot) == wimpdrv_do_get_flag(new_globals, slot)
}

// Predicate: The given <id_word> only appears at <slot> in <g_wimpdrv_info>
predicate p_wimpdrv_slot_idword_unique(globals:globalsmap, slot:word, id_word:word)
    requires WK_ValidGlobalVars_Decls(globals)
    requires wimpdrv_valid_slot_id(slot)
    requires id_word != WimpDrv_ID_RESERVED_EMPTY
{
    forall i :: wimpdrv_valid_slot_id(i) && i != slot &&
                wimpdrv_get_id_word(globals, i) != WimpDrv_ID_RESERVED_EMPTY
            ==> wimpdrv_get_id_word(globals, i) != id_word
}