include "state.dfy"
include "mm/wk_globals.dfy"

const PID_INVALID:uint32 := 0; // Reserved PID so that <g_existing_pids> can be filled with 0s at the beginning
const PID_RESERVED_OS_PARTITION:uint32 := 1;
const PID_MAX:uint32 := UINT32_LIM - 1;

const PID_GENERATE_FUNC_ERROR := PID_RESERVED_OS_PARTITION; // So that generated new PID never equal to PID_RESERVED_OS_PARTITION
const PID_SlotID_INVALID:int := 0xFFFFFFFF;  //

/*********************** Architecture Specific State Invariants and Related Predicates ********************/
predicate WK_ValidPartitionIDs_InGlobalVars(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // 1. Relationships of contants must hold
    PID_INVALID == TruncateUInt32(PID_MAX + 1) &&
    (PID_GENERATE_FUNC_ERROR == PID_RESERVED_OS_PARTITION) &&

    // 2. <g_pid_counter> must never equal to PID_INVALID (== 0)
    pids_g_pid_counter_is_not_reserved_empty(globals) &&

    (
        var parsed_existing_pids:set<WS_PartitionID> := pids_parse_g_wimp_pids(globals);
        var parsed_pid_last_allocated:WS_PartitionID := pids_parse_g_pid_counter(globals);

        // 3. All existing PIDs in the global variable <g_existing_pids> must be equal or smaller than <g_pid_counter>
        (forall pid :: pid in parsed_existing_pids ==> pid.v <= parsed_pid_last_allocated.v) &&

        (true)
    ) &&

    // 4. Any existing pids stored in <g_existing_pids> are different with each other
    pids_g_existing_pids_no_duplicate(globals) &&

    // 5. The global variable <g_existing_pids> does not contain PID_RESERVED_OS_PARTITION
    pids_g_existing_pids_exclude_os_pid(globals) &&

    (true)
}

// Predicate: <g_pid_counter> must never equal to PID_INVALID (== 0)
predicate pids_g_pid_counter_is_not_reserved_empty(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    global_read_word_byoffset(globals, G_PID_Counter(), 0) != PID_INVALID
}

// Predicate: Any existing pids stored in <g_existing_pids> are different with each other
predicate pids_g_existing_pids_no_duplicate(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    var existing:seq<word> := global_read_fullval(globals, G_Existing_PIDs());

    (forall i, j :: (0 <= i < |existing| && 0 <= j < |existing|) &&
            (existing[i] != PID_INVALID && existing[j] != PID_INVALID)
                // If two PIDs are not PID_INVALID
        ==> (existing[i] == existing[j] <==> i == j))
                // Then they are same iff they are at the same slot in the global variable <g_existing_pids>
}

// Predicate: the global variable <g_existing_pids> does not contain PID_RESERVED_OS_PARTITION
predicate pids_g_existing_pids_exclude_os_pid(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    var existing:seq<word> := global_read_fullval(globals, G_Existing_PIDs());

    (forall pid :: pid in existing 
        ==> pid != PID_RESERVED_OS_PARTITION)
}




/*********************** Utility Functions ********************/
predicate pids_valid_slot(slot:word)
{
    0 <= slot < WK_Existing_PIDs_ENTRIES
}

// Predicate: Is the given pid <v> a OS partition's PID 
predicate pids_is_os_pid(v:uint32)
{
    v == PID_RESERVED_OS_PARTITION
}

// Predicate: Is the given pid <v> an existing wimp partition's PID
predicate pids_is_existing_wimp_pid(globals:globalsmap, v:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
{
    var existing:seq<word> := global_read_fullval(globals, G_Existing_PIDs());

    v != PID_INVALID && v in existing
}

// Return allocated PIDs, and the default PID for the OS partition
function WK_GetAllPIDs(globals:globalsmap) : (result:set<WS_PartitionID>)
    requires WK_ValidGlobalVars_Decls(globals)
    ensures forall pid :: pid in result
                ==> pid != WS_PartitionID(PID_INVALID)
{
    pids_parse_g_wimp_pids(globals) + {WS_PartitionID(PID_RESERVED_OS_PARTITION)}
}

// Return allocated PIDs stored in the global variable <g_existing_pids>
function pids_parse_g_wimp_pids(globals:globalsmap) : set<WS_PartitionID>
    requires WK_ValidGlobalVars_Decls(globals)

    ensures forall pid :: pid in pids_parse_g_wimp_pids(globals)
                ==> pid != WS_PartitionID(PID_INVALID)
        // Property: No PID_INVALID is returned
    ensures forall pid :: pid in pids_parse_g_wimp_pids(globals)
                ==> pids_is_existing_wimp_pid(globals, pid.v)
    ensures forall pid :: pids_is_existing_wimp_pid(globals, pid)
                ==> WS_PartitionID(pid) in pids_parse_g_wimp_pids(globals)
{
    var existing:seq<word> := global_read_fullval(globals, G_Existing_PIDs());

    set w | (w in existing) && (w != PID_INVALID) :: WS_PartitionID(w)
}

// Return the WS_PartitionID stored in the global variable <g_pid_counter>
function pids_parse_g_pid_counter(globals:globalsmap) : WS_PartitionID
    requires WK_ValidGlobalVars_Decls(globals)
    requires gvar_get_size(G_PID_Counter()) == ARCH_WORD_BYTES
        // Requirement: the global variable g_pid_counter is one word in length
    requires PID_INVALID == 0
        // Requirement: Due to the definition of PID_MAX and the implementation of the procedure <pid_generate>
    requires pids_g_pid_counter_is_not_reserved_empty(globals)
{
    var w:word := global_read_word_byoffset(globals, G_PID_Counter(), 0);

    WS_PartitionID(w)
}

// Return the <pid> field of the given slot in <g_existing_pids>
function pids_get_pid(globals:globalsmap, slot:uint32) : WS_PartitionID 
    requires WK_ValidGlobalVars_Decls(globals)
    requires pids_valid_slot(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    assert ValidGlobalOffset(G_Existing_PIDs(), slot * WK_Existing_PID_ENTRY_SZ + G_Existing_PIDs_Entry_PID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_Existing_PIDs()) + slot * WK_Existing_PID_ENTRY_SZ + G_Existing_PIDs_Entry_PID_BytesOffset;
    var v := global_read_word(globals, G_Existing_PIDs(), vaddr1);

    WS_PartitionID(v)
}

// Predicate: Only one slot in <g_existing_pids> among all global variables is unchanged
predicate pid_existing_updateslot_update_one_slot_only(globals1:globalsmap, globals2:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires pids_valid_slot(slot)
{
    // Other slots in <g_existing_pids> are unchanged
    (forall i :: pids_valid_slot(i) && i != slot
        ==> pids_get_pid(globals1, i) == pids_get_pid(globals2, i)) &&

    // Other global variables are unchanged
    globals_other_gvar_unchanged(globals1, globals2, G_Existing_PIDs())
}