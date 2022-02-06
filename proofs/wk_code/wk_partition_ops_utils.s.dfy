include "state_properties_validity_subjs_objs_mstate.s.dfy" 

// Predicate: The global variables are modified as expected
predicate wk_create_partition_globalvars_relation(globals1:globalsmap, globals2:globalsmap, pid_slot:uint32, new_pid:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
{
    pids_valid_slot(pid_slot) &&
    new_pid == pids_get_pid(globals2, pid_slot).v &&

    // Other slots in <g_existing_pids> are unchanged
    (forall i :: pids_valid_slot(i) && i != pid_slot
        ==> pids_get_pid(globals1, i) == pids_get_pid(globals2, i)) &&

    // Other global variables except G_PID_Counter() are unchanged
    // [NOTE] We do not need to care about how G_PID_Counter() is modified, because it does not map to any state variables
    // in the sound WK design
    globals_other_gvar_unchanged_2vars(globals1, globals2, G_Existing_PIDs(), G_PID_Counter())
}

// Predicate: The global variables are modified as expected
predicate wk_destroy_partition_globalvars_relation(globals1:globalsmap, globals2:globalsmap, new_pid:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
{
    pids_parse_g_wimp_pids(globals2) == pids_parse_g_wimp_pids(globals1) - {WS_PartitionID(new_pid)} &&

    // Other global variables except G_Existing_PIDs() are unchanged
    globals_other_gvar_unchanged(globals1, globals2, G_Existing_PIDs())
}