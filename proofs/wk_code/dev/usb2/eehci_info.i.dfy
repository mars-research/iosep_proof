include "eehci.s.dfy"
include "../../partition_id.i.dfy"

/*********************** Lemma for <g_existing_pids> Modification  ********************/
// Lemma: When replacing partition ID in <g_existing_pids>, if the old partition has no eEHCI, and 
// WK_USBTD_Map_ValidGlobalVarValues(old_globals), Then WK_USBTD_Map_ValidGlobalVarValues(new_globals)
lemma Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfOverwritePIDOfPartitionHavingNoEEHCI(old_globals:globalsmap, new_globals:globalsmap, pid_vaddr:vaddr, old_pid:word, new_pid:word)
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
    requires forall i:int :: (0 <= i < eEHCI_INSTANCE_NUM)
            ==> (eehci_info_get_pid(old_globals, i) == WS_PartitionID(PID_INVALID) ||
                eehci_info_get_pid(old_globals, i) != WS_PartitionID(old_pid));
        // Requirement: The partition of the overwritten PID must do not contain any eEHCI

    requires WK_EEHCI_Info_ValidGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_Existing_PIDs(), pid_vaddr, new_pid)
    requires old_pid == global_read_word(old_globals, G_Existing_PIDs(), pid_vaddr)
    
    ensures WK_EEHCI_Info_ValidGlobalVarValues(new_globals)
{
    assert forall i :: 0 <= i < eEHCI_INSTANCE_NUM
        ==> eehci_info_get_pid(old_globals, i) == eehci_info_get_pid(new_globals, i);

    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures eehci_info_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) ||
                eehci_info_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals)
    {
        var old_pid_i := eehci_info_get_pid(old_globals, i);
        var new_pid_i := eehci_info_get_pid(new_globals, i);

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




/*********************** Other Public Lemmas  ********************/
// Lemma: If <g_existing_pids> and <g_eechi_pid_map> is unchanged, and WK_EEHCI_Info_ValidGlobalVarValues(globals1),
// Then WK_EEHCI_Info_ValidGlobalVarValues(globals2)
lemma Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
    requires global_read_fullval(globals1, G_EEHCIs_Info()) == global_read_fullval(globals2, G_EEHCIs_Info())
    requires WK_EEHCI_Info_ValidGlobalVarValues(globals1)

    ensures WK_EEHCI_Info_ValidGlobalVarValues(globals2)
{
    assert pids_parse_g_wimp_pids(globals1) == pids_parse_g_wimp_pids(globals2);

    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures (eehci_info_get_pid(globals2, i) == WS_PartitionID(PID_INVALID) || 
            eehci_info_get_pid(globals2, i) in pids_parse_g_wimp_pids(globals2))
    {
        assert eehci_info_get_pid(globals2, i) == eehci_info_get_pid(globals1, i);
    }
}

// Lemma: When updating <eehci_id> field in eEHCI Info, and WK_EEHCI_Info_ValidGlobalVarValues(old_globals), Then 
// WK_EEHCI_Info_ValidGlobalVarValues(new_globals)
lemma Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfUpdateReservedFieldOnly(
    old_globals:globalsmap, new_globals:globalsmap, eehci_id_vaddr:vaddr, new_eehci_id:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires is_valid_vaddr(eehci_id_vaddr)
    requires is_gvar_valid_vaddr(G_EEHCIs_Info(), eehci_id_vaddr)
    requires forall i:int :: (0 <= i < eEHCI_INSTANCE_NUM)
            ==> AddressOfGlobal(G_EEHCIs_Info()) + i * EEHCI_Info_ENTRY_SZ + G_EEHCI_INFO_ENTRY_PID_BytesOffset != eehci_id_vaddr
        // Requirement: We are writting some <eehci_id> field at <eehci_id_vaddr>

    requires WK_EEHCI_Info_ValidGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCIs_Info(), eehci_id_vaddr, new_eehci_id)
    
    ensures WK_EEHCI_Info_ValidGlobalVarValues(new_globals)
{
    assert forall i :: 0 <= i < eEHCI_INSTANCE_NUM
        ==> eehci_info_get_pid(old_globals, i) == eehci_info_get_pid(new_globals, i);

    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures eehci_info_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) ||
                eehci_info_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals)
    {
        // Dafny can automatically prove it.
    }
}

// Lemma: When updating <pid> field in eEHCI Info, if the new PID is either invalid or fulfill <pids_is_existing_wimp_pid>,  
// and WK_EEHCI_Info_ValidGlobalVarValues(old_globals), Then WK_EEHCI_Info_ValidGlobalVarValues(new_globals)
lemma Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfUpdatePIDToExistingPIDs(old_globals:globalsmap, new_globals:globalsmap, pid_vaddr:vaddr, new_pid:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires is_valid_vaddr(pid_vaddr)
    requires is_gvar_valid_vaddr(G_EEHCIs_Info(), pid_vaddr)
    requires new_pid == PID_INVALID || pids_is_existing_wimp_pid(old_globals, new_pid)
        // Requirement: The new PID must be either invalid or fulfill <pids_is_existing_wimp_pid>

    requires WK_EEHCI_Info_ValidGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCIs_Info(), pid_vaddr, new_pid)
    
    ensures WK_EEHCI_Info_ValidGlobalVarValues(new_globals)
{
    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures eehci_info_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) ||
                eehci_info_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals)
    {
        var old_pid_i := eehci_info_get_pid(old_globals, i);
        var new_pid_i := eehci_info_get_pid(new_globals, i);
        var cur_pid_vaddr := AddressOfGlobal(G_EEHCIs_Info()) + i * EEHCI_Info_ENTRY_SZ + G_EEHCI_INFO_ENTRY_PID_BytesOffset;

        if(cur_pid_vaddr != pid_vaddr)
        {
            assert old_pid_i == new_pid_i;
        }
        else
        {
            assert new_pid_i.v == new_pid;
        }
    }
}