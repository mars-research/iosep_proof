include "usb_def.dfy"
include "../../arch/headers.dfy"
include "../../mm/wk_globals.dfy"
include "../../partition_id.s.dfy"

/*********************** Axioms ********************/
// [Math] Axiom (well known): Two valid usbpdev raw address values produce the same USBPDev_Addr if and only if the two 
// values are the same
// [NOTE] This axiom holds because all reserved bits in a valid usbpdev address must be 1
lemma {:axiom} Lemma_USBPDev_UniqueAddrLowAndHighWord_MapToUniqueUSBPDevAddr()
    ensures forall addr_word1, addr_word2 :: usb_is_usbpdev_addr_valid(addr_word1) && usb_is_usbpdev_addr_valid(addr_word2)
                ==> (usb_parse_usbpdev_addr(addr_word1) == usb_parse_usbpdev_addr(addr_word2) <==> addr_word1 == addr_word2)




/*********************** State Invariants and Related Predicates ********************/
predicate WK_WimpUSBPDev_ValidGlobalVarValues(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    P_WimpUSBPDev_ValidGlobalVarValues_PIDs(globals) &&
    P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals) &&
    
    (true)
}

predicate P_WimpUSBPDev_ValidGlobalVarValues_PIDs(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // 1. In each slot of wimp usb pdev info, the PID is either empty or must be a wimp partition's PID
    (forall i :: 0 <= i < WimpUSBPDev_Info_ENTRIES
        ==> (usbpdev_get_pid(globals, i) == WS_PartitionID(PID_INVALID) || 
            usbpdev_get_pid(globals, i) in pids_parse_g_wimp_pids(globals))
    ) && 

    // 2. If a USBPDev has the empty ID, then its PID must be invalid
    (forall i :: usbpdev_valid_slot_id(i) &&
            usbpdev_get_updateflag(globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
            usbpdev_get_addr_low(globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW &&
            usbpdev_get_addr_high(globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH
        ==> usbpdev_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    ) &&

    (true)
}

predicate P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // 1. In each slot of wimp usb pdev info, <usbpdev_addr> must be valid
    // [TODO][Issue-17] WimpUSBPDev_ADDR_EMPTY should be an invalid address. Thus we should modify the following 
    // predicate to include WimpUSBPDev_ADDR_EMPTY. Otherwise WimpUSBPDev_ADDR_EMPTY may actually be one valid USB bus 
    // and devices in the system
    // [NOTE] Maybe the above fix is not needed, because WK_ValidIDMappings says that WimpUSBPDev_ADDR_EMPTY does not 
    // map to any devices in the system
    (forall i :: usbpdev_valid_slot_id(i) && 
            usbpdev_get_updateflag(globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete
        ==> usb_is_usbpdev_addr_valid(usbpdev_get_addr(globals, i))) && 

    // 2. Each slot must map to a unique USBPDev_Addr, if the address is not (WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW)
    (forall i, j :: usbpdev_valid_slot_id(i) && usbpdev_valid_slot_id(j) &&
            usbpdev_get_updateflag(globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete && usbpdev_get_updateflag(globals, j) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
            !(usbpdev_get_addr_low(globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW && usbpdev_get_addr_high(globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH) &&
            !(usbpdev_get_addr_low(globals, j) == WimpUSBPDev_ADDR_EMPTY_LOW && usbpdev_get_addr_high(globals, j) == WimpUSBPDev_ADDR_EMPTY_HIGH)
        ==> ((usbpdev_get_addr_low(globals, i) == usbpdev_get_addr_low(globals, j) && usbpdev_get_addr_high(globals, i) == usbpdev_get_addr_high(globals, j)) <==> i == j)
    ) &&

    // 3. All USBPDev addrs stored in <g_wimpdevs_devlist> must be valid
    (forall i :: usbpdevlist_valid_slot_id(i)
        ==> (
            var usbpdev_addr_raw := usbpdevlist_get_addr(globals, i);
            usb_is_usbpdev_addr_valid(usbpdev_addr_raw)
        )
    ) &&

    (true)
}




/*********************** Predicates ********************/
// Predicate The USB device refered by <slot> must be in <g_wimpdevs_info>
predicate usbpdev_valid_slot_id(slot:uint32)
{
    0 <= slot < WimpUSBPDev_Info_ENTRIES
}

// Return the <id> field of the given USB device info slot in <g_wimpdevs_info>
function usbpdev_get_addr(globals:globalsmap, slot:uint32) : uint64 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdev_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
    var vaddr2 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
    var low := global_read_word(globals, G_WimpUSBPDev_Info(), vaddr1);
    var high := global_read_word(globals, G_WimpUSBPDev_Info(), vaddr2);

    UInt64_FromTwoUInt32s(high, low)
}

// Return the <addr_low> field of the given USB device info slot in <g_wimpdevs_info>
function usbpdev_get_addr_low(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdev_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();
    assert ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset);
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
    var v := global_read_word(globals, G_WimpUSBPDev_Info(), vaddr1);

    v
}

// Return the <addr_high> field of the given USB device info slot in <g_wimpdevs_info>
function usbpdev_get_addr_high(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdev_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();
    assert ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset);
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
    var v := global_read_word(globals, G_WimpUSBPDev_Info(), vaddr1);

    v
}

// Return the <pid> field of the given USB device info slot in <g_wimpdevs_info>
function usbpdev_get_pid(globals:globalsmap, slot:uint32) : WS_PartitionID 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdev_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();
    assert ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset);
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
    var pid := global_read_word(globals, G_WimpUSBPDev_Info(), vaddr1);

    WS_PartitionID(pid)
}

// Return the <update_flag> field of the given USB device info slot in <g_wimpdevs_info>
function usbpdev_get_updateflag(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdev_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
    var v := global_read_word(globals, G_WimpUSBPDev_Info(), vaddr1);

    v
}

// Predicate: The given USBPDev slot is unmodified between <old_globals> and <new_globals>
predicate {:opaque} p_usbpdev_slot_equal(old_globals:globalsmap, new_globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbpdev_valid_slot_id(slot)
{
    usbpdev_get_addr_low(old_globals, slot) == usbpdev_get_addr_low(new_globals, slot) &&
    usbpdev_get_addr_high(old_globals, slot) == usbpdev_get_addr_high(new_globals, slot) &&
    usbpdev_get_pid(old_globals, slot) == usbpdev_get_pid(new_globals, slot) &&
    usbpdev_get_updateflag(old_globals, slot) == usbpdev_get_updateflag(new_globals, slot)
}

// Predicate: Modification to <g_usbpdev_info> change the given slot only, care about the new values only
predicate usbpdev_info_newvalue(
    old_globals:globalsmap, new_globals:globalsmap, slot:uint32, new_usbpdev_addr_low:uint32, new_usbpdev_addr_high:uint32, new_usbpdev_pid:uint32, new_flag:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
{
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
    var vaddr2 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
    var vaddr3 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
    var vaddr4 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;

    var d1 := is_valid_addr(vaddr1) &&
                is_valid_vaddr(vaddr1) &&   
                    // <vaddr1> must be a valid vaddr
                is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1);
                    // <vaddr1> is a valid vaddr in <g_wimpdrvs_info>

    if(d1) then
        var globals1 := global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_usbpdev_addr_low);
        var globals2 := global_write_word(globals1, G_WimpUSBPDev_Info(), vaddr2, new_usbpdev_addr_high);
        var globals3 := global_write_word(globals2, G_WimpUSBPDev_Info(), vaddr3, new_usbpdev_pid);
        var globals4 := global_write_word(globals3, G_WimpUSBPDev_Info(), vaddr4, new_flag);

        new_globals == globals4
    else
        false
}

// Predicate: The given <usbpdev_addr> only appears at <slot> in <g_wimpdrv_info>
predicate p_usbpdev_slot_addr_unique(globals:globalsmap, slot:word, usbpdev_addr:USBPDev_Addr)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdev_valid_slot_id(slot)
{
    forall i :: usbpdev_valid_slot_id(i) && i != slot &&
                usbpdev_get_updateflag(globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
                !(usbpdev_get_addr_low(globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW &&
                usbpdev_get_addr_high(globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH) &&
                usb_is_usbpdev_addr_valid(usbpdev_get_addr(globals, i))
            ==> usb_parse_usbpdev_addr(usbpdev_get_addr(globals, i)) != usbpdev_addr
}




/*********************** Predicates for WimpUSBPDev_DevList ********************/
// Predicate The USB device refered by <slot> must be in <g_wimpdevs_devlist>
predicate usbpdevlist_valid_slot_id(slot:uint32)
{
    0 <= slot < WimpUSBPDev_DevList_ENTRIES
}

// Return the <addr_low> field of the given USB device info slot in <g_wimpdevs_devlist>
function usbpdevlist_get_addr_low(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdevlist_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    assert ValidGlobalOffset(G_WimpUSBPDev_DevList(), slot * WimpUSBPDev_DevList_ENTRY_SZ + WimpUSBPDev_DevList_ENTRY_LowAddr_ByteOffset);
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_DevList()) + slot * WimpUSBPDev_DevList_ENTRY_SZ + WimpUSBPDev_DevList_ENTRY_LowAddr_ByteOffset;
    var v := global_read_word(globals, G_WimpUSBPDev_DevList(), vaddr1);

    v
}

// Return the <addr_high> field of the given USB device info slot in <g_wimpdevs_devlist>
function usbpdevlist_get_addr_high(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdevlist_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();
    assert ValidGlobalOffset(G_WimpUSBPDev_DevList(), slot * WimpUSBPDev_DevList_ENTRY_SZ + WimpUSBPDev_DevList_ENTRY_HighAddr_ByteOffset);
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_DevList()) + slot * WimpUSBPDev_DevList_ENTRY_SZ + WimpUSBPDev_DevList_ENTRY_HighAddr_ByteOffset;
    var v := global_read_word(globals, G_WimpUSBPDev_DevList(), vaddr1);

    v
}

// Return the <id> field of the given USB device info slot in <g_wimpdevs_devlist>
function usbpdevlist_get_addr(globals:globalsmap, slot:uint32) : uint64 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdevlist_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_DevList()) + slot * WimpUSBPDev_DevList_ENTRY_SZ + WimpUSBPDev_DevList_ENTRY_LowAddr_ByteOffset;
    var vaddr2 := AddressOfGlobal(G_WimpUSBPDev_DevList()) + slot * WimpUSBPDev_DevList_ENTRY_SZ + WimpUSBPDev_DevList_ENTRY_HighAddr_ByteOffset;
    var low := global_read_word(globals, G_WimpUSBPDev_DevList(), vaddr1);
    var high := global_read_word(globals, G_WimpUSBPDev_DevList(), vaddr2);

    UInt64_FromTwoUInt32s(high, low)
}

// Function: Return all non-empty USBPDev addresses stored in <g_wimpdevs_devlist>
function usbpdevlist_get_all_non_empty_addrs(globals:globalsmap) : (result:set<USBPDev_Addr>)
    requires WK_ValidGlobalVars_Decls(globals)
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals)
{
    var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
    assert usb_is_usbpdev_addr_valid(empty_addr);

    usbpdevlist_get_all_addrs(globals) - {usb_parse_usbpdev_addr(empty_addr)}
}

// Function: Return all USBPDev addresses stored in <g_wimpdevs_devlist>
function usbpdevlist_get_all_addrs(globals:globalsmap) : (result:set<USBPDev_Addr>)
    requires WK_ValidGlobalVars_Decls(globals)
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals)

    ensures forall addr :: addr in result
                ==> (exists i :: usbpdevlist_valid_slot_id(i) && 
                                addr == usb_parse_usbpdev_addr(usbpdevlist_get_addr(globals, i)))
    ensures forall i :: usbpdevlist_valid_slot_id(i)
                ==> usb_parse_usbpdev_addr(usbpdevlist_get_addr(globals, i)) in result
        // Property: The result contains all USBPDev addresses stored in <g_wimpdevs_devlist>
{
    set i:uint32 | 0 <= i < WimpUSBPDev_DevList_ENTRIES         // usbpdevlist_valid_slot_id
          :: (
              var usbpdev_addr_raw := usbpdevlist_get_addr(globals, i);
              usb_parse_usbpdev_addr(usbpdev_addr_raw)
          )
}



/*********************** Utility Lemmas ********************/