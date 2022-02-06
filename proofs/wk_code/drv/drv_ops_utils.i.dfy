include "drv.s.dfy"
include "../state_properties_validity.s.dfy"
include "../dev/usb2/usb_tds_ops/usb_tds_checks.s.dfy"

lemma Lemma__wimpdrv_find_slot_Prove_usbtds_verifiedtds_do_not_associate_wimpdrv(globals:globalsmap, wimpdrv_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidGlobalVars_Vals(globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals)
    requires wimpdrv_valid_slot_id(wimpdrv_slot)

    requires wimpdrv_get_id_word(globals, wimpdrv_slot) == WimpDrv_ID_RESERVED_EMPTY
    ensures usbtds_verifiedtds_do_not_associate_wimpdrv(globals, wimpdrv_slot)
{
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();

    assert wimpdrv_get_pid(globals, wimpdrv_slot) == WS_PartitionID(PID_INVALID);

    forall usbtd_slot | usbtd_map_valid_slot_id(usbtd_slot) &&
            TestBit(usbtd_map_get_flags(globals, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
        ensures usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot) != wimpdrv_slot
    {
        if(usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot) == wimpdrv_slot)
        {
            var td_type := usbtd_map_get_type(globals, usbtd_slot);
            assert usbtd_slot_valid_type(globals, usbtd_slot);
            assert (td_type == USBTDs_TYPE_QTD32) || (td_type == USBTDs_TYPE_QH32) || 
                (td_type == USBTDs_TYPE_iTD32) || (td_type == USBTDs_TYPE_siTD32);

            assert false;
        }
    }

    reveal usbtds_verifiedtds_do_not_associate_wimpdrv();
}