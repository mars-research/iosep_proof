include "usb_pdev.s.dfy"
include "../../state_properties_validity.s.dfy"
include "usb_tds_ops/usb_tds_checks.s.dfy"

lemma Lemma__usbpdev_find_slot_Prove_usbtds_verifiedtds_do_not_associate_usb_pdev(globals:globalsmap, usbpdev_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidGlobalVars_Vals(globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals)
    requires usbpdev_valid_slot_id(usbpdev_slot)

    requires usbpdev_get_addr_low(globals, usbpdev_slot) == WimpUSBPDev_ADDR_EMPTY_LOW
    requires usbpdev_get_addr_high(globals, usbpdev_slot) == WimpUSBPDev_ADDR_EMPTY_HIGH
    ensures usbtds_verifiedtds_do_not_associate_usb_pdev(globals, usbpdev_slot)
{
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();

    // [TODO] Not support iTD and siTD yet

    forall usbtd_slot | usbtd_map_valid_slot_id(usbtd_slot) &&
            TestBit(usbtd_map_get_flags(globals, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
        ensures usbtd_map_get_usbpdev_slotid(globals, usbtd_slot) != usbpdev_slot
    {
        if(usbtd_map_get_usbpdev_slotid(globals, usbtd_slot) == usbpdev_slot)
        {
            var td_type := usbtd_map_get_type(globals, usbtd_slot);
            assert usbtd_slot_valid_type(globals, usbtd_slot);
            assert (td_type == USBTDs_TYPE_QTD32) || (td_type == USBTDs_TYPE_QH32) || 
                (td_type == USBTDs_TYPE_iTD32) || (td_type == USBTDs_TYPE_siTD32);

            if(td_type == USBTDs_TYPE_QH32)
            {
                assert false;
            }
            else
            {
                assert false;
            }

            assert false;
        }
    }
}

// Lemma: If <usbpdev_addr_raw> != UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW), then
// it parses to a different USBPDev_Addr
lemma Lemma_USBPDevAddr_NonEmptyAddrRawParseToNonEmptyAddr(usbpdev_addr_raw:uint64)
    requires usb_is_usbpdev_addr_valid(usbpdev_addr_raw)
    requires usbpdev_addr_raw != UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW)

    ensures var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
            usb_is_usbpdev_addr_valid(empty_addr)
    ensures var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
            usb_parse_usbpdev_addr(usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr)
{
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
    Lemma_USBPDev_UniqueAddrLowAndHighWord_MapToUniqueUSBPDevAddr();
}