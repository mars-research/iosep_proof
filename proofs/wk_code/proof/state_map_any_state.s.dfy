include "../state.dfy"
include "../state_properties_validity_subjs_objs_mstate.s.dfy"

function method Map_USBPDevAddr_ToDevID(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, id:USBPDev_Addr) : Dev_ID
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(addr) &&
             id != usb_parse_usbpdev_addr(addr)
        // Requirement: The USBPDev must be located at a non-empty address
{
    reveal WK_ValidIDMappings();

    id_mappings.usbpdev_ids[id]
}

function method Map_EEHCIIDWord_ToDevID(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, eehci_id:word) : Dev_ID
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires eehci_id != eEHCI_ID_INVALID
{
    reveal WK_ValidIDMappings();

    id_mappings.eehci_ids[eehci_id]
}