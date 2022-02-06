include "../../../DetailedModel/Syntax.dfy"
include "../../arch/types.dfy"

include "../../utils/common/headers.dfy"

/*********************** Definitions of USB Bus ********************/
const USB_ADDR_MAX:int := 128;
type USBAddr = x:int | (1 <= x < USB_ADDR_MAX) witness usb_addr_witness()




/*********************** Definitions of eEHCI ********************/
const eEHCI_SlotID_EMPTY:int := 0xFFFFFFFF;  // 
const eEHCI_ID_INVALID:uint32 := 0; // [NOTE] eEHCI_ID_INVALID is 0 so we can intialize the eEHCI_mem using memset
const eEHCI_Handle_INVALID:uint32 := 0;
const eEHCI_INSTANCE_NUM:int := 128;

// For <g_eehci_mem>
const G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset:int := 0; 
const G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset:int := ARCH_ADDR_BYTES; 
const G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset:int := 2 * ARCH_ADDR_BYTES; 
const G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset:int := 2 * ARCH_ADDR_BYTES + UINT32_BYTES;
const G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset:int := 2 * ARCH_ADDR_BYTES + 2 * UINT32_BYTES;
const G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset:int := 2 * ARCH_ADDR_BYTES + 3 * UINT32_BYTES;
const G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset:int := 2 * ARCH_ADDR_BYTES + 4 * UINT32_BYTES; 
// Memory size of each eEHCI instance
const eEHCI_INSTANCE_BYTES:int := 2 * ARCH_ADDR_BYTES + 4 * UINT32_BYTES + eEHCI_USBTD_SlotID_NUMS * ARCH_WORD_BYTES;


// For eEHCI Config
const eEHCI_Config_Enable:int := 1;
const eEHCI_Config_Disable:int := 0;

// For eEHCI Interrupt
const eEHCI_Intr_Enable:int := 1;
const eEHCI_Intr_Disable:int := 0;

// For <g_eehcis_info>
const G_EEHCI_Info_ENTRY_Reserved_BytesOffset:int := 0; 
const G_EEHCI_INFO_ENTRY_PID_BytesOffset:int := ARCH_WORD_BYTES;
const EEHCI_Info_ENTRY_SZ:int := 5 * ARCH_WORD_BYTES;

const eEHCI_USBTD_SlotID_NUMS:int := 20;

// Machine representation of eEHCIs' IDs. Value must be a uint32 number.
// [NOTE] <eEHCI_ID> must be a uint32
datatype eEHCI_ID = eEHCI_ID(bus_id:uint16, e_id:uint16)
const eEHCI_ID_BUSID_SHIFT_BITS:int := 16;
const eEHCI_ID_BUSID_MASK:int := 0xFFFF;
const eEHCI_ID_eID_SHIFT_BITS:int := 0;
const eEHCI_ID_eID_MASK:int := 0xFFFF;

// [NOTE] (Corresponding to 2.n3 of sketch.txt) The I/O separation part of WK should contain the memory of eEHCIs
//	- Reason: the I/O separation part of WK wants to ensure that "No red device can issue memory access to eEHCIs", WK 
//  must know eEHCIs' memory region in order to call mHV to do so. Otherwise, the I/O separation part of WK can only 
//  assume the separation of ephemeral devices have done so.
//		- In other words, when configuring IOMMU, mHV understands memory addresses, but not abstract object IDs of eEHCIs
/*datatype eEHCI   = eEHCI(
                        id:eEHCI_ID,
                        
                        config:uint32,
                        status:uint32,

                        usbtd_regs:seq<uint32>
                    )
*/




/*********************** Definitions of WimpUSBPDev_Info ********************/
const WimpUSBPDev_SlotID_EMPTY:int := 0xFFFFFFFF;
const WimpUSBPDev_ADDR_EMPTY_LOW:uint32 := 0xFFFFFFFF;
const WimpUSBPDev_ADDR_EMPTY_HIGH:uint32 := 0xFFFFFFFF;

// (wimp dev ID low:word, wimp dev ID high:word, PID:word/WS_PartitionID, update_flag:word)
// [NOTE] Wimp apps can own USB peripheral devices (including hubs) and ephemeral EHCIs, but not any other ephemeral or 
// physical hubs. Otherwise, hub operations available to wimp apps depending on the USB hierachy of the hub. For example, 
// if a hub connects to two USB peripheral devices, then a wimp app should be able to reset a port. But if a hub connects 
// to two USB hubs, resetting a port of the top hub may break I/O separation
// [TODO] In the core of the I/O separation part of WK, we always need to implement activation of a device by wimp 
// device ID
const WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset:int := 0;
const WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset:int := ARCH_WORD_BYTES;
const WimpUSBPDev_Info_ENTRY_PID_ByteOffset:int := 2 * ARCH_WORD_BYTES;
const WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset:int := 3 * ARCH_WORD_BYTES;
const WimpUSBPDev_Info_ENTRIES:int := 16;
const WimpUSBPDev_Info_ENTRY_SZ:int := 4 * ARCH_WORD_BYTES;

const WimpUSBPDev_Slot_UpdateFlag_Complete:int := 0; // Modifications to the slot is done. Now the slot takes effect.
const WimpUSBPDev_Slot_UpdateFlag_Updating:int := 1; // We are in the middle of updating this slot




/*********************** Definitions of WimpUSBPDev_DevList ********************/
const WimpUSBPDev_DevList_ENTRY_LowAddr_ByteOffset:int := 0;
const WimpUSBPDev_DevList_ENTRY_HighAddr_ByteOffset:int := ARCH_WORD_BYTES;
const WimpUSBPDev_DevList_ENTRIES:int := 32; //WimpUSBPDev_Info_ENTRIES * 2;
const WimpUSBPDev_DevList_ENTRY_SZ:int := 2 * ARCH_WORD_BYTES;



/*********************** Definitions of USB TDs Slots in g_usbtd_mem_map ********************/
const USBTD_SlotID_INVALID:int := 0xFFFFFFFF;  //

const USBTD_ID_MAX:int := ARCH_WORD_LIMIT - 1; // The maximum USBTD
const USBTD_ID_INVALID:int := USBTD_ID_MAX; // The maximum USBTD ID is USBTD_ID_INVALID

const MAX_USB_TD_BYTES:int := 0x5C; // according to EHCI Specification for USB, Appendix B. 
const USB_TD_ENTRY_NUM:int := 2048;

const G_USBTDs_MAP_ENTRY_SZ:int := MAX_USB_TD_BYTES + 11 * ARCH_WORD_BYTES;

// Global variable for external USB TDs stored inside WK
// (usb_td:Bytes[MAX_USB_TD_BYTES], pid:WS_PartitionID/UInt32, type:word/UInt32, usb_bus_id:word/UInt32, flags:word/UInt32,
// eEHCISeparation_Handle:word,
// eEHCISeparation_InputParam1:word/UInt32, eEHCISeparation_InputParam2:word/UInt32, eEHCISeparation_InputParam3:word/UInt32)
const G_USBTDs_MAP_ENTRY_TD_BytesOffset:int := 0;
const G_USBTDs_MAP_ENTRY_ID_BytesOffset:int := MAX_USB_TD_BYTES;
const G_USBTDs_MAP_ENTRY_PID_BytesOffset:int := MAX_USB_TD_BYTES + ARCH_WORD_BYTES;
const G_USBTDs_MAP_ENTRY_TYPE_BytesOffset:int := MAX_USB_TD_BYTES + 2 * ARCH_WORD_BYTES;
const G_USBTDs_MAP_ENTRY_BUSID_BytesOffset:int := MAX_USB_TD_BYTES + 3 * ARCH_WORD_BYTES;
const G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset:int := MAX_USB_TD_BYTES + 4 * ARCH_WORD_BYTES;
const G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset:int := MAX_USB_TD_BYTES + 5 * ARCH_WORD_BYTES;
const G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset:int := MAX_USB_TD_BYTES + 6 * ARCH_WORD_BYTES;
const G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset:int := MAX_USB_TD_BYTES + 7 * ARCH_WORD_BYTES;
const G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset:int := MAX_USB_TD_BYTES + 8 * ARCH_WORD_BYTES;
const G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset:int := MAX_USB_TD_BYTES + 9 * ARCH_WORD_BYTES;
const G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset:int := MAX_USB_TD_BYTES + 10 * ARCH_WORD_BYTES;

// Selector of <InputParam> fields
const G_USBTDs_MAP_ENTRY_InputParam1:int := 1;
const G_USBTDs_MAP_ENTRY_InputParam2:int := 2;
const G_USBTDs_MAP_ENTRY_InputParam3:int := 3;


// Valid values of G_USBTDs_MAP_ENTRY_TYPE
const USBTDs_TYPE_QTD32:int := 1;
const USBTDs_TYPE_QH32:int := 2;
const USBTDs_TYPE_iTD32:int := 3;
const USBTDs_TYPE_siTD32:int := 4;

// Flags in G_USBTDs_MAP_ENTRY_FLAGS
const USBTD_SLOT_FLAG_SlotSecure_Bit:int := 31;
const USBTD_SLOT_FLAG_SubmitDone_Bit:int := 0;




/*********************** Definitions of USB TDs ********************/
const PeriodicFrameList_BYTES:int := 4096; // according to EHCI Specification for USB, Section 3.1. 
const SHL_PeriodicFrameList_BYTES_Bits:int := 12; // left shify 12 bits equals to multiply with PeriodicFrameList_BYTES

const USBTD_Link_NextUSBTD_SHIFT_BITS:int := 4;    // The start bit for linking next USB TD
const QH32_HUB_PORT_SHIFT_BITS:int := 24;
const QH32_HUB_ADDR_SHIFT_BITS:int := 16;

const QTD32_SIZE_BYTES:int := 0x20;
const QH32_SIZE_BYTES:int := 0x30;




/*********************** Axioms ********************/
// [Math] Axiom (well known): UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW) 
// satisfies usb_is_usbpdev_addr_valid
lemma {:axiom} Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty()
    ensures usb_is_usbpdev_addr_valid(UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW))



/*********************** Definitions of USB Peripheral Devices ********************/
const USBPDevAddr_Reserved1_RightShiftBits:int := 16;
const USBPDevAddr_Reserved2_RightShiftBits:int := 21;
const USBPDevAddr_HUB_Addr_RightShiftBits:int := 14;
const USBPDevAddr_HUB_Port_RightShiftBits:int := 7;

const USBPDevAddr_Reserved1_MASK:int := 0xFFFF;
const USBPDevAddr_Reserved2_MASK:int := 0x7FF;
const USBPDevAddr_Reserved1_Val:int := 0xFFFF;
const USBPDevAddr_Reserved2_Val:int := 0x7FF;


// [NOTE] USBPDev_Addr is 64-bit long
datatype USBPDev_Addr = USBPDev_Addr(reserved1:uint16, bus_id:uint16, reserved2:uint11, hub_addr:USBAddr, hub_port:uint7, dev_addr:USBAddr)




/*********************** Utility Functions ********************/
const USB_ADDR_MASK:int := 0x7F;
const HUB_PORT_MASK:int := 0x7F;

// [TODO-Important] What security issue would it cause, if this predicate is violated?
predicate {:opaque} usb_is_usbpdev_addr_valid(id:uint64)
{
    var low := UInt64Low(id);
    var high := UInt64High(id);

    // 1. All the reserved bits must be set to 1
    BitwiseAnd(RightShift(high, USBPDevAddr_Reserved1_RightShiftBits), USBPDevAddr_Reserved1_MASK) == USBPDevAddr_Reserved1_Val &&
    BitwiseAnd(RightShift(low, USBPDevAddr_Reserved2_RightShiftBits), USBPDevAddr_Reserved2_MASK) == USBPDevAddr_Reserved2_Val &&

    // 2. USB addresses cannot be 0
    BitwiseAnd(RightShift(low, USBPDevAddr_HUB_Addr_RightShiftBits), USB_ADDR_MASK) != 0 &&
    BitwiseAnd(low, USB_ADDR_MASK) != 0
}

// Predicate: Is the usb address of the device valid?
predicate {:opaque} usb_is_dev_addr_valid(addr:uint32)
{
    // 0 is reserved for the wimpy kernel (for resetting devices and hubs)
    1 <= addr < USB_ADDR_MAX
}

// Predicate: Is the hub port for the device valid?
predicate {:opaque} usb_is_hub_port_valid(port:uint32)
{
    0 <= port < 128
}

// Predicate: Is the given <bus_id> a valid usb bus ID?
predicate usb_is_valid_bus_id(bus_id:word)
{
    isUInt16(bus_id)
}

// Function: Parse an uint64 into USBPDev_Addr
function usb_parse_usbpdev_addr(addr:uint64):USBPDev_Addr
    requires usb_is_usbpdev_addr_valid(addr)
{
    reveal usb_is_usbpdev_addr_valid();

    var low := UInt64Low(addr);
    var high := UInt64High(addr);

    lemma_MaskReturnUInt16();
    lemma_MaskReturnUInt7();

    USBPDev_Addr(
        USBPDevAddr_Reserved1_Val,                                              // reserved1
        BitwiseAnd(high, 0xFFFF),                                               // bus_id
        USBPDevAddr_Reserved2_Val,                                              // reserved2
        BitwiseAnd(RightShift(low, USBPDevAddr_HUB_Addr_RightShiftBits), USB_ADDR_MASK),  // hub_addr
        BitwiseAnd(RightShift(low, USBPDevAddr_HUB_Port_RightShiftBits), HUB_PORT_MASK),  // hub_port
        BitwiseAnd(low, USB_ADDR_MASK)                                                   // dev_addr
    )
}

// Function: Parse an uint32 into eEHCI_ID
function usb_parse_eehci_id(id:uint32) : eEHCI_ID
{
    var bus_id := BitwiseAnd(RightShift(id, eEHCI_ID_BUSID_SHIFT_BITS), eEHCI_ID_BUSID_MASK);
    var e_id := BitwiseAnd(id, eEHCI_ID_eID_MASK);

    Lemma_BitwiseAndFFFFYieldsUInt16(RightShift(id, eEHCI_ID_BUSID_SHIFT_BITS));
    Lemma_BitwiseAndFFFFYieldsUInt16(id);
    eEHCI_ID(bus_id, e_id)
}




/*********************** Private functions ********************/
function method usb_addr_witness():int
    ensures 1 <= usb_addr_witness() < USB_ADDR_MAX
{
    1
}