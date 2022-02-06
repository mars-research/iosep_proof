//include "../state.dfy"
include "../utils/common/headers.dfy"
include "../arch/headers.dfy"
include "../dev/usb2/usb_def.dfy"

type globaldecls = map<symbol, size>

/*********************** Definition of All Global Variables ********************/
// Global variable: Virtual memory region of wimp apps' ephemeral EHCI memory
// [Assumption] The physical memory region of <g_eehci_mem> must be [G_EEHCI_MEM_PBASE, G_EEHCI_MEM_PBASE + G_EEHCI_MEM_SZ)
const G_EEHCI_MEM_SZ_Tight:int := eEHCI_INSTANCE_NUM * eEHCI_INSTANCE_BYTES;
const G_EEHCI_MEM_SZ:int := roundup(G_EEHCI_MEM_SZ_Tight, PAGE_4K_SZ);
function method {:opaque} G_EEHCI_MEM(): symbol {"g_eehci_mem" }

// Global variable: Virtual memory region of USB TDs
const G_USBTDs_MAP_MEM_SZ_Tight:int := G_USBTDs_MAP_ENTRY_SZ * USB_TD_ENTRY_NUM;
const G_USBTDs_MAP_MEM_SZ:int := roundup(G_USBTDs_MAP_MEM_SZ_Tight, PAGE_4K_SZ);
function method {:opaque} G_USBTD_MAP_MEM(): symbol {"g_usbtd_map_mem" }

// Global variable: The paddr base for wimp apps' ephemeral EHCI memory
const G_EEHCI_MEM_PBASE_SZ:int := ARCH_WORD_BYTES;
function method {:opaque} G_EEHCI_MEM_PBASE(): symbol {"g_eehci_mem_pbase" }

// Global variable holding necessary information (similar to process struct) for wimp usb drv
// (wimp drv ID:word/UInt32, PID:WS_PartitionID/UInt32, do_base_paddr:paddr, do_end_paddr:paddr, update_flag:word/uint32)
const G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset:int := 0; 
const G_WimpDrv_Info_ENTRY_PID_BytesOffset:int := ARCH_WORD_BYTES;
const G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset:int := 2 * ARCH_WORD_BYTES;
const G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset:int := 3 * ARCH_WORD_BYTES;
const G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset:int := 4 * ARCH_WORD_BYTES;
const WimpDrv_Info_ENTRIES:int := 128;
const WimpDrv_Info_ENTRY_SZ:int := 5 * ARCH_WORD_BYTES;
const G_WimpDrvs_Info_SZ:int := WimpDrv_Info_ENTRIES * WimpDrv_Info_ENTRY_SZ;
function method {:opaque} G_WimpDrvs_Info(): symbol {"g_wimpdrvs_info" }

// Global variable for wimp usb peripheral dev information
const G_WimpUSBPDev_Info_SZ:int := WimpUSBPDev_Info_ENTRIES * WimpUSBPDev_Info_ENTRY_SZ;
function method {:opaque} G_WimpUSBPDev_Info(): symbol {"g_wimpdevs_info" }

// Global variable for all assignable USBPDevs
const G_WimpUSBPDev_DevList_SZ:size := WimpUSBPDev_DevList_ENTRIES * WimpUSBPDev_DevList_ENTRY_SZ;
function method {:opaque} G_WimpUSBPDev_DevList(): symbol {"g_wimpdevs_devlist" }

// Global variable for ephemeral interrupt controller - pid mapping for eEHCIs
// (eehci ID:EINTC_ID, PID:WS_PartitionID/UInt32)
const WK_EINTC_PID_MAP_NPAGES:int := 1;
const G_WK_EINTC_PID_MAP_SZ:int := WK_EINTC_PID_MAP_NPAGES * PAGE_4K_SZ;
function method {:opaque} G_EINTC_PID_Map(): symbol {"g_eintc_pid_map" }

// Global variable for ephemeral EHCI - pid mapping for eEHCIs
// (eehci ID:eEHCI_ID, PID:WS_PartitionID/UInt32)

const G_EEHCIs_Info_SZ:int := eEHCI_INSTANCE_NUM * EEHCI_Info_ENTRY_SZ;
function method {:opaque} G_EEHCIs_Info(): symbol {"g_eehcis_info" }

// Global variable for existing wimp partitions
const G_Existing_PIDs_Entry_PID_BytesOffset := 0;
const WK_Existing_PID_ENTRY_SZ:int := ARCH_WORD_BYTES;
const WK_Existing_PIDs_ENTRIES:int := 128;
const G_WK_Existing_PIDs_SZ:int := WK_Existing_PIDs_ENTRIES * WK_Existing_PID_ENTRY_SZ;
function method {:opaque} G_Existing_PIDs(): symbol {"g_existing_pids" }

// Global variable for partition ID counter
const G_PID_Counter_SZ:size := ARCH_WORD_BYTES;
function method {:opaque} G_PID_Counter(): symbol {"g_pid_counter" }

// Global variable for partition ID counter
const G_USBTD_Counter_SZ:size := ARCH_WORD_BYTES;
function method {:opaque} G_USBTD_ID_Counter(): symbol {"g_usbtd_counter" }

// Scratchpad global variable - (one) Temp USB TD
const G_WK_Temp_USBTD_SZ:uint32 := G_USBTDs_MAP_ENTRY_SZ;
function method {:opaque} G_Temp_USBTD(): symbol {"g_temp_usbtd" }


function method WK_GlobalDecls(): globaldecls
    ensures ValidGlobalDecls(WK_GlobalDecls())
{
    map[
        G_EEHCI_MEM() := G_EEHCI_MEM_SZ,
        G_USBTD_MAP_MEM() := G_USBTDs_MAP_MEM_SZ,
        G_EEHCI_MEM_PBASE() := G_EEHCI_MEM_PBASE_SZ,
        G_WimpDrvs_Info() := G_WimpDrvs_Info_SZ,
        G_WimpUSBPDev_Info() := G_WimpUSBPDev_Info_SZ,
        G_EEHCIs_Info() := G_EEHCIs_Info_SZ,

        G_WimpUSBPDev_DevList() := G_WimpUSBPDev_DevList_SZ,
        G_EINTC_PID_Map() := G_WK_EINTC_PID_MAP_SZ,
        G_Existing_PIDs() := G_WK_Existing_PIDs_SZ,
        G_PID_Counter() := G_PID_Counter_SZ,
        G_USBTD_ID_Counter() := G_USBTD_Counter_SZ,

        G_Temp_USBTD() := G_WK_Temp_USBTD_SZ
        ]
}





/*********************** Axioms ********************/
// [Loader] Axiom (well known): globals have an unknown vaddr, only establised by LDR-reloc
function {:axiom} AddressOfGlobal(g:symbol): vaddr
    requires is_gvar_exist(g)
    ensures AddressOfGlobal(g) + gvar_get_size(g) < UINT32_LIM
    ensures is_valid_vaddr(AddressOfGlobal(g))




/*********************** State Invariants of Global Variables ********************/
predicate {:opaque} WK_ValidGlobalVars_Decls(globals:globalsmap)
{
    // globals: Each WK's global variable must have separate memory from each other
    WK_Globals_Separate_Mem() &&

    // globals: global variable size must be word aligned
    (forall g :: g in WK_GlobalDecls()
        ==> WordAligned(WK_GlobalDecls()[g])) &&

    // globals: same names as decls
    (forall g :: g in WK_GlobalDecls() <==> g in globals) &&

    // global: same size as decls
    (forall g :: g in WK_GlobalDecls()
        ==> |globals[g]| == BytesToWords(WK_GlobalDecls()[g])) &&

    (true)
}

predicate DistinctGlobals()
{
    G_EEHCI_MEM() != G_USBTD_MAP_MEM() &&
    G_EEHCI_MEM() != G_EEHCI_MEM_PBASE() &&
    G_EEHCI_MEM() != G_WimpDrvs_Info() &&
    G_EEHCI_MEM() != G_WimpUSBPDev_Info() &&
    G_EEHCI_MEM() != G_EEHCIs_Info() &&
    G_EEHCI_MEM() != G_WimpUSBPDev_DevList() &&
    G_EEHCI_MEM() != G_EINTC_PID_Map() &&
    G_EEHCI_MEM() != G_Existing_PIDs() &&
    G_EEHCI_MEM() != G_PID_Counter() &&
    G_EEHCI_MEM() != G_USBTD_ID_Counter() &&
    G_EEHCI_MEM() != G_Temp_USBTD() &&

    G_USBTD_MAP_MEM() != G_EEHCI_MEM_PBASE() &&
    G_USBTD_MAP_MEM() != G_WimpDrvs_Info() &&
    G_USBTD_MAP_MEM() != G_WimpUSBPDev_Info() &&
    G_USBTD_MAP_MEM() != G_EEHCIs_Info() &&
    G_USBTD_MAP_MEM() != G_WimpUSBPDev_DevList() &&
    G_USBTD_MAP_MEM() != G_EINTC_PID_Map() &&
    G_USBTD_MAP_MEM() != G_Existing_PIDs() &&
    G_USBTD_MAP_MEM() != G_PID_Counter() &&
    G_USBTD_MAP_MEM() != G_USBTD_ID_Counter() &&
    G_USBTD_MAP_MEM() != G_Temp_USBTD() &&

    G_EEHCI_MEM_PBASE() != G_WimpDrvs_Info() &&
    G_EEHCI_MEM_PBASE() != G_WimpUSBPDev_Info() &&
    G_EEHCI_MEM_PBASE() != G_EEHCIs_Info() &&
    G_EEHCI_MEM_PBASE() != G_WimpUSBPDev_DevList() &&
    G_EEHCI_MEM_PBASE() != G_EINTC_PID_Map() &&
    G_EEHCI_MEM_PBASE() != G_Existing_PIDs() &&
    G_EEHCI_MEM_PBASE() != G_PID_Counter() &&
    G_EEHCI_MEM_PBASE() != G_USBTD_ID_Counter() &&
    G_EEHCI_MEM_PBASE() != G_Temp_USBTD() &&

    G_WimpDrvs_Info() != G_WimpUSBPDev_Info() &&
    G_WimpDrvs_Info() != G_EEHCIs_Info() &&
    G_WimpDrvs_Info() != G_WimpUSBPDev_DevList() &&
    G_WimpDrvs_Info() != G_EINTC_PID_Map() &&
    G_WimpDrvs_Info() != G_Existing_PIDs() &&
    G_WimpDrvs_Info() != G_PID_Counter() &&
    G_WimpDrvs_Info() != G_USBTD_ID_Counter() &&
    G_WimpDrvs_Info() != G_Temp_USBTD() &&

    G_WimpUSBPDev_Info() != G_EEHCIs_Info() &&
    G_WimpUSBPDev_Info() != G_WimpUSBPDev_DevList() &&
    G_WimpUSBPDev_Info() != G_EINTC_PID_Map() &&
    G_WimpUSBPDev_Info() != G_Existing_PIDs() &&
    G_WimpUSBPDev_Info() != G_PID_Counter() &&
    G_WimpUSBPDev_Info() != G_USBTD_ID_Counter() &&
    G_WimpUSBPDev_Info() != G_Temp_USBTD() &&

    G_EEHCIs_Info() != G_WimpUSBPDev_DevList() &&
    G_EEHCIs_Info() != G_EINTC_PID_Map() &&
    G_EEHCIs_Info() != G_Existing_PIDs() &&
    G_EEHCIs_Info() != G_PID_Counter() &&
    G_EEHCIs_Info() != G_USBTD_ID_Counter() &&
    G_EEHCIs_Info() != G_Temp_USBTD() &&

    G_WimpUSBPDev_DevList() != G_EINTC_PID_Map() &&
    G_WimpUSBPDev_DevList() != G_Existing_PIDs() &&
    G_WimpUSBPDev_DevList() != G_PID_Counter() &&
    G_WimpUSBPDev_DevList() != G_USBTD_ID_Counter() &&
    G_WimpUSBPDev_DevList() != G_Temp_USBTD() &&

    G_EINTC_PID_Map() != G_Existing_PIDs() &&
    G_EINTC_PID_Map() != G_PID_Counter() &&
    G_EINTC_PID_Map() != G_USBTD_ID_Counter() &&
    G_EINTC_PID_Map() != G_Temp_USBTD() &&

    G_Existing_PIDs() != G_PID_Counter() &&
    G_Existing_PIDs() != G_USBTD_ID_Counter() &&
    G_Existing_PIDs() != G_Temp_USBTD() &&

    G_PID_Counter() != G_USBTD_ID_Counter() &&
    G_PID_Counter() != G_Temp_USBTD() &&

    G_USBTD_ID_Counter() != G_Temp_USBTD() &&

    (true)
}

// Interface realization: <WK_Globals_Separate_Mem>
// Each WK's global variable must have separate memory from each other
// [NOTE] WK loader should ensure different vaddr maps to different paddr
predicate WK_Globals_Separate_Mem()
{
    reveal G_EEHCI_MEM();
    reveal G_USBTD_MAP_MEM();
    reveal G_EEHCI_MEM_PBASE();
    reveal G_WimpDrvs_Info();
    reveal G_WimpUSBPDev_Info();
    reveal G_EEHCIs_Info();

    reveal G_WimpUSBPDev_DevList();
    reveal G_EINTC_PID_Map();
    reveal G_Existing_PIDs();
    reveal G_PID_Counter();
    reveal G_USBTD_ID_Counter();
    reveal G_Temp_USBTD();

    var G_EEHCI_MEM_start := AddressOfGlobal(G_EEHCI_MEM());
    var G_EEHCI_MEM_end := G_EEHCI_MEM_start + G_EEHCI_MEM_SZ;

    var G_USBTDs_MEM_start := AddressOfGlobal(G_USBTD_MAP_MEM());
    var G_USBTDs_MEM_end := G_USBTDs_MEM_start + G_USBTDs_MAP_MEM_SZ;

    var G_EEHCI_MEM_PBASE_start := AddressOfGlobal(G_EEHCI_MEM_PBASE());
    var G_EEHCI_MEM_PBASE_end := G_EEHCI_MEM_PBASE_start + G_EEHCI_MEM_PBASE_SZ; 

    var G_WimpDrvs_Info_start := AddressOfGlobal(G_WimpDrvs_Info());
    var G_WimpDrvs_Info_end := G_WimpDrvs_Info_start + G_WimpDrvs_Info_SZ;

    var G_WimpDev_PID_Map_start := AddressOfGlobal(G_WimpUSBPDev_Info());
    var G_WimpDev_PID_Map_end := G_WimpDev_PID_Map_start + G_WimpUSBPDev_Info_SZ;

    var G_EEHCIs_Info_start := AddressOfGlobal(G_EEHCIs_Info());
    var G_EEHCIs_Info_end := G_EEHCIs_Info_start + G_EEHCIs_Info_SZ;

    var G_WimpUSBPDev_DevList_start := AddressOfGlobal(G_WimpUSBPDev_DevList());
    var G_WimpUSBPDev_DevList_end := G_WimpUSBPDev_DevList_start + G_WimpUSBPDev_DevList_SZ;

    var G_EINTC_PID_Map_start := AddressOfGlobal(G_EINTC_PID_Map());
    var G_EINTC_PID_Map_end := G_EINTC_PID_Map_start + G_WK_EINTC_PID_MAP_SZ;

    var G_Existing_PIDs_start := AddressOfGlobal(G_Existing_PIDs());
    var G_Existing_PIDs_end := G_Existing_PIDs_start + G_WK_Existing_PIDs_SZ;

    var G_PID_Counter_start := AddressOfGlobal(G_PID_Counter());
    var G_PID_Counter_end := G_PID_Counter_start + G_PID_Counter_SZ;

    var G_USBTD_Counter_start := AddressOfGlobal(G_USBTD_ID_Counter());
    var G_USBTD_Counter_end := G_USBTD_Counter_start + G_USBTD_Counter_SZ;

    var G_temp_usbtd_start := AddressOfGlobal(G_Temp_USBTD());
    var G_temp_usbtd_end := G_temp_usbtd_start + G_WK_Temp_USBTD_SZ;

    !(
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_USBTDs_MEM_start, G_USBTDs_MEM_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_WimpDrvs_Info_start, G_WimpDrvs_Info_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_EEHCIs_Info_start, G_EEHCIs_Info_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_EINTC_PID_Map_start, G_EINTC_PID_Map_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_Existing_PIDs_start, G_Existing_PIDs_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_PID_Counter_start, G_PID_Counter_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_start, G_EEHCI_MEM_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end) ||
        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_WimpDrvs_Info_start, G_WimpDrvs_Info_end) ||
        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end) ||
        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_EEHCIs_Info_start, G_EEHCIs_Info_end) ||
        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end) ||
        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_EINTC_PID_Map_start, G_EINTC_PID_Map_end) ||
        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_Existing_PIDs_start, G_Existing_PIDs_end) ||
        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_PID_Counter_start, G_PID_Counter_end) ||
        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_USBTDs_MEM_start, G_USBTDs_MEM_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end, G_WimpDrvs_Info_start, G_WimpDrvs_Info_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end, G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end, G_EEHCIs_Info_start, G_EEHCIs_Info_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end, G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end, G_EINTC_PID_Map_start, G_EINTC_PID_Map_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end, G_Existing_PIDs_start, G_Existing_PIDs_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end, G_PID_Counter_start, G_PID_Counter_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_EEHCI_MEM_PBASE_start, G_EEHCI_MEM_PBASE_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_WimpDrvs_Info_start, G_WimpDrvs_Info_end, G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end) ||
        is_mem_region_overlap(G_WimpDrvs_Info_start, G_WimpDrvs_Info_end, G_EEHCIs_Info_start, G_EEHCIs_Info_end) ||
        is_mem_region_overlap(G_WimpDrvs_Info_start, G_WimpDrvs_Info_end, G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end) ||
        is_mem_region_overlap(G_WimpDrvs_Info_start, G_WimpDrvs_Info_end, G_EINTC_PID_Map_start, G_EINTC_PID_Map_end) ||
        is_mem_region_overlap(G_WimpDrvs_Info_start, G_WimpDrvs_Info_end, G_Existing_PIDs_start, G_Existing_PIDs_end) ||
        is_mem_region_overlap(G_WimpDrvs_Info_start, G_WimpDrvs_Info_end, G_PID_Counter_start, G_PID_Counter_end) ||
        is_mem_region_overlap(G_WimpDrvs_Info_start, G_WimpDrvs_Info_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_WimpDrvs_Info_start, G_WimpDrvs_Info_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end, G_EEHCIs_Info_start, G_EEHCIs_Info_end) ||
        is_mem_region_overlap(G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end, G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end) ||
        is_mem_region_overlap(G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end, G_EINTC_PID_Map_start, G_EINTC_PID_Map_end) ||
        is_mem_region_overlap(G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end, G_Existing_PIDs_start, G_Existing_PIDs_end) ||
        is_mem_region_overlap(G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end, G_PID_Counter_start, G_PID_Counter_end) ||
        is_mem_region_overlap(G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_WimpDev_PID_Map_start, G_WimpDev_PID_Map_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_EEHCIs_Info_start, G_EEHCIs_Info_end, G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end) ||
        is_mem_region_overlap(G_EEHCIs_Info_start, G_EEHCIs_Info_end, G_EINTC_PID_Map_start, G_EINTC_PID_Map_end) ||
        is_mem_region_overlap(G_EEHCIs_Info_start, G_EEHCIs_Info_end, G_Existing_PIDs_start, G_Existing_PIDs_end) ||
        is_mem_region_overlap(G_EEHCIs_Info_start, G_EEHCIs_Info_end, G_PID_Counter_start, G_PID_Counter_end) ||
        is_mem_region_overlap(G_EEHCIs_Info_start, G_EEHCIs_Info_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_EEHCIs_Info_start, G_EEHCIs_Info_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end, G_EINTC_PID_Map_start, G_EINTC_PID_Map_end) ||
        is_mem_region_overlap(G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end, G_Existing_PIDs_start, G_Existing_PIDs_end) ||
        is_mem_region_overlap(G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end, G_PID_Counter_start, G_PID_Counter_end) ||
        is_mem_region_overlap(G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_WimpUSBPDev_DevList_start, G_WimpUSBPDev_DevList_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_EINTC_PID_Map_start, G_EINTC_PID_Map_end, G_Existing_PIDs_start, G_Existing_PIDs_end) ||
        is_mem_region_overlap(G_EINTC_PID_Map_start, G_EINTC_PID_Map_end, G_PID_Counter_start, G_PID_Counter_end) ||
        is_mem_region_overlap(G_EINTC_PID_Map_start, G_EINTC_PID_Map_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_EINTC_PID_Map_start, G_EINTC_PID_Map_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_Existing_PIDs_start, G_Existing_PIDs_end, G_PID_Counter_start, G_PID_Counter_end) ||
        is_mem_region_overlap(G_Existing_PIDs_start, G_Existing_PIDs_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_Existing_PIDs_start, G_Existing_PIDs_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_PID_Counter_start, G_PID_Counter_end, G_USBTD_Counter_start, G_USBTD_Counter_end) ||
        is_mem_region_overlap(G_PID_Counter_start, G_PID_Counter_end, G_temp_usbtd_start, G_temp_usbtd_end) ||

        is_mem_region_overlap(G_USBTD_Counter_start, G_USBTD_Counter_end, G_temp_usbtd_start, G_temp_usbtd_end)
    )
}




/*********************** Interface Realizations ********************/
// Interface realization: <global_read_uint32>
function global_read_uint32(gm: globalsmap, g:symbol, addr:addr): uint32
    requires WK_ValidGlobalVars_Decls(gm)
    requires is_valid_vaddr(addr)
    requires is_gvar_valid_vaddr(g, addr)
{
    global_read_word(gm, g, addr)
}

function global_write_at_vaddr32(gm: globalsmap, g:symbol, a:vaddr32, v:uint32): globalsmap
    requires WK_ValidGlobalVars_Decls(gm)
    requires is_valid_addr(a)
    requires is_valid_vaddr(a)
    requires is_gvar_valid_vaddr(g, a)
    ensures WK_ValidGlobalVars_Decls(global_write_at_vaddr32(gm, g, a, v))
{
    global_write_word(gm, g, a, v)
}

function global_read_at_vaddr32(gm: globalsmap, g:symbol, a:vaddr32): uint32
    requires WK_ValidGlobalVars_Decls(gm)
    requires is_valid_addr(a)
    requires is_valid_vaddr(a)
    requires is_gvar_valid_vaddr(g, a)
{
    global_read_word(gm, g, a)
}




/*********************** Utility Functions and Lemmas ********************/
predicate is_gvar_exist(g:symbol)
{
    g in WK_GlobalDecls()
}

predicate ValidGlobalDecls(decls:globaldecls)
{
    (forall d :: d in decls ==> decls[d] != 0) 
}

// Is <addr> points to a word of the global variable g
predicate is_gvar_valid_vaddr(g:symbol, addr:vaddr)
{
    is_gvar_exist(g) &&
    (AddressOfGlobal(g) <= addr < AddressOfGlobal(g) + gvar_get_size(g))
}

predicate is_gvar_valid_addr(g:symbol, addr:int)
{
    is_valid_addr(addr) && 
    is_valid_vaddr(addr) &&
    is_gvar_valid_vaddr(g, addr)
}

predicate ValidGlobalOffset(g:symbol, offset:int)
{
    is_gvar_exist(g) && 
    WordAligned(offset) &&
    0 <= offset < gvar_get_size(g)
}

// Predicate: All global variables except scratchpad ones are unchanged
predicate {:opaque} global_non_scratchpad_vars_are_unchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
{
    global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2, G_EEHCI_MEM()) &&
    global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM()) &&
    global_read_fullval(globals1, G_EEHCI_MEM_PBASE()) == global_read_fullval(globals2, G_EEHCI_MEM_PBASE()) &&
    global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info()) &&
    global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info()) &&
    global_read_fullval(globals1, G_EEHCIs_Info()) == global_read_fullval(globals2, G_EEHCIs_Info()) &&

    global_read_fullval(globals1, G_WimpUSBPDev_DevList()) == global_read_fullval(globals2, G_WimpUSBPDev_DevList()) &&
    global_read_fullval(globals1, G_EINTC_PID_Map()) == global_read_fullval(globals2, G_EINTC_PID_Map()) &&
    global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs()) &&
    global_read_fullval(globals1, G_PID_Counter()) == global_read_fullval(globals2, G_PID_Counter()) &&
    global_read_fullval(globals1, G_USBTD_ID_Counter()) == global_read_fullval(globals2, G_USBTD_ID_Counter()) &&

    (true)
}

predicate {:opaque} global_non_scratchpad_vars_except_counters_are_unchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
{
    global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2, G_EEHCI_MEM()) &&
    global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM()) &&
    global_read_fullval(globals1, G_EEHCI_MEM_PBASE()) == global_read_fullval(globals2, G_EEHCI_MEM_PBASE()) &&
    global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info()) &&
    global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info()) &&
    global_read_fullval(globals1, G_EEHCIs_Info()) == global_read_fullval(globals2, G_EEHCIs_Info()) &&

    global_read_fullval(globals1, G_WimpUSBPDev_DevList()) == global_read_fullval(globals2, G_WimpUSBPDev_DevList()) &&
    global_read_fullval(globals1, G_EINTC_PID_Map()) == global_read_fullval(globals2, G_EINTC_PID_Map()) &&
    global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs()) &&

    (true)
}

function method gvar_get_size(g:symbol): word
    requires is_gvar_exist(g)
{
    WK_GlobalDecls()[g]
}

function method gvar_read_fullval(s:WK_MState, g:symbol): seq<word>
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s))
    requires is_gvar_exist(g)
    ensures WordsToBytes(|gvar_read_fullval(s, g)|) == gvar_get_size(g)
{   
    reveal WK_ValidGlobalVars_Decls();
    wkm_get_globals(s)[g]
}

function method gvar_read_word_byoffset(s:WK_MState, g:symbol, offset:word): word
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s))
    requires is_gvar_exist(g)
    requires ValidGlobalOffset(g, offset)
{
    gvar_read_fullval(s, g)[BytesToWords(offset)]
}

function gvar_read_word_byaddr(s:WK_MState, g:symbol, addr:addr): word
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s))
    requires is_valid_vaddr(addr)
    requires is_gvar_valid_vaddr(g, addr)
{
    gvar_read_word_byoffset(s, g, addr - AddressOfGlobal(g))
}

function global_read_fullval(gm: globalsmap, g:symbol) : seq<word>
    requires WK_ValidGlobalVars_Decls(gm)
    requires is_gvar_exist(g)
{
    reveal WK_ValidGlobalVars_Decls();

    gm[g]
}

function global_read_word(gm: globalsmap, g:symbol, addr:addr): word
    requires WK_ValidGlobalVars_Decls(gm)
    requires is_valid_vaddr(addr)
    requires is_gvar_valid_vaddr(g, addr)
{
    reveal WK_ValidGlobalVars_Decls();

    var allwords := global_read_fullval(gm, g);
    allwords[BytesToWords(addr - AddressOfGlobal(g))]
}

function global_read_word_byoffset(gm: globalsmap, g:symbol, offset:word): word
    requires WK_ValidGlobalVars_Decls(gm)
    requires is_gvar_exist(g)
    requires ValidGlobalOffset(g, offset)
{
    reveal WK_ValidGlobalVars_Decls();

    var allwords := global_read_fullval(gm, g);
    allwords[BytesToWords(offset)]
}

// [TODO] Refactor wk_globals, x86_globals, and this function, such that architecture functions go to x86_* only 
function global_write_word(gm: globalsmap, g:symbol, a:addr, v:word): globalsmap
    requires WK_ValidGlobalVars_Decls(gm)
    requires is_valid_addr(a)
    requires is_valid_vaddr(a)
    requires is_gvar_valid_vaddr(g, a)
    ensures WK_ValidGlobalVars_Decls(global_write_word(gm, g, a, v))
{
    reveal WK_ValidGlobalVars_Decls();
    var old_vals := gm[g];
    var new_vals := old_vals[BytesToWords(a - AddressOfGlobal(g)) := v];

    gm[g := new_vals]
}

// Interface realization: <global_write_uint64>
function global_write_uint64(gm: globalsmap, g:symbol, a:addr, v:uint64): globalsmap
    requires WK_ValidGlobalVars_Decls(gm)
    requires is_gvar_valid_addr(g, a)
    requires is_gvar_valid_addr(g, a + ARCH_WORD_BYTES)
    ensures WK_ValidGlobalVars_Decls(global_write_uint64(gm, g, a, v))
{
    reveal WK_ValidGlobalVars_Decls();
    
    var low := UInt64Low(v);
    var high := UInt64High(v);

    var new_gm1 := global_write_word(gm, g, a, low);
    var new_gm2 := global_write_word(new_gm1, g, a + ARCH_WORD_BYTES, high);

    new_gm2
}

// Interface realization: <global_read_uint64>
function global_read_uint64(gm: globalsmap, g:symbol, addr:addr): uint64
    requires WK_ValidGlobalVars_Decls(gm)
    requires is_gvar_valid_addr(g, addr)
    requires is_gvar_valid_addr(g, addr + ARCH_WORD_BYTES)
{
    reveal WK_ValidGlobalVars_Decls();

    var low := global_read_word(gm, g, addr);
    var high := global_read_word(gm, g, addr + ARCH_WORD_BYTES);

    UInt64_FromTwoUInt32s(high, low)
}

// All global variables except <g> are unmodified between two states
predicate globals_other_gvar_unchanged(globals1:globalsmap, globals2:globalsmap, g:symbol)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires is_gvar_exist(g)
{
    forall g2 :: is_gvar_exist(g2) && g2 != g
        ==> global_read_fullval(globals1, g2) == global_read_fullval(globals2, g2)
}

// All global variables except <g> are unmodified between two states
predicate globals_other_gvar_unchanged_2vars(globals1:globalsmap, globals2:globalsmap, g1:symbol, g2:symbol)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires is_gvar_exist(g1)
    requires is_gvar_exist(g2)
{
    forall g3 :: is_gvar_exist(g3) && g3 != g1 && g3 != g2
        ==> global_read_fullval(globals1, g3) == global_read_fullval(globals2, g3)
}

// Function: Return the start physical address of the <G_EEHCI_MEM>
function eehci_mem_pbase(globals:globalsmap) : paddr
    requires WK_ValidGlobalVars_Decls(globals)
{
    global_read_word(globals, G_EEHCI_MEM_PBASE(), AddressOfGlobal(G_EEHCI_MEM_PBASE()))
}

// Function: Return the end (excluded) physical address of the <G_EEHCI_MEM>
function eehci_mem_pend(globals:globalsmap) : uint
    requires WK_ValidGlobalVars_Decls(globals)
{
    eehci_mem_pbase(globals) + G_EEHCI_MEM_SZ
}

lemma lemma_DistinctGlobals()
    ensures DistinctGlobals()
{
    reveal G_EEHCI_MEM();
    reveal G_USBTD_MAP_MEM();
    reveal G_EEHCI_MEM_PBASE();
    reveal G_WimpDrvs_Info();
    reveal G_WimpUSBPDev_Info();
    reveal G_EEHCIs_Info();

    reveal G_WimpUSBPDev_DevList();
    reveal G_EINTC_PID_Map();
    reveal G_Existing_PIDs();
    reveal G_PID_Counter();
    reveal G_USBTD_ID_Counter();
    reveal G_Temp_USBTD();
}