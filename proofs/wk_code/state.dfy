include "../DetailedModel/Syntax.dfy"
include "utils/common/headers.dfy"
include "arch/x86/x86_mstate.dfy"
include "dev/usb2/usb_def.dfy"

/*********************** Define Machine State ********************/
// Drivers can access bus controllers to access objects of devices on lower-level buses (e.g., I2C buses, USB buses). 
// These objects only have abstract object IDs and states
datatype IDRef_DevObjs = IDRef_DevObjs(
                                    tds:map<TD_ID, TD_Val>,
                                    fds:map<FD_ID, FD_Val>,
                                    dos:map<DO_ID, DO_Val>
                            )


/*********************** States for Subjects and Objects ********************/
//// Machine representation of Partition ID. Value must be a uint32 number.
datatype WS_PartitionID = WS_PartitionID(v:uint32)

datatype PAddrRegion = PAddrRegion(paddr_start:paddr, paddr_end:uint)
datatype ObjAddrs = ObjAddrs(paddrs:set<PAddrRegion>, pio_addrs:set<ioaddr>)




/*********************** For Wimp Partitions ********************/
datatype WimpDrv = WimpDrv(
                        do_id:DO_ID
                    )

datatype eEHCI   = eEHCI(
                        hcoded_td_id:TD_ID,
                        
                        // Map of register memory offsets to object IDs
                        map_td_ids:map<uint32, TD_ID>,
                        map_fd_ids:map<uint32, FD_ID>,
                        map_do_ids:map<uint32, DO_ID>,

                        // For prove convience, we store the set of eEHCI TDs/FDs/DOs, even though they can be computed
                        // from the fields above
                        td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
                    )

datatype USB_PDevice = USB_PDevice(
                        active_in_os:bool, // If the device is currently active in OS partition
                        hcoded_td_id:TD_ID,
                        fd_ids:set<FD_ID>, do_ids:set<DO_ID>
                    )

/*********************** For OS Partition ********************/
datatype OS_Drv = OS_Drv(
                            pid:WS_PartitionID, 
                            td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
                    )

// Devices in the OS partition can be abstract devices, because their capabilities to access wimp device and drivers 
// are limited by (1) IOMMU, (2) wimp devices do not use PIO
datatype OS_Dev = OS_Dev(
                            pid:WS_PartitionID, 
                            hcoded_td_id:TD_ID, // Hardcoded TD
                            td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
                                
                            // [TODO] Interrupts require additional work; e.g., are we targeting fixed pin-based
                            // PCI interrupts, or MSI?
                        )

datatype OS_TD_Trans_Param = OS_TD_Trans_Param(amodes:set<AMode>, vals:set<OS_TD_Val>) 
datatype OS_TD_Val      = OS_TD_Val(
                                trans_params_tds_atpaddr:map<PAddrRegion, OS_TD_Trans_Param>,
                                trans_params_fds_atpaddr:map<PAddrRegion, FD_Trans_Param>,
                                trans_params_dos_atpaddr:map<PAddrRegion, DO_Trans_Param>,
                                
                                trans_params_tds_atpio:map<ioaddr, OS_TD_Trans_Param>,
                                trans_params_fds_atpio:map<ioaddr, FD_Trans_Param>,
                                trans_params_dos_atpio:map<ioaddr, DO_Trans_Param>,

                                trans_params_tds_atoid:map<TD_ID, OS_TD_Trans_Param>,
                                trans_params_fds_atoid:map<FD_ID, FD_Trans_Param>,
                                trans_params_dos_atoid:map<DO_ID, DO_Trans_Param>
                        )

datatype OS_TD_State    = OS_TD_State(pid:WS_PartitionID, val:OS_TD_Val) 
                                // State of Transfer Descriptor (TD)
datatype OS_FD_State    = OS_FD_State(pid:WS_PartitionID, val:FD_Val)
                                // State of Function Descriptor (FD)
datatype OS_DO_State    = OS_DO_State(pid:WS_PartitionID, val:DO_Val)
                                // State of Data Object (DO)

datatype WSM_Subjects = WSM_Subjects(
                                wimp_drvs:map<Drv_ID, WimpDrv>,
                                eehcis:map<Dev_ID, eEHCI>,
                                usbpdevs:map<Dev_ID, USB_PDevice>, 
                                // [TODO] Ephemeral interrupt controllers and interrupts require additional work

                                os_drvs:map<Drv_ID, OS_Drv>,
                                os_devs:map<Dev_ID, OS_Dev>
                        )


datatype WSM_Objects = WSM_Objects(
                                // Objects in the OS partition are abstract. We assume functions that convert memory 
                                // state, PIO state, addtional device objects state (e.g., registers of device on lower
                                // level buses) to abstract OS objects always exists. In other words, we assume certain
                                // Dafny functions can relate these state to the abstract states of these objects
                                // [NOTE] WSM_Objects does not contain the *_Val of OS objects, because those info
                                // can be calculated from IO_MState
                                os_tds:map<TD_ID, OS_TD_State>,
                                os_fds:map<FD_ID, OS_FD_State>,
                                os_dos:map<DO_ID, OS_DO_State>,

                                // Objects in wimp partitions. The state of these objects corrspondes to the memory 
                                // content of these objects, which is enforced by SIs.
                                // [NOTE] <wimp> contains both wimp drivers and WK
                                // [NOTE] eehci_* do not contain the values here, because they are stored in WK_MState
                                eehci_hcoded_tds:map<TD_ID, TD_Val>,
                                eehci_other_tds:set<TD_ID>,
                                eehci_fds:set<FD_ID>,
                                eehci_dos:set<DO_ID>,
                                usbpdev_tds:map<TD_ID, TD_Val>,
                                usbpdev_fds:map<FD_ID, FD_Val>,
                                usbpdev_dos:map<DO_ID, DO_Val>,
                                wimpdrv_dos:map<DO_ID, DO_Val>,

                                usbtd_tds:set<TD_ID>,
                                usbtd_fds:set<FD_ID>,
                                usbtd_dos:set<DO_ID>
                            )

datatype WSM_Objects_Addrs = WSM_Objects_Addrs(
                                tds_addrs:map<TD_ID, ObjAddrs>,
                                fds_addrs:map<FD_ID, ObjAddrs>,
                                dos_addrs:map<DO_ID, ObjAddrs>
                            )

// ID mappings
// [NOTE] All valid words are keys in the mappings, but only a subset of them map to Drv_IDs/Dev_IDs exist in the system
// [NOTE] One must not use slot IDs as subjects' IDs, because a slot may represent two different subjects at *different*
// time
datatype WSM_ID_Mappings = WSM_ID_Mappings(
                                wimpdrv_ids:map<word, Drv_ID>,
                                eehci_ids:map<word, Dev_ID>,
                                usbpdev_ids:map<USBPDev_Addr, Dev_ID>,

                                // [Assumption] Each USB TD contains one TD, FD and DO.
                                // This makes sense because we can combine multiple TD/FD/DO as a single one
                                usbtd_to_td:map<word, TD_ID>,
                                usbtd_to_fd:map<word, FD_ID>,
                                usbtd_to_do:map<word, DO_ID>
                            )

datatype WSM_Dev_Activate_Conditions = WSM_Dev_Activate_Conditions(
                        ehci_activate_cond:map<Dev_ID, set<Dev_ID>>
                    )

type PMem_Active_Map = map<paddr, bool>

// WSM stands for "wimp system model"
datatype state = WSM_State(
                        // Machine state
                        wk_mstate:WK_MState,    // Machine state of WK

                        // Abstract machine state in addition
                        //// All subjects
                        subjects:WSM_Subjects,
                        //// All objects, which correspond their machine state
                        objects:WSM_Objects,
                        objs_addrs:WSM_Objects_Addrs,

                        id_mappings:WSM_ID_Mappings,

                        // Activate conditions of devices
                        activate_conds:WSM_Dev_Activate_Conditions,

                        ok:bool,

                        // Ghost vars. They are not state variables.
                        //// By recording which memory regions are active in the OS partition, one can decide what 
                        //// subjects and objects are active in the OS partition.
                        //// [NOTE] This ghost variable eases the proof of the commutative diagram by assuming a function,
                        //// which outputs the subjects and objects can be activated in the OS partition. 
                        //// [NOTE] This variable is not a state variable. Incorrect updates to this variable only causes
                        //// subjects and objects that should be active in the OS partition are not active.
                        ghost os_mem_active_map:PMem_Active_Map
                    )



/*
datatype OSDrv = OSDrv(
                        // Partition ID. The OS driver must be either active in the red partition, or inactive
                        pid:WS_PartitionID,

                        // I/O objects in the red driver
                        objs:Map<PAddrRegion, MemObj>
                    )

// [TODO-Important] How to move (memory) I/O objects from red partition to WK and WimpDrvs?
//      - For I/O objects movement to WK, WK's memory contains inactive external objects at the intial state 
//      - For I/O objects movement to WimpDrv, deactivate the set of all related objects and activate the DO in wimp drv
//          - OS (1) unmaps memory by calling mHV to deactivate these I/O objects, then (2) calls WK to create a 
//            partition, and activate Wimp drv (and activate its DO) by mapping the driver and these objects in a 
//            (SecApp's) page table (the partition ID could be the PAddr of the page table root address), wimp driver 
//            ID is given by OS (e.g., the wimp driver ID is generated)

