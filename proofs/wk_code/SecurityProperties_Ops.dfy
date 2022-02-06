include "state_properties.s.dfy"
include "state_utils.s.dfy"
include "transition_constraints.s.dfy"
include "utils/model/utils_objs_secure_state.i.dfy"
include "drv/drv_ops_utils.gen.dfy"
include "os/os_ops.gen.dfy"

// [NOTE] These operations only have s:state as the input parameter, but not any other parameters. This is because  
// function parameters are on stacks in s:state
datatype WSM_Op   = // WK APIs 
                    WSM_WK_EmptyPartitionCreateOp()  | 
                    WSM_WK_EmptyPartitionDestroyOp() |
                    WSM_WimpDrv_ActivateOp() |
                    WSM_WimpDrv_DeactivateOp() |
                    WSM_USBPDev_ActivateOp() |
                    WSM_USBPDev_DeactivateOp() |

                    WSM_USBTD_slot_allocate_1slotOp() |
                    WSM_USBTD_slot_deallocate_1slotOp() |
                    WSM_USBTD_slot_submit_and_verify_qtd32Op() |
                    WSM_USBTD_slot_submit_and_verify_qh32Op() |

                    WSM_EEHCI_ActivateOp() |
                    WSM_EEHCI_DeactivateOp() |

                    WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevsOp() |
                    WSM_OS_Activate_MainMem_ByPAddrOp() |
                    WSM_OS_Deactivate_MainMem_ByPAddrOp() |

                    WSM_WimpDrv_Write_eEHCI_ConfigOp() |
                    WSM_WimpDrv_Read_eEHCI_ConfigOp() |
                    WSM_WimpDrv_Write_eEHCI_StatusOp() |
                    WSM_WimpDrv_Read_eEHCI_StatusOp() |
                    WSM_WimpDrv_Write_eEHCI_USBTDRegOp() |
                    WSM_WimpDrv_Read_eEHCI_USBTDRegOp() |

                    // I/O accesses outside APIs
                    WSM_OSDrvRead_ByPAddrOp(drv_sid:Subject_ID, paddr:PAddrRegion) |
                    WSM_OSDrvRead_ByPIOOp(drv_sid:Subject_ID, pio_addr:ioaddr) |
                    WSM_OSDrvRead_ByObjIDsOp(drv_sid:Subject_ID, read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>) |
                    WSM_OSDevRead_ByPAddrOp(dev_sid:Subject_ID, paddr:PAddrRegion) |
                    WSM_OSDevRead_ByPIOOp(dev_sid:Subject_ID, pio_addr:ioaddr) |
                    WSM_OSNonUSBPDevRead_ByObjIDsOp(dev_sid:Subject_ID, read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>) |

                    WSM_OSDrvWrite_ByPAddrOp(drv_sid:Subject_ID, paddr:PAddrRegion, new_v:string) |
                    WSM_OSDrvWrite_ByPIOOp(drv_sid:Subject_ID, pio_addr:ioaddr, new_v:string) |
                    WSM_OSDrvWrite_ByObjIDsOp(drv_sid:Subject_ID, wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>) |
                    WSM_OSDevWrite_ByPAddrOp(dev_sid:Subject_ID, paddr:PAddrRegion, new_v:string) |
                    WSM_OSDevWrite_ByPIOOp(dev_sid:Subject_ID, pio_addr:ioaddr, new_v:string) |
                    WSM_OSNonUSBPDevWrite_ByObjIDsOp(dev_sid:Subject_ID, wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>) |

                    WSM_WimpDrvRead_ByPAddrOp(drv_id_word:word, read_paddr_start:paddr, read_paddr_end:uint) |
                    WSM_WimpDrvWrite_ByPAddrOp(drv_id_word:word, paddr_start:paddr, paddr_end:uint, new_val:string) |
                    WSM_USBPDevRead_ByObjIDOp(usbpdev_addr:USBPDev_Addr, read_fds:set<FD_ID>, read_dos:set<DO_ID>) | 
                    WSM_USBPDevWrite_ByObjIDOp(usbpdev_addr:USBPDev_Addr, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |

                    WSM_EEHCIWriteOwnDO_ByOffsetOp(eehci_id_word:word, eehci_slot:word, offset:uint32, new_val1:word) |
                    WSM_EEHCIReadOwnObjs_ByOffsetOp(eehci_id_word:word, eehci_slot:word, offset:uint32) |
                    WSM_EEHCIReadUSBTD_BySlotIDOp(eehci_id_word:word, eehci_slot:word, usbtd_slot:word) |
                    WSM_EEHCIReadUSBPDevObj_ByObjIDOp(eehci_id_word:word, eehci_slot:word, fd_ids:set<FD_ID>, do_ids:set<DO_ID>) |
                    WSM_EEHCIWriteUSBPDevObj_ByObjIDOp(eehci_id_word:word, eehci_slot:word, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    WSM_EEHCIReadObjs_ByPAddrOp(eehci_id_word:word, eehci_slot:word, read_paddr_start:paddr, read_paddr_end:uint) |
                    WSM_EEHCIWriteObjs_ByPAddrOp(eehci_id_word:word, eehci_slot:word, write_paddr_start:paddr, write_paddr_end:uint, new_val:string)


datatype WSM_Trace = WSM_Trace(s0:state, ops:seq<WSM_Op>)




//******** Property of Each Operation ********//
predicate P_WSM_WK_EmptyPartitionCreateOp(s:state, op:WSM_Op)
    requires op.WSM_WK_EmptyPartitionCreateOp?
{
    WSM_WK_EmptyPartitionCreate_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WK_EmptyPartitionCreate_PostConditions(s, s', ws_d))
}

predicate P_WSM_WK_EmptyPartitionDestroyOp(s:state, op:WSM_Op)
    requires op.WSM_WK_EmptyPartitionDestroyOp?
{
    WSM_WK_EmptyPartitionDestroy_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WK_EmptyPartitionDestroy_PostConditions(s, s', ws_d))
}

predicate P_WSM_WimpDrv_ActivateOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrv_ActivateOp?
{
    WSM_WimpDrv_Activate_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrv_Activate_PostConditions(s, s', ws_d))
}

predicate P_WSM_WimpDrv_DeactivateOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrv_DeactivateOp?
{
    WSM_WimpDrv_Deactivate_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrv_Deactivate_PostConditions(s, s', ws_d))
}

predicate P_WSM_USBPDev_ActivateOp(s:state, op:WSM_Op)
    requires op.WSM_USBPDev_ActivateOp?
{
    WSM_USBPDev_Activate_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_USBPDev_Activate_PostConditions(s, s', ws_d))
}

predicate P_WSM_USBPDev_DeactivateOp(s:state, op:WSM_Op)
    requires op.WSM_USBPDev_DeactivateOp?
{
    WSM_USBPDev_Deactivate_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_USBPDev_Deactivate_PostConditions(s, s', ws_d))
}

predicate P_WSM_USBTD_slot_allocate_1slotOp(s:state, op:WSM_Op)
    requires op.WSM_USBTD_slot_allocate_1slotOp?
{
    WSM_USBTD_slot_allocate_1slot_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_USBTD_slot_allocate_1slot_PostConditions(s, s', ws_d))
}

predicate P_WSM_USBTD_slot_deallocate_1slotOp(s:state, op:WSM_Op)
    requires op.WSM_USBTD_slot_deallocate_1slotOp?
{
    WSM_USBTD_slot_deallocate_1slot_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_USBTD_slot_deallocate_1slot_PostConditions(s, s', ws_d))
}

predicate P_WSM_USBTD_slot_submit_and_verify_qtd32Op(s:state, op:WSM_Op)
    requires op.WSM_USBTD_slot_submit_and_verify_qtd32Op?
{
    WSM_USBTD_slot_submit_and_verify_qtd32_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_USBTD_slot_submit_and_verify_qtd32_PostConditions(s, s', ws_d))
}


predicate P_WSM_USBTD_slot_submit_and_verify_qh32Op(s:state, op:WSM_Op)
    requires op.WSM_USBTD_slot_submit_and_verify_qh32Op?
{
    WSM_USBTD_slot_submit_and_verify_qh32_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_USBTD_slot_submit_and_verify_qh32_PostConditions(s, s', ws_d))
}

predicate P_WSM_EEHCI_ActivateOp(s:state, op:WSM_Op)
    requires op.WSM_EEHCI_ActivateOp?
{
    WSM_EEHCI_Activate_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_EEHCI_Activate_PostConditions(s, s', ws_d))
}

predicate P_WSM_EEHCI_DeactivateOp(s:state, op:WSM_Op)
    requires op.WSM_EEHCI_DeactivateOp?
{
    WSM_EEHCI_Deactivate_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_EEHCI_Deactivate_PostConditions(s, s', ws_d))
}

predicate P_WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevsOp(s:state, op:WSM_Op)
    requires op.WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevsOp?
{
    WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_PostConditions(s, s', ws_d))
}

predicate P_WSM_OS_Activate_MainMem_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_OS_Activate_MainMem_ByPAddrOp?
{
    WSM_OS_Activate_MainMem_ByPAddr_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_OS_Activate_MainMem_ByPAddr_PostConditions(s, s', ws_d))
}

predicate P_WSM_OS_Deactivate_MainMem_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_OS_Deactivate_MainMem_ByPAddrOp?
{
    WSM_OS_Deactivate_MainMem_ByPAddr_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_OS_Deactivate_MainMem_ByPAddr_PostConditions(s, s', ws_d))
}

predicate P_WimpDrv_Write_eEHCI_ConfigOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrv_Write_eEHCI_ConfigOp?
{
    WSM_WimpDrv_Write_eEHCI_Config_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrv_Write_eEHCI_Config_PostConditions(s, s', ws_d))
}

predicate P_WimpDrv_Read_eEHCI_ConfigOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrv_Read_eEHCI_ConfigOp?
{
    WSM_WimpDrv_Read_eEHCI_Config_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrv_Read_eEHCI_Config_PostConditions(s, s', ws_d))
}

predicate P_WimpDrv_Write_eEHCI_StatusOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrv_Write_eEHCI_StatusOp?
{
    WSM_WimpDrv_Write_eEHCI_Status_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrv_Write_eEHCI_Status_PostConditions(s, s', ws_d))
}

predicate P_WimpDrv_Read_eEHCI_StatusOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrv_Read_eEHCI_StatusOp?
{
    WSM_WimpDrv_Read_eEHCI_Status_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrv_Read_eEHCI_Status_PostConditions(s, s', ws_d))
}

predicate P_WimpDrv_Write_eEHCI_USBTDRegOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrv_Write_eEHCI_USBTDRegOp?
{
    WSM_WimpDrv_Write_eEHCI_USBTDReg_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrv_Write_eEHCI_USBTDReg_PostConditions(s, s', ws_d))
}

predicate P_WimpDrv_Read_eEHCI_USBTDRegOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrv_Read_eEHCI_USBTDRegOp?
{
    WSM_WimpDrv_Read_eEHCI_USBTDReg_PreConditions(s)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrv_Read_eEHCI_USBTDReg_PostConditions(s, s', ws_d))
}




// I/O accesses outside APIs
predicate P_OSDrvRead_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_OSDrvRead_ByPAddrOp?
{
    WSM_OSDrvRead_ByPAddr_PreConditions(s, op.drv_sid, op.paddr)
    ==> (exists s':state, ws_d:bool :: WSM_OSDrvRead_ByPAddr_PostConditions(s, op.drv_sid, op.paddr, s', ws_d))
}

predicate P_OSDrvRead_ByPIOOp(s:state, op:WSM_Op)
    requires op.WSM_OSDrvRead_ByPIOOp?
{
    WSM_OSDrvRead_ByPIO_PreConditions(s, op.drv_sid, op.pio_addr)
    ==> (exists s':state, ws_d:bool :: WSM_OSDrvRead_ByPIO_PostConditions(s, op.drv_sid, op.pio_addr, s', ws_d))
}

predicate P_OSDrvRead_ByObjIDsOp(s:state, op:WSM_Op)
    requires op.WSM_OSDrvRead_ByObjIDsOp?
{
    WSM_OSDrvRead_ByObjIDs_PreConditions(s, op.drv_sid, op.read_tds, op.read_fds, op.read_dos)
    ==> (exists s':state, ws_d:bool :: WSM_OSDrvRead_ByObjIDs_PostConditions(s, op.drv_sid, op.read_tds, op.read_fds, op.read_dos, s', ws_d))
}

predicate P_OSDevRead_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_OSDevRead_ByPAddrOp?
{
    WSM_OSDevRead_ByPAddr_PreConditions(s, op.dev_sid, op.paddr)
    ==> (exists s':state, ws_d:bool :: WSM_OSDevRead_ByPAddr_PostConditions(s, op.dev_sid, op.paddr, s', ws_d))
}

predicate P_OSDevRead_ByPIOOp(s:state, op:WSM_Op)
    requires op.WSM_OSDevRead_ByPIOOp?
{
    WSM_OSDevRead_ByPIO_PreConditions(s, op.dev_sid, op.pio_addr)
    ==> (exists s':state, ws_d:bool :: WSM_OSDevRead_ByPIO_PostConditions(s, op.dev_sid, op.pio_addr, s', ws_d))
}

predicate P_OSNonUSBPDevRead_ByObjIDsOp(s:state, op:WSM_Op)
    requires op.WSM_OSNonUSBPDevRead_ByObjIDsOp?
{
    WSM_OSNonUSBPDevRead_ByObjIDs_PreConditions(s, op.dev_sid, op.read_tds, op.read_fds, op.read_dos)
    ==> (exists s':state, ws_d:bool :: WSM_OSNonUSBPDevRead_ByObjIDs_PostConditions(s, op.dev_sid, op.read_tds, op.read_fds, op.read_dos, s', ws_d))
}

predicate P_OSDrvWrite_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_OSDrvWrite_ByPAddrOp?
{
    WSM_OSDrvWrite_ByPAddr_PreConditions(s, op.drv_sid, op.paddr, op.new_v)
    ==> (exists s':state, ws_d:bool :: WSM_OSDrvWrite_ByPAddr_PostConditions(s, op.drv_sid, op.paddr, op.new_v, s', ws_d))
}

predicate P_OSDrvWrite_ByPIOOp(s:state, op:WSM_Op)
    requires op.WSM_OSDrvWrite_ByPIOOp?
{
    WSM_OSDrvWrite_ByPIO_PreConditions(s, op.drv_sid, op.pio_addr, op.new_v)
    ==> (exists s':state, ws_d:bool :: WSM_OSDrvWrite_ByPIO_PostConditions(s, op.drv_sid, op.pio_addr, op.new_v, s', ws_d))
}

predicate P_OSDrvWrite_ByObjIDsOp(s:state, op:WSM_Op)
    requires op.WSM_OSDrvWrite_ByObjIDsOp?
{
    WSM_OSDrvWrite_ByObjIDs_PreConditions(s, op.drv_sid, op.wsm_td_id_val_map, op.wsm_fd_id_val_map, op.wsm_do_id_val_map)
    ==> (exists s':state, ws_d:bool :: WSM_OSDrvWrite_ByObjIDs_PostConditions(s, op.drv_sid, op.wsm_td_id_val_map, op.wsm_fd_id_val_map, op.wsm_do_id_val_map, s', ws_d))
}

predicate P_OSDevWrite_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_OSDevWrite_ByPAddrOp?
{
    WSM_OSDevWrite_ByPAddr_PreConditions(s, op.dev_sid, op.paddr, op.new_v)
    ==> (exists s':state, ws_d:bool :: WSM_OSDevWrite_ByPAddr_PostConditions(s, op.dev_sid, op.paddr, op.new_v, s', ws_d))
}

predicate P_OSDevWrite_ByPIOOp(s:state, op:WSM_Op)
    requires op.WSM_OSDevWrite_ByPIOOp?
{
    WSM_OSDevWrite_ByPIO_PreConditions(s, op.dev_sid, op.pio_addr, op.new_v)
    ==> (exists s':state, ws_d:bool :: WSM_OSDevWrite_ByPIO_PostConditions(s, op.dev_sid, op.pio_addr, op.new_v, s', ws_d))
}

predicate P_OSNonUSBPDevWrite_ByObjIDsOp(s:state, op:WSM_Op)
    requires op.WSM_OSNonUSBPDevWrite_ByObjIDsOp?
{
    WSM_OSNonUSBPDevWrite_ByObjIDs_PreConditions(s, op.dev_sid, op.wsm_td_id_val_map, op.wsm_fd_id_val_map, op.wsm_do_id_val_map)
    ==> (exists s':state, ws_d:bool :: WSM_OSNonUSBPDevWrite_ByObjIDs_PostConditions(s, op.dev_sid, op.wsm_td_id_val_map, op.wsm_fd_id_val_map, op.wsm_do_id_val_map, s', ws_d))
}

predicate P_WimpDrvRead_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrvRead_ByPAddrOp?
{
    WSM_WimpDrvRead_ByPAddr_PreConditions(s, op.drv_id_word, op.read_paddr_start, op.read_paddr_end)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrvRead_ByPAddr_PostConditions(s, op.drv_id_word, op.read_paddr_start, op.read_paddr_end, s', ws_d))
}

predicate P_WimpDrvWrite_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_WimpDrvWrite_ByPAddrOp?
{
    WSM_WimpDrvWrite_ByPAddr_PreConditions(s, op.drv_id_word, op.paddr_start, op.paddr_end, op.new_val)
    ==> (exists s':state, ws_d:bool :: WSM_WimpDrvWrite_ByPAddr_PostConditions(s, op.drv_id_word, op.paddr_start, op.paddr_end, op.new_val, s', ws_d))
}

predicate P_USBPDevWrite_ByObjIDOp(s:state, op:WSM_Op)
    requires op.WSM_USBPDevWrite_ByObjIDOp?
{
    WSM_USBPDevWrite_ByObjID_PreConditions(s, op.usbpdev_addr, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists s':state, ws_d:bool :: WSM_USBPDevWrite_ByObjID_PostConditions(s, op.usbpdev_addr, op.fd_id_val_map, op.do_id_val_map, s', ws_d))
}

predicate P_USBPDevRead_ByObjIDOp(s:state, op:WSM_Op)
    requires op.WSM_USBPDevRead_ByObjIDOp?
{
    WSM_USBPDevRead_ByObjID_PreConditions(s, op.usbpdev_addr, op.read_fds, op.read_dos)
    ==> (exists s':state, ws_d:bool :: WSM_USBPDevRead_ByObjID_PostConditions(s, op.usbpdev_addr, op.read_fds, op.read_dos, s', ws_d))
}

predicate P_EEHCIWriteOwnDO_ByOffsetOp(s:state, op:WSM_Op)
    requires op.WSM_EEHCIWriteOwnDO_ByOffsetOp?
{
    WSM_EEHCIWriteOwnDO_ByOffset_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.offset, op.new_val1)
    ==> (exists s':state, ws_d:bool :: WSM_EEHCIWriteOwnDO_ByOffset_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.offset, op.new_val1, s', ws_d))
}

predicate P_EEHCIReadOwnObjs_ByOffsetOp(s:state, op:WSM_Op)
    requires op.WSM_EEHCIReadOwnObjs_ByOffsetOp?
{
    WSM_EEHCIReadOwnObjs_ByOffset_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.offset)
    ==> (exists s':state, ws_d:bool :: WSM_EEHCIReadOwnObjs_ByOffset_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.offset, s', ws_d))
}

predicate P_EEHCIReadUSBTD_BySlotIDOp(s:state, op:WSM_Op)
    requires op.WSM_EEHCIReadUSBTD_BySlotIDOp?
{
    WSM_EEHCIReadUSBTD_BySlotID_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.usbtd_slot)
    ==> (exists s':state, ws_d:bool :: WSM_EEHCIReadUSBTD_BySlotID_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.usbtd_slot, s', ws_d))
}

predicate P_EEHCIReadUSBPDevObj_ByObjIDOp(s:state, op:WSM_Op)
    requires op.WSM_EEHCIReadUSBPDevObj_ByObjIDOp?
{
    WSM_EEHCIReadUSBPDevObj_ByObjID_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.fd_ids, op.do_ids)
    ==> (exists s':state, ws_d:bool :: WSM_EEHCIReadUSBPDevObj_ByObjID_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.fd_ids, op.do_ids, s', ws_d))
}

predicate P_EEHCIWriteUSBPDevObj_ByObjIDOp(s:state, op:WSM_Op)
    requires op.WSM_EEHCIWriteUSBPDevObj_ByObjIDOp?
{
    WSM_EEHCIWriteUSBPDevObj_ByObjID_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists s':state, ws_d:bool :: WSM_EEHCIWriteUSBPDevObj_ByObjID_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.fd_id_val_map, op.do_id_val_map, s', ws_d))
}

predicate P_EEHCIReadObjs_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_EEHCIReadObjs_ByPAddrOp?
{
    WSM_EEHCIReadObjs_ByPAddr_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.read_paddr_start, op.read_paddr_end)
    ==> (exists s':state, ws_d:bool, wimpdrv_slot:word :: WSM_EEHCIReadObjs_ByPAddr_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.read_paddr_start, op.read_paddr_end, s', ws_d, wimpdrv_slot))
}

predicate P_EEHCIWriteObjs_ByPAddrOp(s:state, op:WSM_Op)
    requires op.WSM_EEHCIWriteObjs_ByPAddrOp?
{
    WSM_EEHCIWriteObjs_ByPAddr_PreConditions(s, op.eehci_id_word, op.eehci_slot, op.write_paddr_start, op.write_paddr_end, op.new_val)
    ==> (exists s':state, ws_d:bool, wimpdrv_idword:word :: WSM_EEHCIWriteObjs_ByPAddr_PostConditions(s, op.eehci_id_word, op.eehci_slot, op.write_paddr_start, op.write_paddr_end, op.new_val, s', ws_d, wimpdrv_idword))
}




//******** PreConditions and PostConditions of APIs ********//
// [NOTE] We must capture ALL pre-conditions of WK APIs and I/O accesses. And we only need to take a SUBSET of their
// post-conditions to prove Theorems
predicate WSM_WKAPI_Common_PreConditions(s:state)
{
    OpsSaneState(s) &&
    WSM_physical_EHCIs_must_be_inactive(s.subjects, s.activate_conds) &&
            // Requirement: physical EHCIs that map to ephemeral EHCIs must be inactive
    (
        var old_flags := x86_get_eflags(s.wk_mstate);
        !interrupts_enabled(old_flags)
    )
}

predicate WSM_Common_PostConditions(s:state, s':state)
    requires OpsSaneState(s)
{
    OpsSaneState(s') &&
    WSM_IsSecureOps(s, s')
}

predicate WSM_WK_EmptyPartitionCreate_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 19 * ARCH_WORD_BYTES;
        var stack_params_space := 2 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&

    (true)
}

predicate WSM_WK_EmptyPartitionCreate_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WK_EmptyPartitionCreate_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_WK_EmptyPartitionDestroy_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 25 * ARCH_WORD_BYTES;
        var stack_params_space := 1 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&

    (true)
}

predicate WSM_WK_EmptyPartitionDestroy_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WK_EmptyPartitionDestroy_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_WimpDrv_Activate_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 22 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
        var stack_params_space := 4 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space - ARCH_WORD_BYTES)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);

        var drv_id:word := stack_get_val(old_stack, old_esp);
        (drv_id != WimpDrv_ID_RESERVED_EMPTY) &&
        (WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id) in s.subjects.wimp_drvs)
            // Requirement: <drv_id> must exist in <wimp_drvs>
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);

        var new_wimpdrv_idword:word := stack_get_val(old_stack, old_esp);
        var new_do_pbase:word := stack_get_val(old_stack, old_esp + 2 * ARCH_WORD_BYTES);
        var new_do_pend:word := stack_get_val(old_stack, old_esp + 3 * ARCH_WORD_BYTES);
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, new_wimpdrv_idword);

        WK_ValidPMemRegion(new_do_pbase, new_do_pend) &&
            // Requirement: new_do_pbase must <= new_do_pend
        wimpdrv_registration_info_must_exist(s.subjects, s.objects, s.id_mappings, s.objs_addrs, new_wimpdrv_idword, new_do_pbase, new_do_pend)
            // Requirement: When registering a wimp driver, The given information must match the information in <subjs>,  
            // <objs>, <id_mappings>, and <objs_addrs>, as they store all wimp drivers that will be activated in the system
    ) &&

    (true)
}

predicate WSM_WimpDrv_Activate_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WimpDrv_Activate_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_WimpDrv_Deactivate_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 
                        FFI_PMem_ReleaseFromWimps_StackParamsWords * ARCH_WORD_BYTES;
        var stack_params_space := 1 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);
        var old_globals := wkm_get_globals(s.wk_mstate);

        var drv_slot:word := stack_get_val(old_stack, old_esp);
        (   wimpdrv_valid_slot_id(drv_slot) &&
            pids_is_existing_wimp_pid(old_globals, wimpdrv_get_pid(old_globals, drv_slot).v)
        )
            ==> (
                var wimpdrv_idword := wimpdrv_get_id_word(old_globals, drv_slot);
                var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
                wimpdrv_id in s.subjects.wimp_drvs
            )
            // Requirement: If the wimp driver is active in the record, then the corresponding <drv_id> must exist in 
            // <wimp_drvs>
            // [TODO][Issue 31] It is better to move s pre-condition into ValidState SIs
    ) &&
    
    (true)
}

predicate WSM_WimpDrv_Deactivate_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WimpDrv_Deactivate_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_USBPDev_Activate_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 22 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
        var stack_params_space := 3 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space - ARCH_WORD_BYTES)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);

        forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
            // Requirement: USBPDevs in the model/system must have <active_in_os> to be false
    ) &&
    
    (true)
}

predicate WSM_USBPDev_Activate_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_USBPDev_Activate_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_USBPDev_Deactivate_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 29 * ARCH_WORD_BYTES;
        var stack_params_space := 1 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);

        forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
            // Requirement: USBPDevs in the model/system must have <active_in_os> to be false
    ) &&
    
    (true)
}

predicate WSM_USBPDev_Deactivate_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_USBPDev_Deactivate_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_USBTD_slot_allocate_1slot_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 21 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
        var stack_params_space := 2 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space - ARCH_WORD_BYTES)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);

        var td_type:word := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
        (td_type == USBTDs_TYPE_QTD32) || (td_type == USBTDs_TYPE_QH32) || 
        (td_type == USBTDs_TYPE_iTD32) || (td_type == USBTDs_TYPE_siTD32)
            // Requirement: <td_type> must be one of the four types
    ) &&
    
    (true)
}

predicate WSM_USBTD_slot_allocate_1slot_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_USBTD_slot_allocate_1slot_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_USBTD_slot_deallocate_1slot_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 19 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 
                FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES;
        var stack_params_space := 2 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    
    (true)
}

predicate WSM_USBTD_slot_deallocate_1slot_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_USBTD_slot_deallocate_1slot_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_USBTD_slot_submit_and_verify_qtd32_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 68 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 
                FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES;
        var stack_params_space := 8 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space - ARCH_WORD_BYTES)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);
        var old_globals := wkm_get_globals(s.wk_mstate);

        var wimpdrv_slot:word := stack_get_val(old_stack, old_esp + 1 * ARCH_WORD_BYTES);

        (wimpdrv_valid_slot_id(wimpdrv_slot)
            ==> wimpdrv_do_get_flag(old_globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
        ) &&
        (wimpdrv_valid_slot_id(wimpdrv_slot)
            ==> (
                    var wimpdrv_idword := wimpdrv_get_id_word(old_globals, wimpdrv_slot);
                    wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY &&
                    (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
                     wimpdrv_id in s.subjects.wimp_drvs
                    )
            )
        )
            // Requirement: The wimp driver issuing the access must exist in the system
    ) &&
    
    (true)
}

predicate WSM_USBTD_slot_submit_and_verify_qtd32_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_USBTD_slot_submit_and_verify_qtd32_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_USBTD_slot_submit_and_verify_qh32_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 68 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 
                FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES;
        var stack_params_space := 9 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space - ARCH_WORD_BYTES)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);
        var old_globals := wkm_get_globals(s.wk_mstate);

        var wimpdrv_slot:word := stack_get_val(old_stack, old_esp + 1 * ARCH_WORD_BYTES);

        (wimpdrv_valid_slot_id(wimpdrv_slot)
            ==> wimpdrv_do_get_flag(old_globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
        ) &&
        (wimpdrv_valid_slot_id(wimpdrv_slot)
            ==> (
                var wimpdrv_idword := wimpdrv_get_id_word(old_globals, wimpdrv_slot);
                wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY &&
                (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
                 wimpdrv_id in s.subjects.wimp_drvs
                )
            )
        )
            // Requirement: The wimp driver issuing the access must exist in the system
    ) &&
    
    (true)
}

predicate WSM_USBTD_slot_submit_and_verify_qh32_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_USBTD_slot_submit_and_verify_qh32_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_EEHCI_Activate_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 
                        FFI_EEHCI_Activate_ReturnWords * ARCH_WORD_BYTES;
        var stack_params_space := 4 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    
    (true)
}

predicate WSM_EEHCI_Activate_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_EEHCI_Activate_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_EEHCI_Deactivate_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 
                        FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
        var stack_params_space := 1 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);
        var old_globals := wkm_get_globals(s.wk_mstate);

        var eehci_slot:word := stack_get_val(old_stack, old_esp);
        (   eehci_valid_slot_id(eehci_slot) &&
            pids_is_existing_wimp_pid(old_globals, eehci_info_get_pid(old_globals, eehci_slot).v)
        )
            ==> (
                var eehci_idword := eehci_mem_get_eehci_id(old_globals, eehci_slot);
                var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
                eehci_id in s.subjects.eehcis
            )
            // Requirement: If the eEHCI is active in the record, then the corresponding <dev_id> must exist in 
            // <eehcis>
            // [TODO][Issue 31] It is better to move this pre-condition into ValidState SIs
    ) &&
    
    (true)
}

predicate WSM_EEHCI_Deactivate_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_EEHCI_Deactivate_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 18 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
        var stack_params_space := 1 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);

        forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
            // Requirement: USBPDevs in the model/system must have <active_in_os> to be false
    ) &&
    
    (true)
}

predicate WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_OS_Activate_MainMem_ByPAddr_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 9 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
        var stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);

        ins_valid_pmem_activate_main_mem_in_os(s, old_esp)
    ) &&
    
    (true)
}

predicate WSM_OS_Activate_MainMem_ByPAddr_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_OS_Activate_MainMem_ByPAddr_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_OS_Deactivate_MainMem_ByPAddr_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 9 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
        var stack_params_space := FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);

        ins_valid_pmem_deactivate_main_mem_from_os(s, old_esp)
    ) &&
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);

        var paddr_end:word := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
        var paddr_start:word := stack_get_val(old_stack, old_esp);

        var dm := WSM_MapSecureState(s);
        P_OS_Deactivate_MainMem_ByPAddr_AdditonalPreConditions(s, dm, paddr_start, paddr_end)
    ) &&
    
    (true)
}

predicate WSM_OS_Deactivate_MainMem_ByPAddr_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_OS_Deactivate_MainMem_ByPAddr_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_WimpDrv_Access_eEHCI_Obj_PreConditions(
    s:state
)
    requires WSM_WKAPI_Common_PreConditions(s)
    requires var esp := x86_get_reg(s.wk_mstate, ESP);
            IsAddrInStack(esp + 2 * ARCH_WORD_BYTES)
{
    (
        var old_stack := wkm_stack_get_all(s.wk_mstate);
        var old_esp := x86_get_reg(s.wk_mstate, ESP);
        var old_globals := wkm_get_globals(s.wk_mstate);

        var wimpdrv_slot:word := stack_get_val(old_stack, old_esp);
        var eehci_slot:word := stack_get_val(old_stack, old_esp + 1 * ARCH_WORD_BYTES);

        (wimpdrv_valid_slot_id(wimpdrv_slot)
            ==> wimpdrv_do_get_flag(old_globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
        ) &&
        (wimpdrv_valid_slot_id(wimpdrv_slot)
            ==> (
                var wimpdrv_idword := wimpdrv_get_id_word(old_globals, wimpdrv_slot);
                wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY &&
                (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
                 wimpdrv_id in s.subjects.wimp_drvs
                )
            )
        ) &&
            // Requirement: The wimp driver issuing the access must exist in the system
        (eehci_valid_slot_id(eehci_slot)
            ==> (
                var eehci_idword := eehci_mem_get_eehci_id(old_globals, eehci_slot);
                eehci_idword != eEHCI_ID_INVALID &&
                (var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_idword);
                 eehci_id in s.subjects.eehcis
                )
            )
        )
            // Requirement: the eEHCI being accessed must be active and exist in the system
    ) &&
    
    (true)
}

predicate WSM_WimpDrv_Write_eEHCI_Config_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 28 * ARCH_WORD_BYTES;
        var stack_params_space := 3 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space - ARCH_WORD_BYTES)
    ) &&
    WSM_WimpDrv_Access_eEHCI_Obj_PreConditions(s) &&
    
    (true)
}

predicate WSM_WimpDrv_Write_eEHCI_Config_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WimpDrv_Write_eEHCI_Config_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_WimpDrv_Read_eEHCI_Config_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 28 * ARCH_WORD_BYTES;
        var stack_params_space := 2 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    WSM_WimpDrv_Access_eEHCI_Obj_PreConditions(s) &&
    
    (true)
}

predicate WSM_WimpDrv_Read_eEHCI_Config_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WimpDrv_Read_eEHCI_Config_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_WimpDrv_Write_eEHCI_Status_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 28 * ARCH_WORD_BYTES;
        var stack_params_space := 3 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space - ARCH_WORD_BYTES)
    ) &&
    WSM_WimpDrv_Access_eEHCI_Obj_PreConditions(s) &&
    
    (true)
}

predicate WSM_WimpDrv_Write_eEHCI_Status_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WimpDrv_Write_eEHCI_Status_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_WimpDrv_Read_eEHCI_Status_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 28 * ARCH_WORD_BYTES;
        var stack_params_space := 2 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    WSM_WimpDrv_Access_eEHCI_Obj_PreConditions(s) &&
    
    (true)
}

predicate WSM_WimpDrv_Read_eEHCI_Status_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WimpDrv_Read_eEHCI_Status_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_WimpDrv_Write_eEHCI_USBTDReg_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 29 * ARCH_WORD_BYTES;
        var stack_params_space := 4 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space - ARCH_WORD_BYTES)
    ) &&
    WSM_WimpDrv_Access_eEHCI_Obj_PreConditions(s) &&
    
    (true)
}

predicate WSM_WimpDrv_Write_eEHCI_USBTDReg_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WimpDrv_Write_eEHCI_USBTDReg_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}

predicate WSM_WimpDrv_Read_eEHCI_USBTDReg_PreConditions(
    s:state
)
{
    WSM_WKAPI_Common_PreConditions(s) &&
    (
        var stack_req_space := 28 * ARCH_WORD_BYTES;
        var stack_params_space := 3 * ARCH_WORD_BYTES;
        var esp := x86_get_reg(s.wk_mstate, ESP);

        IsAddrInStack(esp - stack_req_space) &&
        IsAddrInStack(esp + stack_params_space)
    ) &&
    WSM_WimpDrv_Access_eEHCI_Obj_PreConditions(s) &&
    
    (true)
}

predicate WSM_WimpDrv_Read_eEHCI_USBTDReg_PostConditions(
    s:state, 
    s':state, ws_d:bool
)
    requires WSM_WimpDrv_Read_eEHCI_USBTDReg_PreConditions(s)
{
    WSM_Common_PostConditions(s, s') &&

    (true)
}




//******** PreConditions and PostConditions of I/O Accesses other than APIs ********//
predicate WSM_OSDrvRead_ByPAddr_PreConditions(
    s:state,
    drv_sid:Subject_ID, paddr:PAddrRegion
)
{
    OpsSaneState(s) &&
    WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The driver is in the red partition

    paddr.paddr_start <= paddr.paddr_end &&
        // Requirement: Valid memory address

    (
        var t := OSDrvRead_ByPAddr_GetReadObjs(s, paddr);
        var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
        var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
        var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
        (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
            ==> id !in read_tds)
    ) &&

    (true)
}

predicate WSM_OSDrvRead_ByPAddr_PostConditions(
    s:state, 
    drv_sid:Subject_ID, paddr:PAddrRegion,
    s':state, ws_d:bool
)
    requires WSM_OSDrvRead_ByPAddr_PreConditions(s, drv_sid, paddr)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var t := OSDrvRead_ByPAddr_GetReadObjs(s, paddr);
        var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
        var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
        var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, read_tds, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_OSDrvRead_ByPIO_PreConditions(
    s:state,
    drv_sid:Subject_ID, pio_addr:ioaddr
)
{
    OpsSaneState(s) &&
    WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The driver is in the red partition

    (
        var t := OSDrvRead_ByPIO_GetReadObjs(s, pio_addr);
        var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
        var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
        var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
        (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
            ==> id !in read_tds)
    ) &&

    (true)
}

predicate WSM_OSDrvRead_ByPIO_PostConditions(
    s:state, 
    drv_sid:Subject_ID, pio_addr:ioaddr,
    s':state, ws_d:bool
)
    requires WSM_OSDrvRead_ByPIO_PreConditions(s, drv_sid, pio_addr)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var t := OSDrvRead_ByPIO_GetReadObjs(s, pio_addr);
        var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
        var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
        var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, read_tds, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_OSDrvRead_ByObjIDs_PreConditions(
    s:state,
    drv_sid:Subject_ID, read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
{
    OpsSaneState(s) &&
    WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The driver is in the red partition

    (
        P_OSDrvAccess_AccessActiveObjsOnly(s, read_tds, read_fds, read_dos) &&
        (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
            ==> id !in read_tds)
    ) &&

    (true)
}

predicate WSM_OSDrvRead_ByObjIDs_PostConditions(
    s:state, 
    drv_sid:Subject_ID, read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>,
    s':state, ws_d:bool
)
    requires WSM_OSDrvRead_ByObjIDs_PreConditions(s, drv_sid, read_tds, read_fds, read_dos)
{
    WSM_Common_PostConditions(s, s') &&

    (
        ws_d == true
                ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, read_tds, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_OSDevRead_ByPAddr_PreConditions(
    s:state,
    dev_sid:Subject_ID, paddr:PAddrRegion
)
{
    OpsSaneState(s) &&
    WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The device is in the red partition

    paddr.paddr_start <= paddr.paddr_end &&
        // Requirement: Valid memory address

    (
        var t := OSDevRead_ByPAddr_GetReadObjs(s, paddr);
        var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
        var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
        var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
        WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_OSDevRead_ByPAddr_PostConditions(
    s:state, 
    dev_sid:Subject_ID, paddr:PAddrRegion,
    s':state, ws_d:bool
)
    requires WSM_OSDevRead_ByPAddr_PreConditions(s, dev_sid, paddr)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var t := OSDevRead_ByPAddr_GetReadObjs(s, paddr);
        var read_tds := t.0; // IDs of TDs overlapping with the memory region <paddr>
        var read_fds := t.1; // IDs of FDs overlapping with the memory region <paddr>
        var read_dos := t.2; // IDs of DOs overlapping with the memory region <paddr>
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, read_tds, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_OSDevRead_ByPIO_PreConditions(
    s:state,
    dev_sid:Subject_ID, pio_addr:ioaddr
)
{
    OpsSaneState(s) &&
    WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The device is in the red partition

    (
        var t := OSDevRead_ByPIO_GetReadObjs(s, pio_addr);
        var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
        var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
        var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
        WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_OSDevRead_ByPIO_PostConditions(
    s:state, 
    dev_sid:Subject_ID, pio_addr:ioaddr,
    s':state, ws_d:bool
)
    requires WSM_OSDevRead_ByPIO_PreConditions(s, dev_sid, pio_addr)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var t := OSDevRead_ByPIO_GetReadObjs(s, pio_addr);
        var read_tds := t.0; // IDs of TDs located at the PIO addr <pio_addr>
        var read_fds := t.1; // IDs of FDs located at the PIO addr <pio_addr>
        var read_dos := t.2; // IDs of DOs located at the PIO addr <pio_addr>
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, read_tds, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_OSNonUSBPDevRead_ByObjIDs_PreConditions(
    s:state,
    dev_sid:Subject_ID, read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
{
    OpsSaneState(s) &&
    WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The device is in the red partition

    (
        WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_OSNonUSBPDevRead_ByObjIDs_PostConditions(
    s:state, 
    dev_sid:Subject_ID, read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>,
    s':state, ws_d:bool
)
    requires WSM_OSNonUSBPDevRead_ByObjIDs_PreConditions(s, dev_sid, read_tds, read_fds, read_dos)
{
    WSM_Common_PostConditions(s, s') &&

    (
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, read_tds, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_OSDrvWrite_ByPAddr_PreConditions(
    s:state,
    drv_sid:Subject_ID, paddr:PAddrRegion, new_v:string
)
{
    OpsSaneState(s) &&
    WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The driver is in the red partition

    paddr.paddr_start <= paddr.paddr_end &&
        // Requirement: Valid memory address

    (
        var t := OSDrvWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
        (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
            ==> id !in wsm_td_id_val_map)
    ) &&

    (
        var t1:= OSDrvWrite_ByPAddr_InnerFunc_Modification1(s, drv_sid, paddr, new_v);
        var t_s' := t1.0;
        OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(t_s') &&
        OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(t_s')
    ) &&

    (true)
}

predicate WSM_OSDrvWrite_ByPAddr_PostConditions(
    s:state, 
    drv_sid:Subject_ID, paddr:PAddrRegion, new_v:string,
    s':state, ws_d:bool
)
    requires WSM_OSDrvWrite_ByPAddr_PreConditions(s, drv_sid, paddr, new_v)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var t := OSDrvWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
    ) &&

    (true)
}

predicate WSM_OSDrvWrite_ByPIO_PreConditions(
    s:state,
    drv_sid:Subject_ID, pio_addr:ioaddr, new_v:string
)
{
    OpsSaneState(s) &&
    WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The driver is in the red partition

    (
        var t := OSDrvWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs located at the PIO addr <pio_addr>, and values to be written
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs located at the PIO addr <pio_addr>, and values to be written
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs located at the PIO addr <pio_addr>, and values to be written
        (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
            ==>id !in wsm_td_id_val_map)
    ) &&

    (
        var t1:= OSDrvWrite_ByPIO_InnerFunc_Modification1(s, drv_sid, pio_addr, new_v);
        var t_s' := t1.0;
        OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(t_s') &&
        OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(t_s')
    ) &&

    (true)
}

predicate WSM_OSDrvWrite_ByPIO_PostConditions(
    s:state, 
    drv_sid:Subject_ID, pio_addr:ioaddr, new_v:string,
    s':state, ws_d:bool
)
    requires WSM_OSDrvWrite_ByPIO_PreConditions(s, drv_sid, pio_addr, new_v)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var t := OSDrvWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs located at the PIO addr <pio_addr>, and values to be written
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs located at the PIO addr <pio_addr>, and values to be written
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs located at the PIO addr <pio_addr>, and values to be written
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
    ) &&

    (true)
}

predicate WSM_OSDrvWrite_ByObjIDs_PreConditions(
    s:state,
    drv_sid:Subject_ID, wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
{
    OpsSaneState(s) &&
    WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The driver is in the red partition

    (
        P_OSDrvAccess_AccessActiveObjsOnly(s, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map)) &&
        (forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
            ==>id !in wsm_td_id_val_map)
    ) &&

    (
        (forall id :: id in wsm_td_id_val_map
                ==> id !in s.objects.usbpdev_tds) &&
        (forall id :: id in wsm_fd_id_val_map
                ==> id !in s.objects.usbpdev_fds) &&
        (forall id :: id in wsm_do_id_val_map
                ==> id !in s.objects.usbpdev_dos)
    ) &&

    (
        var t1:= OSDrvWrite_ByObjIDs_InnerFunc_Modification1(s, drv_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
        var t_s' := t1.0;
        OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(t_s') &&
        OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(t_s')
    ) &&

    (true)
}

predicate WSM_OSDrvWrite_ByObjIDs_PostConditions(
    s:state, 
    drv_sid:Subject_ID, wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>,
    s':state, ws_d:bool
)
    requires WSM_OSDrvWrite_ByObjIDs_PreConditions(s, drv_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
{
    WSM_Common_PostConditions(s, s') &&

    (
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
    ) &&

    (true)
}

predicate WSM_OSDevWrite_ByPAddr_PreConditions(
    s:state,
    dev_sid:Subject_ID, paddr:PAddrRegion, new_v:string
)
{
    OpsSaneState(s) &&
    WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The device is in the red partition

    paddr.paddr_start <= paddr.paddr_end &&
        // Requirement: Valid memory address

    (
        var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
        WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
    ) &&

    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    (
        var dm := WSM_MapState(s);
        DM_IsValidState(dm) && DM_IsSecureState(dm)
    ) &&
        // Pre-conditions needed by <WSD_OSDevWrite_Stub>. These pre-conditions can be proved, but need to be specified here
    (
        var t1:= OSDevWrite_ByPAddr_InnerFunc(s, dev_sid, paddr, new_v);
        var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
        var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
        var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
        var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
        var t2 := WSD_OSDevWrite_Stub(WSM_MapState(s), dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        WSM_MapState(t1.0) == t2.0
    ) &&
        // Requirement: The modifications in this operation maps to the corresponding modifications in the WK design spec

    (true)
}

predicate WSM_OSDevWrite_ByPAddr_PostConditions(
    s:state, 
    dev_sid:Subject_ID, paddr:PAddrRegion, new_v:string,
    s':state, ws_d:bool
)
    requires WSM_OSDevWrite_ByPAddr_PreConditions(s, dev_sid, paddr, new_v)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var t := OSDevWrite_ByPAddr_GetWriteObjsValsPairs(s, paddr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
    ) &&

    (true)
}

predicate WSM_OSDevWrite_ByPIO_PreConditions(
    s:state,
    dev_sid:Subject_ID, pio_addr:ioaddr, new_v:string
)
{
    OpsSaneState(s) &&
    WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The device is in the red partition

    (
        var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
        WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
    ) &&

    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    (
        var dm := WSM_MapState(s);
        DM_IsValidState(dm) && DM_IsSecureState(dm)
    ) &&
        // Pre-conditions needed by <WSD_OSDevWrite_Stub>. These pre-conditions can be proved, but need to be specified here
    (
        var t1:= OSDevWrite_ByPIO_InnerFunc(s, dev_sid, pio_addr, new_v);
        var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0;
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1;
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2;
        var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
        var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
        var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
        var t2 := WSD_OSDevWrite_Stub(WSM_MapState(s), dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        WSM_MapState(t1.0) == t2.0
    ) &&
        // Requirement: The modifications in this operation maps to the corresponding modifications in the WK design spec

    (true)
}

predicate WSM_OSDevWrite_ByPIO_PostConditions(
    s:state, 
    dev_sid:Subject_ID, pio_addr:ioaddr, new_v:string,
    s':state, ws_d:bool
)
    requires WSM_OSDevWrite_ByPIO_PreConditions(s, dev_sid, pio_addr, new_v)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var t := OSDevWrite_ByPIO_GetWriteObjsValsPairs(s, pio_addr, new_v);
        var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := t.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
        var wsm_fd_id_val_map:map<FD_ID, FD_Val> := t.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
        var wsm_do_id_val_map:map<DO_ID, DO_Val> := t.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
    ) &&

    (true)
}

// [NOTE] Needs 100s to verify
predicate WSM_OSNonUSBPDevWrite_ByObjIDs_PreConditions(
    s:state,
    dev_sid:Subject_ID, wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
{
    OpsSaneState(s) &&
    WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid)) &&
    (WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
        // Requirement: The device is in the red partition

    WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map) &&

    (
        (forall id :: id in wsm_td_id_val_map
                ==> id !in s.objects.usbpdev_tds) &&
        (forall id :: id in wsm_fd_id_val_map
                ==> id !in s.objects.usbpdev_fds) &&
        (forall id :: id in wsm_do_id_val_map
                ==> id !in s.objects.usbpdev_dos)
    ) &&

    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    (
        var dm := WSM_MapState(s);
        DM_IsValidState(dm) && DM_IsSecureState(dm)
    ) &&
        // Pre-conditions needed by <WSD_OSDevWrite_Stub>. These pre-conditions can be proved, but need to be specified here
    (
        var t1:= OSNonUSBPDevWrite_ByObjIDs_InnerFunc(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map);
        var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
        var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
        var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;
        var t2 := WSD_OSDevWrite_Stub(WSM_MapState(s), dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        WSM_MapState(t1.0) == t2.0
    ) &&
        // Requirement: The modifications in this operation maps to the corresponding modifications in the WK design spec

    (true)
}

predicate WSM_OSNonUSBPDevWrite_ByObjIDs_PostConditions(
    s:state, 
    dev_sid:Subject_ID, wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>,
    s':state, ws_d:bool
)
    requires WSM_OSNonUSBPDevWrite_ByObjIDs_PreConditions(s, dev_sid, wsm_td_id_val_map, wsm_fd_id_val_map, wsm_do_id_val_map)
{
    WSM_Common_PostConditions(s, s') &&

    (
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_sid, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
    ) &&

    (true)
}

predicate WSM_WimpDrvRead_ByPAddr_PreConditions(
    s:state,
    drv_id_word:word, read_paddr_start:paddr, read_paddr_end:uint
)
{
    OpsSaneState(s) &&

    (
        drv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
        WSM_IsWimpDrvID(s.subjects, drv_id)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        wimpdrv_idword_in_record(globals, drv_id_word)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_id.sid) in pids_parse_g_wimp_pids(globals)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
        wimpdrv_do_get_paddr_base(globals, drv_slot) <= read_paddr_start < read_paddr_end <= wimpdrv_do_get_paddr_end(globals, drv_slot)
    ) &&

    (true)
}

predicate WSM_WimpDrvRead_ByPAddr_PostConditions(
    s:state, 
    drv_id_word:word, read_paddr_start:paddr, read_paddr_end:uint, 
    s':state, ws_d:bool
)
    requires WSM_WimpDrvRead_ByPAddr_PreConditions(s, drv_id_word, read_paddr_start, read_paddr_end)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
        var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_id.sid, {}, {}, {wimpdrv_do_id})
    ) &&

    (true)
}

predicate WSM_WimpDrvWrite_ByPAddr_PreConditions(
    s:state,
    drv_id_word:word, paddr_start:paddr, paddr_end:uint, new_val:string
)
{
    OpsSaneState(s) &&

    (
        drv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
        WSM_IsWimpDrvID(s.subjects, drv_id)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        wimpdrv_idword_in_record(globals, drv_id_word)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_id.sid) in pids_parse_g_wimp_pids(globals)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
        wimpdrv_do_get_paddr_base(globals, drv_slot) <= paddr_start < paddr_end <= wimpdrv_do_get_paddr_end(globals, drv_slot)
    ) &&

    (true)
}

predicate WSM_WimpDrvWrite_ByPAddr_PostConditions(
    s:state, 
    drv_id_word:word, paddr_start:paddr, paddr_end:uint, new_val:string,
    s':state, ws_d:bool
)
    requires WSM_WimpDrvWrite_ByPAddr_PreConditions(s, drv_id_word, paddr_start, paddr_end, new_val)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word);
        var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, drv_id.sid, {}, {}, {wimpdrv_do_id})
    ) &&

    (true)
}

predicate WSM_USBPDevRead_ByObjID_PreConditions(
    s:state,
    usbpdev_addr:USBPDev_Addr, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
{
    OpsSaneState(s) &&

    (
        var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
        usb_is_usbpdev_addr_valid(addr) &&
        usbpdev_addr != usb_parse_usbpdev_addr(addr)
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        WSM_IsUSBPDevID(s.subjects, dev_id)
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, {}, read_fds, read_dos)
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        forall fd_id2 :: fd_id2 in read_fds
            ==> fd_id2 in s.subjects.usbpdevs[dev_id].fd_ids
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        forall do_id2 :: do_id2 in read_dos
            ==> do_id2 in s.subjects.usbpdevs[dev_id].do_ids
    ) &&

    (true)
}

predicate WSM_USBPDevRead_ByObjID_PostConditions(
    s:state, 
    usbpdev_addr:USBPDev_Addr, read_fds:set<FD_ID>, read_dos:set<DO_ID>, 
    s':state, ws_d:bool
)
    requires WSM_USBPDevRead_ByObjID_PreConditions(s, usbpdev_addr, read_fds, read_dos)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {}, read_fds, read_dos)
    ) &&

    (true)
}

predicate WSM_USBPDevWrite_ByObjID_PreConditions(
    s:state,
    usbpdev_addr:USBPDev_Addr, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    OpsSaneState(s) &&

    (
        var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
        usb_is_usbpdev_addr_valid(addr) &&
        usbpdev_addr != usb_parse_usbpdev_addr(addr)
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        WSM_IsUSBPDevID(s.subjects, dev_id)
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, map[], fd_id_val_map, do_id_val_map)
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        forall fd_id2 :: fd_id2 in fd_id_val_map
            ==> fd_id2 in s.subjects.usbpdevs[dev_id].fd_ids
    ) &&

    (
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        forall do_id2 :: do_id2 in do_id_val_map
            ==> do_id2 in s.subjects.usbpdevs[dev_id].do_ids
    ) &&

    (true)
}

predicate WSM_USBPDevWrite_ByObjID_PostConditions(
    s:state, 
    usbpdev_addr:USBPDev_Addr, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    s':state, ws_d:bool
)
    requires WSM_USBPDevWrite_ByObjID_PreConditions(s, usbpdev_addr, fd_id_val_map, do_id_val_map)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var td_id_val_map:map<TD_ID, TD_Val> := map[];
        var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map))
    ) &&

    (true)
}

predicate WSM_EEHCIWriteOwnDO_ByOffset_PreConditions(
    s:state,
    eehci_id_word:word, eehci_slot:word, offset:uint32, new_val1:word
)
{
    OpsSaneState(s) &&

    (
        eehci_id_word != eEHCI_ID_INVALID &&
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_IsEEHCIDevID(s.subjects, dev_id)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_idword_in_record(globals, eehci_id_word) &&
        var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID) &&
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_INVALID) &&
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
    ) &&

    offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        var t_write_params := WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(s, eehci_id_word, dev_id, offset, new_val1);
        WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, t_write_params.0, t_write_params.1, t_write_params.2)
    ) &&

    (true)
}

predicate WSM_EEHCIWriteOwnDO_ByOffset_PostConditions(
    s:state, 
    eehci_id_word:word, eehci_slot:word, offset:uint32, new_val1:word,
    s':state, ws_d:bool
)
    requires WSM_EEHCIWriteOwnDO_ByOffset_PreConditions(s, eehci_id_word, eehci_slot, offset, new_val1)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        var t_write_params := WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(s, eehci_id_word, dev_id, offset, new_val1);
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, MapGetKeys(t_write_params.0), MapGetKeys(t_write_params.1), MapGetKeys(t_write_params.2))
    ) &&

    (true)
}

predicate WSM_EEHCIReadOwnObjs_ByOffset_PreConditions(
    s:state,
    eehci_id_word:word, eehci_slot:word, offset:uint32
)
{
    OpsSaneState(s) &&

    (
        eehci_id_word != eEHCI_ID_INVALID &&
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_IsEEHCIDevID(s.subjects, dev_id)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_idword_in_record(globals, eehci_id_word) &&
        var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
    ) &&

    (
        offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset || offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset ||
        offset == G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset || offset == G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset ||
        offset in eehci_usbtd_regs_offsets()
    ) &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        var t_read_objs := WSM_EEHCIRead_OwnRegsToIDs(s, eehci_id_word, dev_id, offset);
        WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, t_read_objs.0, t_read_objs.1, t_read_objs.2)
    ) &&

    (true)
}

predicate WSM_EEHCIReadOwnObjs_ByOffset_PostConditions(
    s:state, 
    eehci_id_word:word, eehci_slot:word, offset:uint32,
    s':state, ws_d:bool
)
    requires WSM_EEHCIReadOwnObjs_ByOffset_PreConditions(s, eehci_id_word, eehci_slot, offset)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        var t_read_objs := WSM_EEHCIRead_OwnRegsToIDs(s, eehci_id_word, dev_id, offset);
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, t_read_objs.0, t_read_objs.1, t_read_objs.2)
    ) &&

    (true)
}

predicate WSM_EEHCIReadUSBTD_BySlotID_PreConditions(
    s:state,
    eehci_id_word:word, eehci_slot:word, usbtd_slot:word
)
{
    OpsSaneState(s) &&

    (
        eehci_id_word != eEHCI_ID_INVALID &&
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_IsEEHCIDevID(s.subjects, dev_id)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_idword_in_record(globals, eehci_id_word) &&
        var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
    ) &&

    (
        usbtd_slot != USBTD_SlotID_INVALID
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        CanActiveEEHCIReadUSBTD(globals, eehci_slot, usbtd_slot)
    ) &&

    (true)
}

predicate WSM_EEHCIReadUSBTD_BySlotID_PostConditions(
    s:state, 
    eehci_id_word:word, eehci_slot:word, usbtd_slot:word,
    s':state, ws_d:bool
)
    requires WSM_EEHCIReadUSBTD_BySlotID_PreConditions(s, eehci_id_word, eehci_slot, usbtd_slot)
{
    WSM_Common_PostConditions(s, s') &&

    (
        usbtd_map_valid_slot_id(usbtd_slot)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        isUInt32(USBTD_SLOT_FLAG_SlotSecure_Bit) &&
        TestBit(usbtd_map_get_flags(globals, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
    ) &&
        
    (
        var globals := wkm_get_globals(s.wk_mstate);
        usbtd_map_get_pid(globals, usbtd_slot) != WS_PartitionID(PID_INVALID)
    ) &&
        // Properties needed by the following properties
    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        var td_id := EEHCIReadUSBTD_CanActiveEEHCIReadUSBTD_Property(s, eehci_id_word, eehci_slot, usbtd_slot);
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {td_id}, {}, {})
    ) &&

    (true)
}

predicate WSM_EEHCIReadUSBPDevObj_ByObjID_PreConditions(
    s:state,
    eehci_id_word:word, eehci_slot:word, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
{
    OpsSaneState(s) &&

    (
        eehci_id_word != eEHCI_ID_INVALID &&
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_IsEEHCIDevID(s.subjects, dev_id)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_idword_in_record(globals, eehci_id_word) &&
        var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
    ) &&

    (
        forall id :: id in fd_ids
            ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD(s, eehci_slot, id)
    ) &&

    (
        forall id :: id in do_ids
            ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DO(s, eehci_slot, id)
    ) &&

    (true)
}

predicate WSM_EEHCIReadUSBPDevObj_ByObjID_PostConditions(
    s:state, 
    eehci_id_word:word, eehci_slot:word, fd_ids:set<FD_ID>, do_ids:set<DO_ID>,
    s':state, ws_d:bool
)
    requires WSM_EEHCIReadUSBPDevObj_ByObjID_PreConditions(s, eehci_id_word, eehci_slot, fd_ids, do_ids)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {}, fd_ids, do_ids)
    ) &&

    (true)
}

predicate WSM_EEHCIWriteUSBPDevObj_ByObjID_PreConditions(
    s:state,
    eehci_id_word:word, eehci_slot:word, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    OpsSaneState(s) &&

    (
        eehci_id_word != eEHCI_ID_INVALID &&
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_IsEEHCIDevID(s.subjects, dev_id)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_idword_in_record(globals, eehci_id_word) &&
        var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID) &&
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_INVALID) &&
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
    ) &&

    (
        (forall id :: id in fd_id_val_map
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD(s, eehci_slot, id)) &&
        (forall id :: id in do_id_val_map
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DO(s, eehci_slot, id))
    ) &&

    (
        (forall id :: id in fd_id_val_map
                ==> fd_id_val_map[id].v in usbpdev_string_range_for_fds_dos(s.subjects, EEHCIAccessUSBPDevObj_GetTargetUSBPDevID(s, id.oid), id.oid)) &&
        (forall id :: id in do_id_val_map
                ==> do_id_val_map[id].v in usbpdev_string_range_for_fds_dos(s.subjects, EEHCIAccessUSBPDevObj_GetTargetUSBPDevID(s, id.oid), id.oid))
    ) &&

    (true)
}

predicate WSM_EEHCIWriteUSBPDevObj_ByObjID_PostConditions(
    s:state, 
    eehci_id_word:word, eehci_slot:word, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    s':state, ws_d:bool
)
    requires WSM_EEHCIWriteUSBPDevObj_ByObjID_PreConditions(s, eehci_id_word, eehci_slot, fd_id_val_map, do_id_val_map)
{
    WSM_Common_PostConditions(s, s') &&

    (
        var td_id_val_map:map<TD_ID, TD_Val> := map[];
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, MapGetKeys(td_id_val_map), MapGetKeys(fd_id_val_map), MapGetKeys(do_id_val_map))
    ) &&

    (true)
}

predicate WSM_EEHCIReadObjs_ByPAddr_PreConditions(
    s:state,
    eehci_id_word:word, eehci_slot:word, read_paddr_start:paddr, read_paddr_end:uint
)
{
    OpsSaneState(s) &&

    (
        eehci_id_word != eEHCI_ID_INVALID &&
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_IsEEHCIDevID(s.subjects, dev_id)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_idword_in_record(globals, eehci_id_word) &&
        var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_INVALID)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
    ) &&

    (
        read_paddr_start < read_paddr_end
    ) &&

    (
        EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer(s, eehci_slot, read_paddr_start, read_paddr_end)
    ) &&

    (true)
}

predicate WSM_EEHCIReadObjs_ByPAddr_PostConditions(
    s:state, 
    eehci_id_word:word, eehci_slot:word, read_paddr_start:paddr, read_paddr_end:uint,
    s':state, ws_d:bool, wimpdrv_slot:word
)
    requires WSM_EEHCIReadObjs_ByPAddr_PreConditions(s, eehci_id_word, eehci_slot, read_paddr_start, read_paddr_end)
{
    WSM_Common_PostConditions(s, s') &&

    (
        wimpdrv_valid_slot_id(wimpdrv_slot) &&
        wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, read_paddr_start, read_paddr_end)
    ) &&

    (
        var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
        wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
        WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
    ) &&
        // Properties needed by the following properties
    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
        var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
        ws_d == true
            ==> WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {}, {}, {wimpdrv_do_id})
    ) &&

    (true)
}

predicate WSM_EEHCIWriteObjs_ByPAddr_PreConditions(
    s:state,
    eehci_id_word:word, eehci_slot:word, write_paddr_start:paddr, write_paddr_end:uint, new_val:string
)
{
    OpsSaneState(s) &&

    (
        eehci_id_word != eEHCI_ID_INVALID &&
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_IsEEHCIDevID(s.subjects, dev_id)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_idword_in_record(globals, eehci_id_word) &&
        var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID) &&
        eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    (
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_INVALID) &&
        WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
            != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
    ) &&

    (
        write_paddr_start < write_paddr_end
    ) &&

    (
        EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer(s, eehci_slot, write_paddr_start, write_paddr_end)
    ) &&

    (true)
}

predicate WSM_EEHCIWriteObjs_ByPAddr_PostConditions(
    s:state, 
    eehci_id_word:word, eehci_slot:word, write_paddr_start:paddr, write_paddr_end:uint, new_val:string,
    s':state, ws_d:bool, wimpdrv_idword:word
)
    requires WSM_EEHCIWriteObjs_ByPAddr_PreConditions(s, eehci_id_word, eehci_slot, write_paddr_start, write_paddr_end, new_val)
{
    WSM_Common_PostConditions(s, s') &&

    (
        wimpdrv_idword_in_record(wkm_get_globals(s.wk_mstate), wimpdrv_idword) &&
        (wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY) 
    ) &&

    (
        WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword) in s.subjects.wimp_drvs
        
    ) &&

    (
        var globals := wkm_get_globals(s.wk_mstate);
        var drv_slot := wimpdrv_get_slot_by_idword(globals, wimpdrv_idword);
        wimpdrv_do_get_paddr_base(globals, drv_slot) <= write_paddr_start < write_paddr_end <= wimpdrv_do_get_paddr_end(globals, drv_slot)
    ) &&

    (
        var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
        var new_do_val:DO_Val := wimpdrv_write_do_get_do_val(s, wimpdrv_idword, write_paddr_start, write_paddr_end, new_val);
        var do_id_val_map := map[wimpdrv_do_id := new_do_val];
        var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
        ws_d == true
            ==> WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s, dev_id.sid, {}, {}, MapGetKeys(do_id_val_map))
    ) &&

    (true)
}