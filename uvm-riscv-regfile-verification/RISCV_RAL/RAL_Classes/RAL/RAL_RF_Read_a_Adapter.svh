/*######################################################################
## Class Name: RF_Read_a_Adapter
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .It converts RAL transaction methods to interface transactions in case of read method for port a in Register File.
######################################################################*/
class RF_Read_a_Adapter extends uvm_reg_adapter;
    `uvm_object_utils(RF_Read_a_Adapter)

    function new(string name = "RF_Read_a_Adapter");
        super.new(name);
    endfunction

    virtual function uvm_sequence_item reg2bus (const ref uvm_reg_bus_op rw);
        Register_File_Sequence_Item REG_item;
        return REG_item;
    endfunction


    virtual function void bus2reg (uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
        Register_File_Sequence_Item REG_item;

        if (! $cast (REG_item, bus_item)) begin
            `uvm_fatal ("reg2apb_adapter", "Failed to cast bus_item to REG_item")
        end

                rw.kind = UVM_READ;
                rw.addr = REG_item.raddr_a_i;
                rw.data = REG_item.rdata_a_o;                

        
        `uvm_info ("read_a_adapter", $sformatf("bus2reg : addr=0x%0h data=0x%0h kind=%s status=%s", 
                                        rw.addr, 
                                        rw.data, 
                                        rw.kind.name(), 
                                        rw.status.name()), UVM_LOW);
    endfunction
    
endclass : RF_Read_a_Adapter
