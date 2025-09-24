/*######################################################################
## Class Name: RF_Adapter
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .It converts RAL transaction methods to interface transactions in case of write method in Register File. 
######################################################################*/
class RF_Adapter extends uvm_reg_adapter;
    `uvm_object_utils(RF_Adapter)

    Reg_Block adapter_Reg_Block_inst; 

    function new(string name = "RF_Adapter");
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


        if (REG_item.l_status) // write
            begin
                rw.kind = UVM_WRITE;
                rw.addr = REG_item.l_addr;
                rw.data = REG_item.l_data;
    
                // Update the mirror value
               
                adapter_Reg_Block_inst.RF_REG[REG_item.l_addr].predict(REG_item.l_data); 
                `uvm_info ("adapter", $sformatf("bus2reg : addr=0x%0h data=0x%0h kind=%s status=%s REG_item.wr_a = %b REG_item.wr_b = %b", 
                                                rw.addr, 
                                                rw.data, 
                                                rw.kind.name(), 
                                                rw.status.name(),
                                                REG_item.we_a_i,
                                                REG_item.we_b_i), UVM_LOW);
            end
        
    endfunction
    
endclass : RF_Adapter
