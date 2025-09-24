class DM_Adapter extends uvm_reg_adapter;
    `uvm_object_utils(DM_Adapter)

    Reg_Block adapter_Reg_Block_inst; 

    function new(string name = "DM_Adapter");
        super.new(name);
    endfunction

    virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
        Data_Memory_Seq_Item tr = Data_Memory_Seq_Item::type_id::create("tr");
        `uvm_info("ADAPTER", $sformatf("Reg2Bus: offset=0x%0h, value=0x%0h", rw.addr, rw.data), UVM_LOW);
        return tr;
    endfunction

    virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
        Data_Memory_Seq_Item tr;

        if(!$cast(tr, bus_item)) begin
          `uvm_fatal("CASTFAIL", "Failed to cast bus_item to Data_Memory_Seq_Item")
          return;
        end
        
        if (adapter_Reg_Block_inst == null) 
			begin
				`uvm_fatal("ADAPTER", "adapter_Reg_Block_inst is NULL in run_phase")
			end

        rw.kind     = tr.data_we_o ? UVM_WRITE : UVM_READ;
        rw.addr     = tr.address;
        rw.status   = UVM_IS_OK;

        if (rw.kind == UVM_WRITE)
            begin
                rw.data = tr.data;
                adapter_Reg_Block_inst.Memory.Write(tr.address, tr.data); // write the mirror value after each transaction
                `uvm_info("ADAPTER", $sformatf("bus2reg: UVM_WRITE value=0x%0h, Addr=0x%0h", tr.data, tr.address, ), UVM_LOW);
            end
        else
            begin
                rw.data = tr.data;
                `uvm_info("ADAPTER", $sformatf("bus2reg: UVM_READ value=0x%0h, Addr=0x%0h", tr.data, tr.address), UVM_LOW);
            end
    endfunction
endclass