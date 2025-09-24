//-----------------------------------------------------------------------------
// Engineer:Nourhan
//Sequence: Always enables fetch with full configuration
//-----------------------------------------------------------------------------
class Configuration_Sequence extends uvm_sequence #(Configuration_Seq_Item);
    `uvm_object_utils(Configuration_Sequence)
    
    // Configuration reference
    Configuration_cfg cfg;
    
    function new(string name = "Configuration_Sequence");
        super.new(name);
    endfunction
    
    task body();
        Configuration_Seq_Item item;
        // Create transaction
        item = Configuration_Seq_Item::type_id::create("item");
        start_item(item);
            // Always enable fetch
            item.fetch_enable_i = 0;
            item.boot_addr_i = 32'h0000_0000;
            item.mtvec_addr_i = 32'h0000_2000;
            item.dm_halt_addr_i =  32'h0000_3000;
            item.dm_exception_addr_i =  32'h0000_4000;
            item.rst_n = 0;
            item.pulp_clock_en_i = 0;
            item.scan_cg_en_i=0;
            item.boot_addr_i[0] = 0;
            item.mtvec_addr_i[1:0] = 0;
            item.dm_halt_addr_i[1:0] = 0;
            item.dm_exception_addr_i[1:0] = 0;
        
        `uvm_info("Configuration_Sequence", $sformatf("Sending configuration:\n%s", item.convert2string()), UVM_MEDIUM)
        finish_item(item);
	// Start and finish item
        start_item(item);
            // Always enable fetch
            item.fetch_enable_i = 1;
            item.boot_addr_i = 32'h0000_0000;
            item.mtvec_addr_i = 32'h0000_2000;
            item.dm_halt_addr_i =  32'h0000_3000;
            item.dm_exception_addr_i =  32'h0000_4000;
            item.rst_n = 1;
            item.pulp_clock_en_i = 0;
            item.scan_cg_en_i=0;
            item.boot_addr_i[0] = 0;
            item.mtvec_addr_i[1:0] = 0;
            item.dm_halt_addr_i[1:0] = 0;
            item.dm_exception_addr_i[1:0] = 0;
        
        `uvm_info("Configuration_Sequence", $sformatf("Sending configuration:\n%s", item.convert2string()), UVM_MEDIUM)
        finish_item(item);

       
    
    endtask
endclass
class Configuration_Sequence2 extends uvm_sequence #(Configuration_Seq_Item);
    `uvm_object_utils(Configuration_Sequence2)
    
    // Configuration reference
    Configuration_cfg cfg;
    
    function new(string name = "Configuration_Sequence2");
        super.new(name);
    endfunction
    
    task body();
        Configuration_Seq_Item item;
        // Create transaction
        item = Configuration_Seq_Item::type_id::create("item");
        start_item(item);
            // Always enable fetch
            item.fetch_enable_i = 0;
            item.boot_addr_i = 32'h0000_0000;
            item.mtvec_addr_i = 32'h0000_2000;
            item.dm_halt_addr_i =  32'h0000_3000;
            item.dm_exception_addr_i =  32'h0000_4000;
            item.rst_n = 0;
            item.pulp_clock_en_i = 0;
            item.scan_cg_en_i=0;
            item.boot_addr_i[0] = 0;
            item.mtvec_addr_i[1:0] = 0;
            item.dm_halt_addr_i[1:0] = 0;
            item.dm_exception_addr_i[1:0] = 0;
        
        `uvm_info("Configuration_Sequence2", $sformatf("Sending configuration:\n%s", item.convert2string()), UVM_MEDIUM)
        finish_item(item);
	// Start and finish item
        start_item(item);
            // Always enable fetch
            item.fetch_enable_i = 1;
            item.boot_addr_i = 32'h0000_0000;
            item.mtvec_addr_i = 32'h0000_2000;
            item.dm_halt_addr_i =  32'h0000_3000;
            item.dm_exception_addr_i =  32'h0000_4000;
            item.rst_n = 1;
            item.pulp_clock_en_i = 0;
            item.scan_cg_en_i=0;
            item.boot_addr_i[0] = 0;

            item.mtvec_addr_i[1:0] = 0;
            item.dm_halt_addr_i[1:0] = 0;
            item.dm_exception_addr_i[1:0] = 0;
        
        `uvm_info("Configuration_Sequence2", $sformatf("Sending configuration:\n%s", item.convert2string()), UVM_MEDIUM)
        finish_item(item);

       
    
    endtask
endclass
