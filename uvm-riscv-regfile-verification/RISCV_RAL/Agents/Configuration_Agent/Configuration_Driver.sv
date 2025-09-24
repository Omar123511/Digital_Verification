//-----------------------------------------------------------------------------
// Class: Configuration_Driver
// Engineer: Nourhan
// Description: UVM driver for Configuration interface. Responsible for:
//              - Receiving sequence items from the sequencer
//              - Driving signal-level transactions to the DUT via virtual interface
//              - Handling clock synchronization and signal timing
//-----------------------------------------------------------------------------
class Configuration_Driver extends uvm_driver #(Configuration_Seq_Item);
    `uvm_component_utils(Configuration_Driver)
    
    virtual Configuration_IF d_if;
    Configuration_Seq_Item stim_seq_item;
    Configuration_cfg cfg;

    //-----------------------------------------------------------------------------
    // Function: new
    // Description: Constructor
    //-----------------------------------------------------------------------------
    function new(string name = "Configuration_Driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //-----------------------------------------------------------------------------
    // Task: run_phase (main_phase)
    // Description: Main driver operation loop:
    //  1. Gets sequence items from sequencer
    //  2. Drives them to the DUT via drive_transfer task
    //  3. Reports completion back to sequencer
    //  4. Logs transaction details
    //-----------------------------------------------------------------------------
    task main_phase(uvm_phase phase);

        
        forever begin
            // Get next sequence item
            seq_item_port.get_next_item(stim_seq_item);
            
            // Drive the transaction
            drive_transfer(stim_seq_item);
            
            // Indicate completion
            seq_item_port.item_done();
            
            `uvm_info("Configuration_Driver", $sformatf("Drove transaction: %s", 
                      stim_seq_item.convert2string()), UVM_HIGH)
        end
    endtask

       //-----------------------------------------------------------------------------
    // Task: drive_transfer
    // Parameters:
    //  item - Sequence item containing transaction data
    // Description:
    //  - Drives signal-level values to the DUT interface
    //  - Synchronizes with clock edge
    //  - Maps sequence item fields to interface signals
    //-----------------------------------------------------------------------------
    task drive_transfer(Configuration_Seq_Item item);
       
        @(posedge d_if.clk);
        // Drive all interface signals from sequence item
        d_if.rst_n              <= item.rst_n;
        d_if.scan_cg_en_i        <= item.scan_cg_en_i;
        d_if.fetch_enable_i      <= item.fetch_enable_i;
        d_if.pulp_clock_en_i     <= item.pulp_clock_en_i;
        d_if.boot_addr_i         <= item.boot_addr_i;
        d_if.mtvec_addr_i        <= item.mtvec_addr_i;
        d_if.dm_halt_addr_i      <= item.dm_halt_addr_i;
        d_if.dm_exception_addr_i <= item.dm_exception_addr_i;
        d_if.hart_id_i           <= item.hart_id_i;
	
    endtask
endclass
