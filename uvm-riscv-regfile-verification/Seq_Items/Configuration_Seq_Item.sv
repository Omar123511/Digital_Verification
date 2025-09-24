//-----------------------------------------------------------------------------
// Class: Configuration_Seq_Item
// Description: Transaction object for Configuration interface. Contains:
//              - All configurable signals with randomization support
//              - Address alignment and range constraints
//              - Standard UVM methods for copy, compare and print
//-----------------------------------------------------------------------------
class Configuration_Seq_Item extends uvm_sequence_item;
    `uvm_object_utils(Configuration_Seq_Item)

    // Control signals
    rand bit        rst_n;
    rand bit        scan_cg_en_i;
    rand bit        fetch_enable_i;
    rand bit        pulp_clock_en_i;
    
    // Address signals
    rand bit [31:0] boot_addr_i;
    rand bit [31:0] mtvec_addr_i;
    rand bit [31:0] dm_halt_addr_i;
    rand bit [31:0] dm_exception_addr_i;
    rand bit [31:0] hart_id_i;
    
    // Status signal
    bit             core_sleep_o;
    //-------------------------------------------------------
    // Constraints: Address Alignment
    // Ensures proper alignment of all address signals
    //-------------------------------------------------------
    constraint addr_alignment {
        boot_addr_i[0] == 0;               // Half-word aligned
        mtvec_addr_i[1:0] == 0;            // Word aligned
        dm_halt_addr_i[1:0] == 0;          // Word aligned  
        dm_exception_addr_i[1:0] == 0;     // Word aligned
    }
    //-------------------------------------------------------
    // Constraints: Address Ranges
    // Defines valid ranges for configurable addresses
    //-------------------------------------------------------
    constraint addr_ranges {
        boot_addr_i inside {[32'h0000_1000:32'hFFFF_F000]};
        mtvec_addr_i inside {[32'h0000_2000:32'hFFFF_E000]};
    }

    //-----------------------------------------------------------------------------
    // Function: new
    // Description: Constructor
    //-----------------------------------------------------------------------------
    function new(string name = "Configuration_Seq_Item");
        super.new(name);
    endfunction
    //-----------------------------------------------------------------------------
    // Function: do_copy
    // Parameters:
    //  rhs - Object to copy from
    // Description: Deep copy of all transaction fields
    //-----------------------------------------------------------------------------
    function void do_copy(uvm_object rhs);
        Configuration_Seq_Item rhs_;
        if (!$cast(rhs_, rhs)) begin
            `uvm_fatal("DO_COPY", "Cast failed")
        end
        rst_n              = rhs_.rst_n;
        scan_cg_en_i        = rhs_.scan_cg_en_i;
        fetch_enable_i      = rhs_.fetch_enable_i;
        pulp_clock_en_i     = rhs_.pulp_clock_en_i;
        boot_addr_i         = rhs_.boot_addr_i;
        mtvec_addr_i        = rhs_.mtvec_addr_i;
        dm_halt_addr_i      = rhs_.dm_halt_addr_i;
        dm_exception_addr_i = rhs_.dm_exception_addr_i;
        hart_id_i          = rhs_.hart_id_i;
        core_sleep_o       = rhs_.core_sleep_o;
    endfunction
    //-----------------------------------------------------------------------------
    // Function: convert2string
    // Returns: Formatted string representation of transaction
    // Description: Creates human-readable string of all transaction fields
    //-----------------------------------------------------------------------------
    function string convert2string();
        string s;
        s = $sformatf("rst_n: %0b | scan_cg_en_i: %0b | fetch_enable_i: %0b | pulp_clock_en_i: %0b\n", 
                      rst_n, scan_cg_en_i, fetch_enable_i, pulp_clock_en_i);
        s = {s, $sformatf("boot_addr_i: 0x%8h | mtvec_addr_i: 0x%8h\n", 
                          boot_addr_i, mtvec_addr_i)};
        s = {s, $sformatf("dm_halt_addr_i: 0x%8h | dm_exception_addr_i: 0x%8h | hart_id_i: 0x%8h\n",
                          dm_halt_addr_i, dm_exception_addr_i, hart_id_i)};
        s = {s, $sformatf("core_sleep_o: %0b", core_sleep_o)};
        return s;
    endfunction

    //-----------------------------------------------------------------------------
    // Function: do_compare
    // Parameters:
    //  rhs       - Object to compare against
    //  comparer  - UVM comparer policy
    // Returns:   1 if equal, 0 if different
    // Description: Compares all transaction fields
    //-----------------------------------------------------------------------------
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        Configuration_Seq_Item rhs_;
        if (!$cast(rhs_, rhs)) begin
            `uvm_error("DO_COMPARE", "Cast failed")
            return 0;
        end
        return (super.do_compare(rhs, comparer) &&
                rst_n              == rhs_.rst_n &&
                scan_cg_en_i        == rhs_.scan_cg_en_i &&
                fetch_enable_i      == rhs_.fetch_enable_i &&
                pulp_clock_en_i     == rhs_.pulp_clock_en_i &&
                boot_addr_i         == rhs_.boot_addr_i &&
                mtvec_addr_i        == rhs_.mtvec_addr_i &&
                dm_halt_addr_i      == rhs_.dm_halt_addr_i &&
                dm_exception_addr_i == rhs_.dm_exception_addr_i &&
                hart_id_i          == rhs_.hart_id_i &&
                core_sleep_o       == rhs_.core_sleep_o);
    endfunction
endclass