//-----------------------------------------------------------------------------
// Class: Configuration_cfg
// Engineer: Nourhan
// Description: Configuration object for configuration agent. Contains:
//              - Virtual interface handle
//              - Agent configuration parameters
//              - Address constraints and defaults
//              - Address validation and generation methods
//-----------------------------------------------------------------------------
class Configuration_cfg extends uvm_object;
    `uvm_object_utils(Configuration_cfg)

    // Virtual interface
    virtual Configuration_IF configuration_vif;

    // Agent configuration
    uvm_active_passive_enum configuration_is_active;
    bit cfg_has_coverage = 1;
    bit cfg_checks_enabled = 1;
    
    // Address constraints
    bit [31:0] cfg_min_boot_addr = 32'h0000_1000;
    bit [31:0] cfg_max_boot_addr = 32'hFFFF_F000;
    bit [31:0] cfg_min_mtvec_addr = 32'h0000_2000;
    bit [31:0] cfg_max_mtvec_addr = 32'hFFFF_E000;
    
    // Default addresses
    bit [31:0] cfg_default_boot_addr = 32'h0000_0000;
    bit [31:0] cfg_default_mtvec_addr = 32'h0000_2000;
    bit [31:0] cfg_default_dm_halt_addr = 32'h0000_3000;
    bit [31:0] cfg_default_dm_exception_addr = 32'h0000_4000;

    function new(string name = "Configuration_cfg");
        super.new(name);
    endfunction

        // Function: is_boot_addr_valid
    // Returns true if address is half-word aligned (LSB = 0)
    function bit is_boot_addr_valid(bit [31:0] addr);
        return (addr[0] == 0); // Half-word aligned
    endfunction
    // Function: is_mtvec_addr_valid
    // Returns true if address is word aligned (2 LSBs = 0)
    function bit is_mtvec_addr_valid(bit [31:0] addr);
        return (addr[1:0] == 0); // Word aligned
    endfunction
    // Function: is_dm_addr_valid
    // Returns true if address is word aligned (2 LSBs = 0)
    function bit is_dm_addr_valid(bit [31:0] addr);
        return (addr[1:0] == 0); // Word aligned
    endfunction

     //-------------------------------------------------------
    // Random Address Generation Methods
    //-------------------------------------------------------

    // Function: get_random_boot_addr
    // Returns random boot address within constraints:
    // - Within min/max range
    // - Half-word aligned (LSB = 0)
    // - Falls back to default if randomization fails
    function bit [31:0] get_random_boot_addr();
        bit [31:0] addr;
        if (!std::randomize(addr) with {
            addr >= cfg_min_boot_addr;
            addr <= cfg_max_boot_addr;
            addr[0] == 0;
        }) begin
            `uvm_warning("RAND", "Using default boot address")
            return cfg_default_boot_addr;
        end
        return addr;
    endfunction
    // Function: get_random_mtvec_addr
    // Returns random mtvec address within constraints:
    // - Within min/max range
    // - Word aligned (2 LSBs = 0)
    // - Falls back to default if randomization fails
    function bit [31:0] get_random_mtvec_addr();
        bit [31:0] addr;
        if (!std::randomize(addr) with {
            addr >= cfg_min_mtvec_addr;
            addr <= cfg_max_mtvec_addr;
            addr[1:0] == 0;
        }) begin
            `uvm_warning("RAND", "Using default mtvec address")
            return cfg_default_mtvec_addr;
        end
        return addr;
    endfunction
endclass