//-----------------------------------------------------------------------------
// Interface: Configuration_IF
// Engineer: Nourhan
// Description: Physical interface for configuration signals. Contains:
//              - All input signals for device configuration
//              - Output signals reflecting device status
//              - Used to connect DUT with UVM testbench components
//-----------------------------------------------------------------------------
interface Configuration_IF();
  // Input signals
  logic        rst_n;
  bit clk;
  logic        scan_cg_en_i;
  logic        fetch_enable_i;
  logic        pulp_clock_en_i;
  logic [31:0] boot_addr_i;
  logic [31:0] mtvec_addr_i;
  logic [31:0] dm_halt_addr_i;
  logic [31:0] dm_exception_addr_i;
  logic [31:0] hart_id_i;
  
  // Output signals
  logic        core_sleep_o;
 
endinterface