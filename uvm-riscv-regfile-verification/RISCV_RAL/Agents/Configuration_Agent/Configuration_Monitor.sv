//-----------------------------------------------------------------------------
// Class: Configuration_Monitor
// Engineer: Nourhan
// Description: UVM Monitor for Configuration interface. Responsible for:
//              - Observing DUT signals through virtual interface
//              - Capturing signal states into transaction items
//              - Broadcasting transactions via analysis port for scoreboard/coverage
//-----------------------------------------------------------------------------
class Configuration_Monitor extends uvm_monitor;
  `uvm_component_utils(Configuration_Monitor)
  
  virtual Configuration_IF m_if;
  Configuration_cfg cfg;
  uvm_analysis_port #(Configuration_Seq_Item) mon_ap;
  Configuration_Seq_Item item;
 
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
   
      mon_ap = new("mon_ap", this);
      item = Configuration_Seq_Item::type_id::create("item");
  endfunction
    //-----------------------------------------------------------------------------
    // Task: main_phase
    // Description: Main monitoring operation loop:
    //  1. Waits for clock edge and small delay for signal stability
    //  2. Captures input and output signals from interface
    //  3. Logs captured transaction
    //  4. Broadcasts transaction via analysis port
    //-----------------------------------------------------------------------------  
  task main_phase(uvm_phase phase);
    
    forever begin
       @(posedge m_if.clk);
       #1step;
      // Capture inputs
      item.rst_n               = m_if.rst_n;
      item.scan_cg_en_i        = m_if.scan_cg_en_i;
      item.fetch_enable_i      = m_if.fetch_enable_i;
      item.pulp_clock_en_i     = m_if.pulp_clock_en_i;
      item.boot_addr_i         = m_if.boot_addr_i;
      item.mtvec_addr_i        = m_if.mtvec_addr_i;
      item.dm_halt_addr_i      = m_if.dm_halt_addr_i;
      item.dm_exception_addr_i = m_if.dm_exception_addr_i;
      item.hart_id_i           = m_if.hart_id_i;
      
      
      // Capture output
      item.core_sleep_o = m_if.core_sleep_o;

      `uvm_info("Configuration_Monitor", $sformatf("Sampled Packet is %s", item.convert2string), UVM_FULL)
      // Send captured transaction
      mon_ap.write(item);
    end
  endtask
endclass