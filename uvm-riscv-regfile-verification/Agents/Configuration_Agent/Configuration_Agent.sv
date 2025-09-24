//-----------------------------------------------------------------------------
// Class: Configuration_Agent
// Engineer: Nourhan
// Description: UVM agent for configuration interface. Manages driver, sequencer,
//              and monitor components based on active/passive configuration.
//-----------------------------------------------------------------------------
class Configuration_Agent extends uvm_agent;
    `uvm_component_utils(Configuration_Agent)
    
    uvm_analysis_port #(Configuration_Seq_Item) agt_ap;
    Configuration_cfg cfg;
    Configuration_Driver driv; 
    Configuration_Sequencer sqr; 
    Configuration_Monitor mon; 

    function new(string name = "Configuration_Agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    //-------------------------------------------------------
    // Build Phase
    // - Gets configuration from config_db
    // - Creates agent components based on active/passive mode
    //-------------------------------------------------------
    function void build_phase(uvm_phase phase);
          
        // Get configuration object from config_db
        if (!uvm_config_db#(Configuration_cfg)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG", "Failed to get configuration object")
        end
        
        // Create monitor (always created)
        mon = Configuration_Monitor::type_id::create("mon", this);
        agt_ap = new("agt_ap", this);
        mon.m_if=cfg.configuration_vif;
        
        // Only create driver and sequencer if active
        if (cfg.configuration_is_active == UVM_ACTIVE) begin
            driv = Configuration_Driver::type_id::create("driv", this);
            sqr = Configuration_Sequencer::type_id::create("sqr", this);
            driv.d_if=cfg.configuration_vif;
        end
    endfunction
        //-------------------------------------------------------
    // Connect Phase
    // - Connects monitor to agent analysis port
    // - Connects driver to sequencer if active
    //-------------------------------------------------------
    function void connect_phase(uvm_phase phase);

        
        // Connect monitor to agent analysis port
        mon.mon_ap.connect(agt_ap);
        
        // Connect driver to sequencer if active
        if (cfg.configuration_is_active == UVM_ACTIVE) begin
            
            driv.seq_item_port.connect(sqr.seq_item_export);
        end
    endfunction
endclass