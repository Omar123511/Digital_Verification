/*######################################################################
## Class Name: Data_Memory_Agent 
## Engineer : Noureldeen Yehia
## Date: May 2025
######################################################################*/

class Data_Memory_Agent extends uvm_agent;

    // Factory Component Registration
    `uvm_component_utils(Data_Memory_Agent)

    // Declare TLM Analysis Ports for Agent
    uvm_analysis_port#(Data_Memory_Seq_Item) agt_dut_ap; // Full Transaction to be sent to SB & SC

    // Constructor
    function new(string name = "Data_Memory_Agent", uvm_component parent);
        super.new(name, parent);

        // Create TLM Analysis Ports
        agt_dut_ap = new("agt_dut_ap", this);
    endfunction

    // Virtual Interface Instance
    virtual Data_Memory_IF vif;

    // Instances of Components inside Agent
    Data_Memory_Sequencer     sqr;
    Data_Memory_Driver        driver;
    Data_Memory_Monitor       monitor;
    Data_Memory_Storage       storage;
    Data_Memory_Config        cfg;

    // Build Phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "Build Phase of Agent", UVM_MEDIUM)

        if (!uvm_config_db#(Data_Memory_Config)::get(this, "", "Agt_Data_Memory_IF", cfg))
            `uvm_fatal("build_phase", "Driver - Unable to get configuration object");

        // Create Factory Components
        monitor = Data_Memory_Monitor::type_id::create("monitor", this);
        storage = Data_Memory_Storage::type_id::create("storage", this);
        

        uvm_config_db#(Data_Memory_Storage)::set(this, "*", "Data_Memory_Storage", storage);

        monitor.vif = cfg.Data_Memory_vif;

        if (cfg.Data_Memory_is_active == UVM_ACTIVE) begin
            sqr           = Data_Memory_Sequencer::type_id::create("sqr", this);
            driver        = Data_Memory_Driver::type_id::create("driver", this);
            driver.vif    = cfg.Data_Memory_vif;
        end
    endfunction

    // Connect Phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info(get_type_name(), "Connect Phase of Agent", UVM_MEDIUM)

        // Connect Monitor Analysis Ports
        monitor.mon_ap.connect(agt_dut_ap);

        // Connect Monitor Request Port to Sequencer Export
        monitor.req_ap.connect(sqr.request_export);

        // Connect Driver and Sequencer if active
        if (cfg.Data_Memory_is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sqr.seq_item_export);
        end
    endfunction

endclass