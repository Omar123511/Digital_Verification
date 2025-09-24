/*######################################################################
## Class Name: Data_Memory_Sequencer  
## Engineer : Noureldeen Yehia
## Date: May 2025
######################################################################*/

class Data_Memory_Sequencer extends uvm_sequencer#(Data_Memory_Seq_Item);
/*
    Sequencer Class is parameterized with Transaction to pass it to seq_item_export #(REQ)
    and so we don't have to declare and construct it because it's already created implicitly.
*/

    // Factory Component Registration
    `uvm_component_utils(Data_Memory_Sequencer)

    // TLM Analysis Export to receive requests from Monitor
    uvm_analysis_export#(Data_Memory_Seq_Item) request_export;

    // TLM Analysis FIFO to queue request transactions
    uvm_tlm_analysis_fifo#(Data_Memory_Seq_Item) request_fifo;

    // Transaction Instance
    Data_Memory_Seq_Item s_item;

    // Storage Handle
    Data_Memory_Storage storage;

    // Constructor
    function new(string name = "Data_Memory_Sequencer", uvm_component parent);
        super.new(name, parent);

        // Create Export and FIFO
        request_export = new("request_export", this);
        request_fifo   = new("request_fifo", this); 
    endfunction

    // Build Phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "Build Phase of Sequencer", UVM_MEDIUM)

        // Get Storage Handle from config_db
        void'(uvm_config_db#(Data_Memory_Storage)::get(this, "", "Data_Memory_Storage", storage));
    endfunction

    // Connect Phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // Connect Export to FIFO
        request_export.connect(request_fifo.analysis_export);
        `uvm_info(get_type_name(), "Connect Phase of Sequencer", UVM_MEDIUM)
    endfunction

endclass