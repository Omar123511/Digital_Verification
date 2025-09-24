/*######################################################################
## Class Name: Instruction_Agent  
## Engineer : Omnia Mohamed
## Date: April 2025
## Description:
    .It gets its config object from config_db and based on it, decide whether to be active or passive agent.
    .It will be an active agent which contains sequencer, driver and monitor.
    .It broadcasts the collected transaction to scoreboard and instruction_subscriber.
######################################################################*/
class Instruction_Agent extends uvm_agent;
    `uvm_component_utils(Instruction_Agent)
    
    Instruction_Agent_Config cfg;
    Instruction_Driver drv;
    Instruction_Monitor mon;
    Instruction_Sequencer sqr;

    uvm_analysis_port#(Instruction_Seq_Item) agent_ap;
    

    function new(string name="Instruction_Agent",uvm_component parent=null);
        super.new(name,parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        if(!uvm_config_db#(Instruction_Agent_Config)::get(this,"","Instruction_Agent_Config",cfg))
            `uvm_fatal("Instruction_Agent","Can't get Instruction_Agent_Config from the config db ")

        if(cfg.agent_is_active==UVM_ACTIVE)begin
            drv=Instruction_Driver::type_id::create("drv",this);
            sqr=Instruction_Sequencer::type_id::create("sqr",this);
            drv.vif=cfg.vif;
        end
        mon=Instruction_Monitor::type_id::create("mon",this);
        mon.vif=cfg.vif;
        agent_ap=new("agent_ap",this);
    endfunction
    virtual function void connect_phase(uvm_phase phase);
        if(cfg.agent_is_active==UVM_ACTIVE)begin
            drv.seq_item_port.connect(sqr.seq_item_export);
            
        end
        mon.mon_ap.connect(this.agent_ap);
    endfunction

endclass