/*######################################################################
## Class Name: Register_File_Agent  
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .The Agent fetches the configuration object to assign the interface to the internal components.
    .The agent type is passive.
    .It broadcasts the collected transaction to from monitor to coverage and scoreboard classes.
######################################################################*/

class Register_File_Agent extends uvm_agent;
	`uvm_component_utils(Register_File_Agent)

	Register_File_Monitor RF_mon;
	Register_File_Driver RF_drv;
	Register_File_Sequencer RF_sqr;
	Register_File_CFG RF_cfg;
	uvm_analysis_port #(Register_File_Sequence_Item) RF_agt_Actual_ap, RF_agt_Expected_ap;

	function new(string name = "Register_File_Agent", uvm_component parent = null);
		super.new(name, parent);
	endfunction


	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		if(!uvm_config_db #(Register_File_CFG)::get(this,"","RF_cfg", RF_cfg))
			`uvm_fatal("build_phase", "Register_File_Agent - unable to get RF_cfg")

		RF_mon   = Register_File_Monitor::type_id::create("RF_mon", this);
		
		RF_agt_Actual_ap = new("RF_agt_Actual_ap", this);
		RF_agt_Expected_ap = new("RF_agt_Expected_ap", this);
		
		RF_mon.RF_vif = RF_cfg.RF_vif;

	
		if (RF_cfg.RF_Is_Active == UVM_ACTIVE) begin
			RF_drv = Register_File_Driver::type_id::create("RF_drv", this);
			RF_sqr  = Register_File_Sequencer::type_id::create("RF_sqr", this);
			RF_drv.RF_vif = RF_cfg.RF_vif;
		end
	endfunction

		function void connect_phase(uvm_phase phase);
			RF_mon.REF_Monitor_ap.connect(RF_agt_Actual_ap);
 
			// Connect driver and sequencer in case of active agent
			if (RF_cfg.RF_Is_Active == UVM_ACTIVE)
			begin			
				RF_drv.RF_vif = RF_cfg.RF_vif;
				RF_drv.seq_item_port.connect(RF_sqr.seq_item_export);
			end
		endfunction
endclass : Register_File_Agent