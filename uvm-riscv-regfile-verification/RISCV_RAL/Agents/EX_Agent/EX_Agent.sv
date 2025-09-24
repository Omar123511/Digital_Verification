
/*######################################################################
## Class Name : EX_Agent  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## UVM agent for the Execute (EX) stage of the CV32E40P RISC-V core.
## Encapsulates EX Driver, EX Sequencer (in active case), EX Monitor and EX Reference Model
## Send monitor seq items and golden reference values to corresponding subscribers
######################################################################*/

class EX_Agent extends uvm_agent;

		`uvm_component_utils(EX_Agent) // Register EX_Agent with the UVM factory

		// Components handles
		EX_Monitor mon;
		EX_Config cfg;
		EX_Driver drv;
		EX_Sequencer sqr;
		EX_Ref_Model rm;
		uvm_analysis_port #(EX_Seq_Item) agt_ap;
		uvm_analysis_port #(EX_Ref_Seq_Item) ref_agt_ap;

		function new (string name = "EX_Agent", uvm_component parent = null);
			super.new(name,parent);
		endfunction

		// Build phase: create and configure components
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			
			// Retrieve configuration object
			if(!uvm_config_db #(EX_Config)::get(this,"","EX_CFG", cfg))
				`uvm_fatal("build_phase", "EX Agent - unable to get EX configuration object")

			// Create components
			mon = EX_Monitor::type_id::create("mon", this);
			agt_ap = new("agt_ap", this);
			ref_agt_ap = new("ref_agt_ap", this);
			rm = EX_Ref_Model::type_id::create("rm", this);
			mon.EX_vif = cfg.EX_vif;
			// Create driver and sequencer in case of active agent
			if (cfg.EX_is_active == UVM_ACTIVE)
			begin
					drv.EX_vif = cfg.EX_vif;
					drv = EX_Driver::type_id::create("drv", this);
					sqr  = EX_Sequencer::type_id::create("sqr", this);
			end
		endfunction

		function void connect_phase(uvm_phase phase);
			// Monitor broadcasts transactions to agent analysis port and reference model
			mon.mon_ap.connect(agt_ap);
			mon.mon_ap.connect(rm.ex_model_export);
			
			rm.ref_ap.connect(ref_agt_ap);

			// Connect driver and sequencer in case of active agent
			if (cfg.EX_is_active == UVM_ACTIVE)
			begin			
				
				drv.seq_item_port.connect(sqr.seq_item_export);
			end
		endfunction

	endclass
