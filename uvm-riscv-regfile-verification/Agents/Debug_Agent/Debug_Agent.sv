/*######################################################################
## Class Name : Debug_Agent  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## UVM agent for the Debug Interface of the CV32E40P RISC-V core.
## Encapsulates Debug Driver, Debug Sequencer, Debug Monitor
######################################################################*/

class Debug_Agent extends uvm_agent;

		// Register Debug Agent with the factory
		`uvm_component_utils(Debug_Agent)

		// Configuration object handle
		Debug_Config cfg;

		// UVM agent components
		Debug_Driver drv;
		Debug_Sequencer sqr;
		Debug_Monitor mon;

		// Analysis port to broadcast monitor transactions	
		uvm_analysis_port #(Debug_Seq_Item) agt_ap;

		function new (string name = "Debug_Agent", uvm_component parent = null);
			super.new(name,parent);
		endfunction

		// Build phase: create subcomponents and retrieve config
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);

			// Get the Debug_Config from the configuration database
			if(!uvm_config_db #(Debug_Config)::get(this,"","Debug_Config", cfg))
				`uvm_fatal("Debug_Agent", "Debug Agent - unable to get Debug configuration object")

			// Create monitor component
			mon = Debug_Monitor::type_id::create("mon", this);

			// Create analysis port to broadcast monitored transactions
			agt_ap=new("agt_ap",this);

			// If the agent is active, create driver and sequencer
			if (cfg.Debug_is_active == UVM_ACTIVE)
			begin
				drv = Debug_Driver::type_id::create("drv", this);
				sqr  = Debug_Sequencer::type_id::create("sqr", this);
			end
		endfunction

		function void connect_phase(uvm_phase phase);
			// Connect monitor analysis port to agent analysis port
			mon.mon_ap.connect(agt_ap);

			// Connect virtual interface to monitor
			mon.Debug_vif = cfg.Debug_vif;

			// If agent is active, connect driver and sequencer
			if (cfg.Debug_is_active == UVM_ACTIVE)
			begin
				// Connect virtual interface to driver
				drv.Debug_vif = cfg.Debug_vif;
				drv.seq_item_port.connect(sqr.seq_item_export);
			end
		endfunction
endclass
