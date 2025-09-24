/*######################################################################
## Class Name : Debug_Monitor  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Monitors the Debug Interface (debug_vif) signals
######################################################################*/


class Debug_Monitor extends uvm_monitor;

		// Register Debug Monitor with the UVM factory
		`uvm_component_utils(Debug_Monitor)

		// Virtual interface for interacting with the Debug interface
		virtual Debug_Interface Debug_vif;

		// Sequence item for storing signals observed on the interface
		Debug_Seq_Item seq_item;

		// Analysis port for sending collected sequence items
		uvm_analysis_port #(Debug_Seq_Item) mon_ap;

		function new(string name = "Debug_Monitor", uvm_component parent = null);
			super.new(name,parent);
		endfunction

		// Build phase: Initialize the analysis port
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			mon_ap = new("mon_ap", this);
		endfunction

		// Run phase: Capture and analyze signals from the Debug interface
		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				seq_item = Debug_Seq_Item::type_id::create("seq_item");
				@(posedge Debug_vif.clk);
				// Capture signals from the Debug interface
				seq_item.debug_req_i = Debug_vif.debug_req_i;
				seq_item.debug_havereset_o = Debug_vif.debug_havereset_o;
				seq_item.debug_running_o = Debug_vif.debug_running_o;
				seq_item.debug_halted_o = Debug_vif.debug_halted_o;

				// Send the sequence item to the analysis port
				mon_ap.write(seq_item);
				`uvm_info("Debug_Monitor", seq_item.convert2string(), UVM_FULL)
		end
	endtask
endclass
