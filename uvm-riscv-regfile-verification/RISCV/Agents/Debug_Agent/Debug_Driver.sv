/*######################################################################
## Class Name : Debug_Driver  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Drives instruction execution transactions to the debug interface 
######################################################################*/


class Debug_Driver extends uvm_driver #(Debug_Seq_Item);
		// Register Debug Driver with the UVM factory
		`uvm_component_utils(Debug_Driver)

		// Virtual interface to interact with the Debug interface
		virtual Debug_Interface Debug_vif;

		// Sequence item that holds the stimulus data for the Debug interface
		Debug_Seq_Item stim_seq_item;

		function new(string name = "Debug_Driver", uvm_component parent = null);
			super.new(name,parent);
		endfunction

		// Build phase: Set up any required configurations or subcomponents
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
		endfunction

		// Connect phase: Connect any necessary ports or interfaces
		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
		endfunction

		// Run phase: Drives the stimulus based on received sequence items
		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				// Create a new sequence item to hold the stimulus
				stim_seq_item = Debug_Seq_Item::type_id::create("stim_seq_item");

				// Get the next sequence item from the sequencer
				seq_item_port.get_next_item(stim_seq_item);

				// Drive the stimulus to the virtual interface
				Debug_vif.debug_req_i = stim_seq_item.debug_req_i;

				// Mark the sequence item as done
				seq_item_port.item_done();
				`uvm_info("Debug_Driver", stim_seq_item.convert2string, UVM_HIGH)
			end
		endtask
endclass


