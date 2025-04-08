class ALU_sequencer extends uvm_sequencer #(ALU_sequence_item);
	
	`uvm_component_utils(ALU_sequencer)

	ALU_sequence_item seq_item;

	function new(string name = "ALU_sequencer", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	
endclass : ALU_sequencer