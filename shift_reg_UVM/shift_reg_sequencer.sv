package shift_reg_sequencer_pkg;

	import uvm_pkg::*;
	`include "uvm_macros.svh"

	import shift_reg_seq_item_pkg::*;
	

	class shift_reg_sequencer extends uvm_sequencer #(shift_reg_seq_item);
		`uvm_component_utils(shift_reg_sequencer);

		function new(string name = "shift_reg_sequencer", uvm_component parent = null);
			super.new(name, parent);
		endfunction
	endclass : shift_reg_sequencer
	
endpackage : shift_reg_sequencer_pkg

