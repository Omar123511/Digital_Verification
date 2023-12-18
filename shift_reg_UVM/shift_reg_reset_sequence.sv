package shift_reg_reset_sequence_pkg;

	import uvm_pkg::*;
	`include "uvm_macros.svh"

	import shift_reg_seq_item_pkg::*;

	class shift_reg_reset_sequence extends uvm_sequence #(shift_reg_seq_item);

		`uvm_object_utils(shift_reg_reset_sequence);

		shift_reg_seq_item seq_item;

		function new(string name = "shift_reg_reset_sequence");
			super.new(name);
		endfunction

		task body;
			seq_item = shift_reg_seq_item::type_id::create("seq_item");

			start_item(seq_item);

			seq_item.reset = 1;
			seq_item.serial_in = 0;
			seq_item.direction = 0;
			seq_item.mode = 0;
			seq_item.datain = 0;

			finish_item(seq_item);

			
		endtask : body	
	endclass : shift_reg_reset_sequence
	
endpackage : shift_reg_reset_sequence_pkg
