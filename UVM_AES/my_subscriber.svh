class my_subscriber extends uvm_subscriber #(my_sequence_item);
	
	`uvm_component_utils(my_subscriber)
	my_sequence_item seq_item_inst0;

	covergroup cg;
		cp_in 		:	coverpoint seq_item_inst0.in;

		cp_key 		: 	coverpoint seq_item_inst0.key;

		cp_out		: 	coverpoint seq_item_inst0.out; 	

	endgroup : cg


	function new(string name = "my_subscriber", uvm_component parent = null);
		super.new(name, parent);
		cg = new();
	endfunction

	function void write(my_sequence_item t);
		seq_item_inst0 = t;
		cg.sample();
	endfunction

endclass : my_subscriber