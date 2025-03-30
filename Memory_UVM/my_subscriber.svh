class my_subscriber extends uvm_subscriber #(my_sequence_item);
	
	`uvm_component_utils(my_subscriber)
	my_sequence_item seq_item_inst0;

	covergroup cg;
		cp_EN 		:	coverpoint seq_item_inst0.i_EN iff (seq_item_inst0.i_rst_n){
			bins zero_one_zero = (0 => 1 => 0);
		} 
		cp_address 	: 	coverpoint seq_item_inst0.i_address 	iff (seq_item_inst0.i_rst_n);
		cp_data_in 	:	coverpoint seq_item_inst0.i_data_in 	iff (seq_item_inst0.i_rst_n && seq_item_inst0.i_EN);

		cp_data_out : 	coverpoint seq_item_inst0.o_data_out 	iff (seq_item_inst0.i_rst_n);
		cp_valid	: 	coverpoint seq_item_inst0.o_valid		iff	(seq_item_inst0.i_rst_n); 	

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