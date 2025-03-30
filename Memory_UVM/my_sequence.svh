class my_sequence extends uvm_sequence #(my_sequence_item);

	`uvm_object_utils(my_sequence)
	my_sequence_item seq_item_inst0;

	parameter TESTS = 10000;

	function new (string name = "my_sequence");
		super.new(name);
		
	endfunction

	virtual task body;
		$display("my_sequence::body");
		repeat(TESTS) begin
			seq_item_inst0 = my_sequence_item::type_id::create("seq_item_inst0");
			start_item(seq_item_inst0);
			assert(seq_item_inst0.randomize()) else $display("%0t::my_sequence::seq_item_inst0 randomization failed", $time());	
			finish_item(seq_item_inst0);
		end
		
	endtask : body
	
	
endclass : my_sequence