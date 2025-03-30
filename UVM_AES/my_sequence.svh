class my_sequence extends uvm_sequence #(my_sequence_item);

	`uvm_object_utils(my_sequence)
	my_sequence_item seq_item_inst0;

	parameter TESTS = 2000;

	int file_handle;
    int result;



	function new (string name = "my_sequence");
		super.new(name);
		
	endfunction

	virtual task body;
		$display("my_sequence::body");

		repeat(TESTS) begin
			seq_item_inst0 = my_sequence_item::type_id::create("seq_item_inst0");
			start_item(seq_item_inst0);

			assert(seq_item_inst0.randomize()) else $display("%0t::my_sequence::seq_item_inst0 randomization failed", $time());	
			// file_handle = $fopen("input.txt","w");
			// $fwrite(file_handle,"%h",seq_item_inst0.in);
			// $fwrite(file_handle,"\n%h",seq_item_inst0.key);
			// $fclose(file_handle);
		    // result = $system("python AES.py input.txt output.txt");
		    // if (result != 0) begin
    		// 	`uvm_fatal("PYTHON_ERROR", "Failed to run AES.py");
  			// end

			finish_item(seq_item_inst0);
		end
		
	endtask : body
	
	
endclass : my_sequence