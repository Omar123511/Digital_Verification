class my_sequence_a_op extends uvm_sequence #(my_sequence_item);

	`uvm_object_utils(my_sequence_a_op)

	my_cfg cfg;

	function new(string name = "my_sequence_a_op");
		super.new(name);
	endfunction


	virtual task body ();
		if (!uvm_config_db#(my_cfg)::get(null, "", "my_cfg", cfg)) begin
	      `uvm_fatal("CFG_ERR", "Failed to retrieve configuration object!")
		end
		cfg.seq_a_op_on = 1;
		cfg.seq_b_op_1_on = 0;
		cfg.seq_b_op_2_on = 0;
		cfg.seq_all_on = 0;
	  

		repeat (cfg.item_count_a_op) begin
			req = my_sequence_item::type_id::create("req");
			req.a_en.rand_mode(0);
			req.b_en.rand_mode(0);

			start_item(req);
			req.a_en = 1;
			req.b_en = 0;
			assert(req.randomize());
			

    		finish_item(req);
		end
	    `uvm_info(get_full_name(), $sformatf("Done generation of %0d items", cfg.item_count_a_op), UVM_LOW)

	endtask
	
endclass : my_sequence_a_op

class my_sequence_b_op_1 extends uvm_sequence #(my_sequence_item);

	`uvm_object_utils(my_sequence_b_op_1)

	my_cfg cfg;

	function new(string name = "my_sequence_b_op_1");
		super.new(name);
	endfunction


	virtual task body ();
		if (!uvm_config_db#(my_cfg)::get(null, "", "my_cfg", cfg)) begin
	      `uvm_fatal("CFG_ERR", "Failed to retrieve configuration object!")
		end
		cfg.seq_a_op_on = 0;
		cfg.seq_b_op_1_on = 1;
		cfg.seq_b_op_2_on = 0;
		cfg.seq_all_on = 0;
		

		repeat (cfg.item_count_b_op_1) begin
			req = my_sequence_item::type_id::create("req");
			req.a_en.rand_mode(0);
			req.b_en.rand_mode(0);

			start_item(req);
			req.a_en = 0;
			req.b_en = 1;
			assert(req.randomize());
			

    			finish_item(req);
		
		end
	    `uvm_info(get_full_name(), $sformatf("Done generation of %0d items", cfg.item_count_b_op_1), UVM_LOW)

	endtask
	
endclass : my_sequence_b_op_1


class my_sequence_b_op_2 extends uvm_sequence #(my_sequence_item);

	`uvm_object_utils(my_sequence_b_op_2)

	my_cfg cfg;

	function new(string name = "my_sequence_b_op_2");
		super.new(name);
	endfunction


	virtual task body ();
		if (!uvm_config_db#(my_cfg)::get(null, "", "my_cfg", cfg)) begin
	      `uvm_fatal("CFG_ERR", "Failed to retrieve configuration object!")
		end
		cfg.seq_a_op_on = 0;
		cfg.seq_b_op_1_on = 0;
		cfg.seq_b_op_2_on = 1;
		cfg.seq_all_on = 0;
		repeat (cfg.item_count_b_op_2) begin
			req = my_sequence_item::type_id::create("req");
			req.a_en.rand_mode(0);
			req.b_en.rand_mode(0);

			start_item(req);
			req.a_en = 1;
			req.b_en = 1;
			assert(req.randomize());
			

    		finish_item(req);
		
		end
	    `uvm_info(get_full_name(), $sformatf("Done generation of %0d items", cfg.item_count_b_op_2), UVM_LOW)

	endtask
	
endclass : my_sequence_b_op_2


class my_sequence_all extends uvm_sequence #(my_sequence_item);

	`uvm_object_utils(my_sequence_all)

	my_cfg cfg;

	function new(string name = "my_sequence_all");
		super.new(name);
	endfunction


	virtual task body ();
		if (!uvm_config_db#(my_cfg)::get(null, "", "my_cfg", cfg)) begin
	      `uvm_fatal("CFG_ERR", "Failed to retrieve configuration object!")
		end
		cfg.seq_a_op_on = 0;
		cfg.seq_b_op_1_on = 0;
		cfg.seq_b_op_2_on = 0;
		cfg.seq_all_on = 1;
		repeat (cfg.item_count) begin 													//add config_object in repeat
			// req = my_sequence_item::type_id::create("req"); 				//req is defined in uvm_sequence base class
			// start_item(req);
			// assert(req.randomize());
    		// finish_item(req);			
			
			req = my_sequence_item::type_id::create("req");
			start_item(req);
	    	`uvm_info(get_full_name(), $sformatf("start_item: "), UVM_LOW)

			assert(req.randomize());
	    	`uvm_info(get_full_name(), $sformatf("Generate new item: "), UVM_LOW)

    		finish_item(req);
		end
	    `uvm_info(get_full_name(), $sformatf("Done generation of %0d items", cfg.item_count), UVM_LOW)

	endtask
	
endclass : my_sequence_all


class my_sequence extends uvm_sequence #(my_sequence_item);

	`uvm_object_utils(my_sequence)

	my_sequence_a_op seq_a_op;
	my_sequence_b_op_1 seq_b_op_1;
	my_sequence_b_op_2 seq_b_op_2;
	my_sequence_all seq_all;

	my_cfg cfg;
	

	function new(string name = "my_sequence");
		super.new(name);
	endfunction


	virtual task body ();
		if (!uvm_config_db#(my_cfg)::get(null, "", "my_cfg", cfg))
	      `uvm_fatal("CFG_ERR", "Failed to retrieve configuration object!")
		
		`uvm_do(seq_a_op)
    		`uvm_do(seq_b_op_1)
    	 	`uvm_do(seq_b_op_2)
    		`uvm_do(seq_all)

	    `uvm_info(get_full_name(), $sformatf("Done generation of %0d items", cfg.item_count_sum), UVM_LOW)
	    // `uvm_info(get_full_name(), $sformatf("Done generation of %0d items", cfg.count_sum), UVM_LOW)

	endtask
	
endclass : my_sequence
