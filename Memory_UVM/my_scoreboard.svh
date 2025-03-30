class my_scoreboard extends uvm_scoreboard;

	`uvm_component_utils(my_scoreboard)

	virtual intf vif;
	my_sequence_item seq_item_inst0;

	logic [31:0] o_data_out_expec;
	logic o_valid_expec;
	logic [31 : 0] l_arr [16];
	int error_count, correct_count;

	uvm_analysis_imp #(my_sequence_item, my_scoreboard) my_analysis_imp;

	function new(string name = "my_scoreboard", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		$display("my_scoreboard::build_phase");
		seq_item_inst0 = my_sequence_item::type_id::create("seq_item_inst0");
		my_analysis_imp = new("my_analysis_imp", this);
	endfunction

	virtual function void write(my_sequence_item seq_item_inst0);
		// error_count = 0; correct_count = 0;
		// golden_model(logic [31:0] o_data_out_expec, logic o_valid_expec);
		// check_result(logic [31:0] o_data_out_expec, logic o_valid_expec);
		// golden_model;
		// check_result;	
		if (!seq_item_inst0.i_rst_n) begin
			o_data_out_expec 	= 0;
			o_valid_expec 		= 0;
		end
		else begin
			if (seq_item_inst0.i_EN) begin
				l_arr[seq_item_inst0.i_address] = seq_item_inst0.i_data_in; 
				o_valid_expec = 1'b0;
			end
			else begin
				o_data_out_expec = l_arr[seq_item_inst0.i_address];
				o_valid_expec = 1'b1;
			end
		end

		$display("my_scoreboard::check_result");
		$display("%0t::SCB::i_rst_n = %h, i_EN = %h, i_address = %h, i_data_in = %h", $time(), seq_item_inst0.i_rst_n, seq_item_inst0.i_EN, seq_item_inst0.i_address, seq_item_inst0.i_data_in);
		if (!seq_item_inst0.i_EN) begin
			if ({o_valid_expec, o_data_out_expec} !== {seq_item_inst0.o_valid, seq_item_inst0.o_data_out}) begin
				$display("-------------------------------------------------------");
				$display("%0t::ERROR!", $time());
				$display("valid_expected = %h, valid = %h", o_valid_expec, seq_item_inst0.o_valid);
				$display("data_out_expected = %h, data_out = %h", o_data_out_expec, seq_item_inst0.o_data_out);
				$display("-------------------------------------------------------");
				error_count = error_count + 1;
			end	

			else begin
				$display("-------------------------------------------------------");
				$display("%0t::PASS!", $time());
				$display("valid_expected = %h, valid = %h", o_valid_expec, seq_item_inst0.o_valid);
				$display("data_out_expected = %h, data_out = %h", o_data_out_expec, seq_item_inst0.o_data_out);
				$display("-------------------------------------------------------");
				correct_count = correct_count + 1;
			end
		end
		$display("correct_count = %d, error_count = %d",correct_count, error_count);


	endfunction

	// virtual task run_phase(uvm_phase phase);
	// 	super.run_phase(phase);
	// 	if (!seq_item_inst0.i_rst_n) begin
	// 		seq_item_inst0.o_data_out 	= 0;
	// 		seq_item_inst0.o_valid 		= 0;
	// 	end
	// 	else begin
	// 		if (seq_item_inst0.i_EN) begin
	// 			l_arr[seq_item_inst0.i_address] = seq_item_inst0.i_data_in; 
	// 			o_valid_expec = 1'b0;
	// 		end
	// 		else begin
	// 			o_data_out_expec = l_arr[seq_item_inst0.i_address];
	// 			o_valid_expec = 1'b1;
	// 			if ({o_valid_expec, o_data_out_expec} !== {seq_item_inst0.o_valid, seq_item_inst0.o_data_out}) begin
	// 				$display("-------------------------------------------------------");
	// 				$display("%0t::ERROR!", $time());
	// 				$display("valid_expected = %h, valid = %h", o_valid_expec, seq_item_inst0.o_valid);
	// 				$display("data_out_expected = %h, data_out = %h", o_data_out_expec, seq_item_inst0.o_data_out);
	// 				$display("-------------------------------------------------------");
	// 				error_count = error_count + 1;
	// 			end	

	// 			else begin
	// 				$display("-------------------------------------------------------");
	// 				$display("%0t::PASS!", $time());
	// 				$display("valid_expected = %h, valid = %h", o_valid_expec, seq_item_inst0.o_valid);
	// 				$display("data_out_expected = %h, data_out = %h", o_data_out_expec, seq_item_inst0.o_data_out);
	// 				$display("-------------------------------------------------------");
	// 				correct_count = correct_count + 1;
	// 			end
	// 		end
	// 	end

	// 	$display("correct_count = %d, error_count = %d",correct_count, error_count);


		
	// endtask : run_phase





	// task golden_model(logic [31:0] o_data_out_expec, logic o_valid_expec);
	// task golden_model;
	// 	if (!seq_item_inst0.i_rst_n) begin
	// 		seq_item_inst0.o_data_out 	= 0;
	// 		seq_item_inst0.o_valid 		= 0;
	// 	end
	// 	else begin
	// 		if (seq_item_inst0.i_EN) begin
	// 			l_arr[seq_item_inst0.i_address] = seq_item_inst0.i_data_in; 
	// 			o_valid_expec = 1'b0;
	// 		end
	// 		else begin
	// 			o_data_out_expec = l_arr[seq_item_inst0.i_address];
	// 			o_valid_expec = 1'b1;
	// 		end
	// 	end
	// endtask

	// task check_result;
	// 	$display("my_scoreboard::check_result");
	// 	if ({o_valid_expec, o_data_out_expec} !== {seq_item_inst0.o_valid, seq_item_inst0.o_data_out}) begin
	// 		$display("-------------------------------------------------------");
	// 		$display("ERROR!");
	// 		$display("valid_expected = %d, valid = %d", o_valid_expec, seq_item_inst0.o_valid);
	// 		$display("data_out_expected = %d, data_out = %d", o_data_out_expec, seq_item_inst0.o_data_out);
	// 		$display("-------------------------------------------------------");
	// 		error_count = error_count + 1;
	// 	end	

	// 	else begin
	// 		$display("-------------------------------------------------------");
	// 		$display("PASS!");
	// 		$display("valid_expected = %d, valid = %d", o_valid_expec, seq_item_inst0.o_valid);
	// 		$display("data_out_expected = %d, data_out = %d", o_data_out_expec, seq_item_inst0.o_data_out);
	// 		$display("-------------------------------------------------------");
	// 		correct_count = correct_count + 1;
	// 	end		
	// endtask : check_result
	
endclass : my_scoreboard