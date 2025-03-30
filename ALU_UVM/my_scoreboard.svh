class my_scoreboard extends uvm_scoreboard;

	bit [OUTPUT_WIDTH-1:0] C_expected;

	uvm_analysis_imp #(my_sequence_item, my_scoreboard) m_analysis_imp;
	
	my_sequence_item seq_item_q [$];

	my_cfg cfg;


	`uvm_component_utils(my_scoreboard)

	function new(string name = "my_scoreboard", uvm_component parent);
		super.new(name, parent);
	endfunction


	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		m_analysis_imp = new("m_analysis_imp", this);
		if (!uvm_config_db#(my_cfg)::get(null, "", "my_cfg", cfg)) begin
	      `uvm_fatal("CFG_ERR", "Failed to retrieve configuration object!")
		end
	endfunction



	virtual function void write(my_sequence_item req);
		seq_item_q.push_back(req);
		count_packets();
	endfunction

	virtual task run_phase(uvm_phase phase);
		super.run_phase(phase);

		forever begin

			my_sequence_item req_clone;
		
			wait(seq_item_q.size() > 0);
			req_clone = seq_item_q.pop_front();

			if (req_clone.a_en && !req_clone.b_en) begin
				case (req_clone.a_op)
					'd0 : C_expected = {req_clone.A[4], req_clone.A} + {req_clone.B[4], req_clone.B}; 				//ALU_2
					'd1 : C_expected = {req_clone.A[4], req_clone.A} - {req_clone.B[4], req_clone.B};				//ALU_3
					'd2 : C_expected = req_clone.A ^ req_clone.B; 											//ALU_4
					'd3 : C_expected = req_clone.A & req_clone.B; 											//ALU_5
					'd4 : C_expected = req_clone.A & req_clone.B; 											//ALU_6
					'd5 : C_expected = req_clone.A | req_clone.B; 											//ALU_7
					'd6 : C_expected = ~(req_clone.A ^ req_clone.B); 										//ALU_8
					default : C_expected = 0;
				endcase
			end

			else if (!req_clone.a_en && req_clone.b_en) begin
				case (req_clone.b_op)
					'd0 : C_expected = ~(req_clone.A & req_clone.B); 										//ALU_10
					'd1 : C_expected = {req_clone.A[4], req_clone.A} + {req_clone.B[4], req_clone.B}; 				//ALU_11
					'd2 : C_expected = {req_clone.A[4], req_clone.A} + {req_clone.B[4], req_clone.B}; 				//ALU_12
					default : C_expected = 0;
				endcase
			end

			else if (req_clone.a_en && req_clone.b_en) begin
				case (req_clone.b_op)
					'd0 : C_expected = req_clone.A ^ req_clone.B; 											//ALU_14
					'd1 : C_expected = ~(req_clone.A ^ req_clone.B); 										//ALU_15
					'd2 : C_expected = {req_clone.A[4], req_clone.A} - 6'd1; 								//ALU_16
					'd3 : C_expected = {req_clone.B[4], req_clone.B} + 6'd2; 								//ALU_17
				endcase
			end
			else begin
				C_expected = C_expected; 															//ALU_18
			end
		
			if (req_clone.C != C_expected) begin
				`uvm_info(get_type_name(),$sformatf("------ :: FAIL::DATA MISMATCHED! :: ------"),UVM_LOW)
				`uvm_info(get_type_name(),$sformatf("Expected Data: %0d Actual Data: %0d",$signed(C_expected), $signed(req_clone.C)),UVM_LOW)
				req_clone.print();
    		`uvm_info(get_type_name(),"------------------------------------",UVM_LOW)
				cfg.error_count++;
			end

			else begin
				`uvm_info(get_type_name(),$sformatf("------ :: SUCCESS::DATA MATCHED! :: ------"),UVM_LOW)
				`uvm_info(get_type_name(),$sformatf("Expected Data: %0d Actual Data: %0d",$signed(C_expected), $signed(req_clone.C)),UVM_LOW)
				req_clone.print();
    		`uvm_info(get_type_name(),"------------------------------------",UVM_LOW)
				cfg.correct_count++;
			end	
		end
	endtask : run_phase




	virtual function void count_packets();
		if (cfg.seq_a_op_on) begin
			cfg.count_a_op++;
		end
		
		if (cfg.seq_b_op_1_on) begin
			cfg.count_b_op_1++;
		end
	
		if (cfg.seq_b_op_2_on) begin
			cfg.count_b_op_2++;
		end

		if (cfg.seq_all_on) begin
			cfg.count++;
		end

		
	endfunction : count_packets

endclass : my_scoreboard
