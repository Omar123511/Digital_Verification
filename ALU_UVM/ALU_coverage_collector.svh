class ALU_coverage_collector extends uvm_subscriber #(ALU_sequence_item);


	`uvm_component_utils(ALU_coverage_collector)

	ALU_sequence_item seq_item;

	ALU_cfg cfg;


	covergroup ALU_cg;
	
	

		A_add_sub_cp 		: coverpoint seq_item.A 						//ALU_2, //ALU_3, //ALU_11, //ALU_12, //ALU_16, //ALU_17
									{	bins maxpos = {MAXPOS};
										bins maxneg = {MAXNEG};
										bins zero = {ZERO};
										bins A_default = default; 
										illegal_bins maxneg_ignore = {-16};
										}


		B_add_sub_cp 		: coverpoint seq_item.B    					//ALU_2, //ALU_3, //ALU_11, //ALU_12, //ALU_16, //ALU_17
								{	bins maxpos = {MAXPOS};
									bins maxneg = {MAXNEG};
									bins zero = {ZERO};
									bins B_default = default; 
									illegal_bins maxneg_ignore = {-16};
								}

		
		A_logic_cp 			: coverpoint seq_item.A  						//ALU_4, //ALU_5, //ALU_6, //ALU_8, //ALU_10, //ALU_14, //ALU_15

									{
										bins walkingones_b[] = {1, 2, 4, 8};
									}
		
		
		B_logic_cp			: coverpoint seq_item.B	 					//ALU_4, //ALU_5, //ALU_6, //ALU_8, //ALU_10, //ALU_14, //ALU_15									
										{
											bins walkingones_b[] = {1, 2, 4, 8};
										}

		a_en_cp 	: coverpoint seq_item.a_en;
		b_en_cp 	: coverpoint seq_item.b_en;

		a_op_cp		: coverpoint seq_item.a_op iff (seq_item.a_en && !seq_item.b_en)
										{
											bins add = {ADD_A};
											bins sub = {SUB_A};
											bins logic_process[] = {XOR_A, AND_A_1, AND_A_2, OR_A, XNOR_A};
											illegal_bins a_op_invalid = {INVALID_A};
										}
		b_op_1_cp		: coverpoint seq_item.b_op iff (!seq_item.a_en && seq_item.b_en)
										{
											bins logic_process = {NAND_B_1};
											bins add[] = {ADD1_B_1, ADD2_B_1};
											illegal_bins b_op_invalid = {INVALID_B_1};
										}

		b_op_2_cp		: coverpoint seq_item.b_op iff (seq_item.a_en && seq_item.b_en)
										{
											bins logic_process[] = {XOR_B_2, XNOR_B_2};
											bins add_sub[] = {SUBONE_B_2, ADDTWO_B_2};
										}

	 	C_cp 			: coverpoint $signed(seq_item.C)
										{
											ignore_bins ignore = {-31, 31};
											illegal_bins illegal = {-32}; 
										}


		cross_A_B_op_add_sub_a_op	: cross A_add_sub_cp, B_add_sub_cp, a_op_cp 					//ALU_2, //ALU_3, //ALU_11, //ALU_12, //ALU_16, //ALU_17
									{	

										ignore_bins logical_bins = binsof(a_op_cp.logic_process);	

									}

		cross_A_B_op_add_sub_b_op_1	: cross A_add_sub_cp, B_add_sub_cp, b_op_1_cp 					//ALU_2, //ALU_3, //ALU_11, //ALU_12, //ALU_16, //ALU_17
									{

										ignore_bins logical_bins = binsof(b_op_1_cp.logic_process);

									}

		cross_A_B_op_add_sub_b_op_2	: cross A_add_sub_cp, B_add_sub_cp, b_op_2_cp					//ALU_2, //ALU_3, //ALU_11, //ALU_12, //ALU_16, //ALU_17
									{
																	
										ignore_bins logical_bins = binsof(b_op_2_cp.logic_process);

									}

	
		cross_A_B_op_logic_a_op 		: cross A_logic_cp, B_logic_cp, a_op_cp 					//ALU_4, //ALU_5, //ALU_6, //ALU_8, //ALU_10, //ALU_14, //ALU_15
									{
									
										ignore_bins add_bins = binsof(a_op_cp.add);
										ignore_bins sub_bins = binsof(a_op_cp.sub);

										
									}

		cross_A_B_op_logic_b_op_1 		: cross A_logic_cp, B_logic_cp, b_op_1_cp 					//ALU_4, //ALU_5, //ALU_6, //ALU_8, //ALU_10, //ALU_14, //ALU_15
									{
									
										ignore_bins add_sub_bins = binsof(b_op_1_cp.add);


									}

		cross_A_B_op_logic_b_op_2 		: cross A_logic_cp, B_logic_cp, b_op_2_cp 					//ALU_4, //ALU_5, //ALU_6, //ALU_8, //ALU_10, //ALU_14, //ALU_15
									{
								
									
										ignore_bins add_sub_bins = binsof(b_op_2_cp.add_sub);

									}

		cross_a_b_en 			: cross a_en_cp, b_en_cp;

	endgroup : ALU_cg





	function new(string name = "ALU_coverage_collector", uvm_component parent = null);
		super.new(name, parent);
		ALU_cg = new();
	endfunction



	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (~uvm_config_db#(ALU_cfg)::get(null, "", "ALU_cfg", cfg)) begin
			`uvm_fatal(get_full_name(), "ERROR FETCHING ALU_cfg")
		end
		seq_item = ALU_sequence_item::type_id::create("seq_item");
	endfunction




	function void write(ALU_sequence_item t);
		seq_item = t;
		cfg.cov_items++;
		ALU_cg.sample();
	endfunction
	
	virtual function void extract_phase(uvm_phase phase);
    	super.extract_phase(phase);
    
    	`uvm_info(get_type_name(), $sformatf("Coverage Report: %0f", ALU_cg.get_coverage()), UVM_LOW)
  endfunction

endclass : ALU_coverage_collector

