import mypkg::*;

class mycov;



	covergroup cg;
	

	

		A_add_sub_cp 		: coverpoint trans.A 						//ALU_2, //ALU_3, //ALU_11, //ALU_12, //ALU_16, //ALU_17
									{	bins maxpos = {MAXPOS};
										bins maxneg = {MAXNEG};
										bins zero = {ZERO};
										bins A_default = default; 
										illegal_bins maxneg_ignore = {-16};
										}


		B_add_sub_cp 		: coverpoint trans.B    					//ALU_2, //ALU_3, //ALU_11, //ALU_12, //ALU_16, //ALU_17
								{	bins maxpos = {MAXPOS};
									bins maxneg = {MAXNEG};
									bins zero = {ZERO};
									bins B_default = default; 
									illegal_bins maxneg_ignore = {-16};
								}

		
		A_logic_cp 			: coverpoint trans.A  						//ALU_4, //ALU_5, //ALU_6, //ALU_8, //ALU_10, //ALU_14, //ALU_15

									{
										bins walkingones_b[] = {1, 2, 4, 8};
									}
		
		
		B_logic_cp			: coverpoint trans.B	 					//ALU_4, //ALU_5, //ALU_6, //ALU_8, //ALU_10, //ALU_14, //ALU_15									
										{
											bins walkingones_b[] = {1, 2, 4, 8};
										}

		a_en_cp 	: coverpoint trans.a_en;
		b_en_cp 	: coverpoint trans.b_en;

		a_op_cp		: coverpoint trans.a_op iff (trans.a_en && !trans.b_en)
										{
											bins add = {ADD_A};
											bins sub = {SUB_A};
											bins logic_process[] = {XOR_A, AND_A_1, AND_A_2, OR_A, XNOR_A};
											illegal_bins a_op_invalid = {INVALID_A};
										}
		b_op_1_cp		: coverpoint trans.b_op iff (!trans.a_en && trans.b_en)
										{
											bins logic_process = {NAND_B_1};
											bins add[] = {ADD1_B_1, ADD2_B_1};
											illegal_bins b_op_invalid = {INVALID_B_1};
										}

		b_op_2_cp		: coverpoint trans.b_op iff (trans.a_en && trans.b_en)
										{
											bins logic_process[] = {XOR_B_2, XNOR_B_2};
											bins add_sub[] = {SUBONE_B_2, ADDTWO_B_2};
										}

	 	C_cp 			: coverpoint $signed(trans.C)
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

		cross_A_B_op_add_sub_b_op_2	: cross A_add_sub_cp, B_add_sub_cp, b_op_2_cp 					//ALU_2, //ALU_3, //ALU_11, //ALU_12, //ALU_16, //ALU_17
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

	endgroup : cg


	mailbox mon2collector;
	mytrans trans;


	function new(mailbox mon2collector);
		this.mon2collector = mon2collector;

		cg = new();
	endfunction

	task main();
		forever begin
			mon2collector.get(trans);
			trans.display("COVERAGE");

			cg.sample();

		end
		
	endtask : main
	
endclass : mycov
