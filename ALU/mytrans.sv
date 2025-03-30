import mypkg::*;


class mytrans;

	/////////////////////////////////////////////////////////////////////////////
	

	
	rand logic a_en, b_en; //operations enable
	
	rand logic [A_OP_WIDTH-1:0] a_op;
	rand logic [B_OP_WIDTH-1:0] b_op;

	rand logic signed [DATA_WIDTH-1:0] A, B;

	logic [OUTPUT_WIDTH-1:0] C;

	/////////////////////////////////////////////////////////////////////////////

	rand e_perm A_ext, B_ext;
	rand logic [DATA_WIDTH-1:0] A_rem_val, B_rem_val;

	e_a_op l_a_op_arr[7] = {ADD_A, SUB_A, XOR_A, AND_A_1, AND_A_2, OR_A, XNOR_A};
	e_b_op_1 l_b_op_1_arr[3] = {NAND_B_1, ADD1_B_1, ADD2_B_1};
	e_b_op_2 l_b_op_2_arr[4] = {XOR_B_2, XNOR_B_2, SUBONE_B_2, ADDTWO_B_2};


	logic [DATA_WIDTH-1] walking_ones [] = {1,2,4,8};

	rand logic [DATA_WIDTH-1] walking_ones_true_A, walking_ones_false_A, walking_ones_true_B, walking_ones_false_B;

	/////////////////////////////////////////////////////////////////////////////


	constraint c_walking_ones {
		walking_ones_true_A inside {walking_ones};
		walking_ones_true_B inside {walking_ones};
		!(walking_ones_false_A inside {walking_ones, IGNORE});
		!(walking_ones_false_B inside {walking_ones, IGNORE});
		
	}


	constraint c_rem_values {
		A_rem_val != MAXPOS || ZERO || MAXNEG || IGNORE;
		B_rem_val != MAXPOS || ZERO || MAXNEG || IGNORE;

	}

	constraint c_unique
			{
			unique{A};
			unique{B};
			unique{a_op};
			unique{b_op};
			A != IGNORE;
			B != IGNORE; 
			}

	constraint c_en 		  	 	{ 																					

		(a_en == 0 && b_en == 0) dist {0 := 80, 1 := 20}; 															//ALU_18
		
	}

	constraint c_a_op {
		if(a_en && !b_en){
			if(a_op == ADD_A || a_op == SUB_A){ 																			//ALU_2, ALU_3 
				A dist {A_ext := 80, A_rem_val := 20}; 	
				B dist {B_ext := 80, B_rem_val := 20};
			}

			else if(a_op == XOR_A || a_op == AND_A_1 || a_op == AND_A_2 || a_op == OR_A || a_op == XNOR_A){ 								//ALU_4, ALU_5, ALU_6, ALU_7, ALU_8   
				A dist {walking_ones_true_A := 90, walking_ones_false_A := 10};
				B dist {walking_ones_true_B := 90, walking_ones_false_B := 10};
				 
			}	
				
		a_op dist {[l_a_op_arr[0]:l_a_op_arr[6]] := 90, INVALID_A := 0}; 											//ALU_9
		}


	}


	constraint c_b_op_1 {

		if(!a_en && b_en){
			if(b_op == NAND_B_1){ 																							//ALU_10						
				A dist {walking_ones_true_A := 90, walking_ones_false_A := 10};
				B dist {walking_ones_true_B := 90, walking_ones_false_B := 10};
				
				}
			else if(b_op == ADD1_B_1 || b_op == ADD2_B_1){ 																		//ALU_11, ALU_12
				A dist {A_ext := 80, A_rem_val := 20}; 	
				B dist {B_ext := 80, B_rem_val := 20};
				}

		b_op dist {[l_b_op_1_arr[0]:l_b_op_1_arr[2]] := 80, INVALID_B_1 := 0}; 									//ALU_9
		}


		
	}

	constraint c_b_op_2 {

			if(a_en && b_en){
				if(b_op == XOR_B_2 || b_op == XNOR_B_2){ 																		//ALU_14, ALU_15						
					A dist {walking_ones_true_A := 90, walking_ones_false_A := 10};
					B dist {walking_ones_true_B := 90, walking_ones_false_B := 10};
					
					}
				else if(b_op == SUBONE_B_2 || b_op == ADDTWO_B_2){ 																	//ALU_16, ALU_17
					A dist {A_ext := 80, A_rem_val := 20}; 	
					B dist {B_ext := 80, B_rem_val := 20};
					}

				b_op inside {l_b_op_2_arr}; 									//ALU_9


			}
			
		}

	


		function void display(string component);
			$display("-[%0s]-", component);
			$display("%0t", $time);
			$display("-------------------------------------");
			$display("a_en = %b, b_en = %b", a_en, b_en);
			$display("a_op = %0d, b_op = %0d", a_op, b_op);
			$display("A = %0d, B = %0d", A, B);
			$display("C = %0d", $signed(C));
			$display("-------------------------------------");
		endfunction

		function void display_ips(string component);
			$display("-[%0s]-", component);
			$display("%0t", $time);
			$display("-------------------------------------");
			$display("a_en = %b, b_en = %b", a_en, b_en);
			$display("a_op = %0d, b_op = %0d", a_op, b_op);
			$display("A = %0d, B = %0d", A, B);
			$display("-------------------------------------");
		endfunction



	
endclass : mytrans
