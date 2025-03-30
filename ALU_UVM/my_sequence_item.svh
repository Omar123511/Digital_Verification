class my_sequence_item extends uvm_sequence_item;


	logic ALU_en;

	rand logic a_en, b_en; //operations enable
	
	rand logic [A_OP_WIDTH-1:0] a_op;
	rand logic [B_OP_WIDTH-1:0] b_op;

	rand logic signed [DATA_WIDTH-1:0] A, B;

	logic [OUTPUT_WIDTH-1:0] C;


	/////////////////////////////////////////////////////////////////////////////

	// `uvm_object_utils_begin(my_sequence_item)
	// 	`uvm_field_int(ALU_en, UVM_DEFAULT)
	// 	`uvm_field_int(a_en, UVM_DEFAULT)
	// 	`uvm_field_int(b_en, UVM_DEFAULT)
	// 	`uvm_field_int(a_op, UVM_DEFAULT)
	// 	`uvm_field_int(b_op, UVM_DEFAULT)
	// 	`uvm_field_int(A, UVM_DEFAULT)
	// 	`uvm_field_int(B, UVM_DEFAULT)
	// 	`uvm_field_int(C, UVM_DEFAULT)
	// `uvm_object_utils_end

	  `uvm_object_utils(my_sequence_item)
	


	function new (string name = "my_sequence_item");
		super.new(name);
	endfunction


	/////////////////////////////////////////////////////////////////////////////

	rand e_perm A_ext, B_ext;
	rand logic [DATA_WIDTH-1:0] A_rem_val, B_rem_val;

	e_a_op l_a_op_arr[7] = {ADD_A, SUB_A, XOR_A, AND_A_1, AND_A_2, OR_A, XNOR_A};
	e_b_op_1 l_b_op_1_arr[3] = {NAND_B_1, ADD1_B_1, ADD2_B_1};
	e_b_op_2 l_b_op_2_arr[4] = {XOR_B_2, XNOR_B_2, SUBONE_B_2, ADDTWO_B_2};

	e_a_op enum_a_op;
	e_b_op_1 enum_b_op_1;
	e_b_op_2 enum_b_op_2;

	logic [DATA_WIDTH-1] walking_ones [] = {1,2,4,8};

	rand logic [DATA_WIDTH-1] walking_ones_true_A, walking_ones_false_A, walking_ones_true_B, walking_ones_false_B;

	/////////////////////////////////////////////////////////////////////////////


	constraint c_walking_ones {
		walking_ones_true_A inside {walking_ones};
		walking_ones_true_B inside {walking_ones};
		!(walking_ones_false_A inside {walking_ones});
		!(walking_ones_false_B inside {walking_ones});
		
	}


	constraint c_rem_values {
		// A_rem_val != MAXPOS || ZERO || MAXNEG;
		// B_rem_val != MAXPOS || ZERO || MAXNEG;
		//A_ext inside {MAXPOS, ZERO, MAXNEG};
		//B_ext inside {MAXPOS, ZERO, MAXNEG};
		!(A_rem_val inside {MAXPOS, ZERO, MAXNEG});
		!(B_rem_val inside {MAXPOS, ZERO, MAXNEG});

	}

	// constraint c_unique
	// 		{
	// 		// unique{A};
	// 		// unique{B};
	// 		// unique{a_op};
	// 		// unique{b_op};
	// 		// A dist {[MAXNEG : -1] := 50, [0:MAXPOS := 50]};
	// 		// B dist {[MAXNEG : -1] := 50, [0:MAXPOS := 50]};
	// 		A != IGNORE;
	// 		B != IGNORE;
	// 		// a_op != INVALID_A;
	// 		// b_op != INVALID_B_1; 
	// 		}

	constraint c_unique {
			A != IGNORE;
			B != IGNORE;
	 		// unique{A};
			// unique{B};
			// unique{a_op};
			// unique{b_op};

			// unique{b_op};
			// A dist {[MAXNEG : -1] := 50, [0:MAXPOS] := 0};
			// B dist {[MAXNEG : -1] := 50, [0:MAXPOS] := 0};
		
			a_op != INVALID_A;
			//(b_op == INVALID_B_1) dist {1 := 0};
			// b_op != INVALID_B_1;


	}

	// constraint assign_op{
		// enum_a_op == a_op;
		// (!a_en && b_en) -> (enum_b_op_1 == b_op);
		// (a_en && b_en) -> (enum_b_op_2 == b_op);

		// a_op == enum_a_op;
		// (!a_en && b_en) -> (b_op == enum_b_op_1);
		// (a_en && b_en) -> (b_op == enum_b_op_2); 

	// }

	constraint c_en 		  	 	{ 																					

		(a_en == 0 && b_en == 0) dist {0 := 90, 1 := 10}; 															//ALU_18
		
	}


	constraint c_op {
		// if(a_en && !b_en){
		// 	//a_op dist { ADD_A :/ 40, SUB_A :/ 40, [XOR_A:XNOR_A] :/ 20 };
		// 	a_op inside {l_a_op_arr};
		// 	// a_op inside {ADD_A, SUB_A, XOR_A, AND_A_1, AND_A_2, OR_A, XNOR_A};
		// 	}
		if(!a_en && b_en){
		//	b_op inside {[l_b_op_1_arr[0]:l_b_op_1_arr[2]]};
			b_op inside {0, 1, 2};									//ALU_9

			}
		else if(a_en && b_en){
			//b_op dist {l_b_op_2_arr[0] := 10, l_b_op_2_arr[1] := 10, l_b_op_2_arr[2] := 40, l_b_op_2_arr[3] := 40}; 									
			b_op inside {0, 1, 2, 3}; 			//ALU_9
			}
	}

	constraint c_A_B {
		if(a_en && !b_en){
			if(a_op == ADD_A || a_op == SUB_A){
				A dist {A_ext := 80, A_rem_val := 20};
			 	B dist {B_ext := 80, B_rem_val := 20};
			}
			else if(a_op == XOR_A || a_op == AND_A_1 || a_op == AND_A_2 || a_op == OR_A || a_op == XNOR_A){
				A dist {walking_ones_true_A := 80, walking_ones_false_A := 20};
				B dist {walking_ones_true_B := 80, walking_ones_false_B := 20};
			}	
		}

		if(!a_en && b_en){
			if(b_op == ADD1_B_1 || b_op == ADD2_B_1){
				A dist {A_ext := 80, A_rem_val := 20};
				B dist {B_ext := 80, B_rem_val := 20};
			}
			else if(b_op == NAND_B_1){
				A dist {walking_ones_true_A := 80, walking_ones_false_A := 20};
				B dist {walking_ones_true_B := 80, walking_ones_false_B := 20};
			}	
		}
		
		if(a_en && b_en){
			if(b_op == SUBONE_B_2 || b_op == ADDTWO_B_2){
				A dist {A_ext := 80, A_rem_val := 20};
				B dist {B_ext := 80, B_rem_val := 20};
			}
			else if(b_op == XOR_B_2 || b_op == XNOR_B_2){
				A dist {walking_ones_true_A := 80, walking_ones_false_A := 20};
				B dist {walking_ones_true_B := 80, walking_ones_false_B := 20};
			}	
		}
		
		// if(a_op == ADD_A || a_op == SUB_A || b_op == ADD1_B_1 || b_op == ADD2_B_1 || b_op == SUBONE_B_2 || b_op == ADDTWO_B_2){
		// 	 A dist {A_ext := 80, A_rem_val := 20};
		// 	 B dist {B_ext := 80, B_rem_val := 20};
	
		// 	}
		// else if(a_op == XOR_A || a_op == AND_A_1 || a_op == AND_A_2 || a_op == OR_A || a_op == XNOR_A || b_op == NAND_B_1 || b_op == XOR_B_2 || b_op == XNOR_B_2){
		// 	A dist {walking_ones_true_A := 80, walking_ones_false_A := 20};
		// 	B dist {walking_ones_true_B := 80, walking_ones_false_B := 20};
		// 	}
		
	}








	// constraint c_a_op {
	// 	if(a_en && !b_en){
	// 		if(a_op == ADD_A || a_op == SUB_A){ 																			//ALU_2, ALU_3 
	// 			// A dist {MAXPOS := 25, MAXNEG := 50, ZERO := 25,  A_rem_val := 30};
	// 			// B dist {MAXPOS := 25, MAXNEG := 50, ZERO := 25,  B_rem_val := 30}; 	
				
	// 			A dist {A_ext := 70, A_rem_val := 30};
	// 			B dist {B_ext := 70, B_rem_val := 30};
	// 		}

	// 		else if(a_op == XOR_A || a_op == AND_A_1 || a_op == AND_A_2 || a_op == OR_A || a_op == XNOR_A){ 								//ALU_4, ALU_5, ALU_6, ALU_7, ALU_8   
	// 			A dist {walking_ones_true_A := 60, walking_ones_true_A := 40};
	// 			B dist {walking_ones_true_B := 60, walking_ones_false_B := 40};
				 
	// 		}	
				
	// 	// a_op dist {[l_a_op_arr[0]:l_a_op_arr[6]] := 90, INVALID_A := 0}; 											//ALU_9
	// 	// a_op dist { ADD_A := 40, SUB_A := 40, [XOR_A:XNOR_A] := 20 };
	// 	}


	// }


	// constraint c_b_op_1 {

	// 	if(!a_en && b_en){
	// 		if(b_op == NAND_B_1){ 																							//ALU_10						
	// 			A dist {walking_ones_true_A := 60, walking_ones_false_A := 40};
	// 			B dist {walking_ones_true_B := 60, walking_ones_false_B := 40};
				
	// 			}
	// 		else if(b_op == ADD1_B_1 || b_op == ADD2_B_1){ 																		//ALU_11, ALU_12
	// 			// A dist {A_ext := 80, A_rem_val := 20}; 
	// 			A dist {MAXPOS := 25, MAXNEG := 50, ZERO := 25,  A_rem_val := 30};
	// 			B dist {MAXPOS := 25, MAXNEG := 50, ZERO := 25,  B_rem_val := 30}; 
				
	// 			// A dist {A_ext := 80, A_rem_val := 20}; 
	// 			// B dist {B_ext := 80, B_rem_val := 20};
	// 			}

	// 	// b_op dist {[l_b_op_1_arr[0]:l_b_op_1_arr[2]] := 80, INVALID_B_1 := 0}; 									//ALU_9
	// 	// b_op inside {[l_b_op_1_arr[0]:l_b_op_1_arr[2]]};									//ALU_9
	// 		b_op != INVALID_B_1;									//ALU_9

	// 	}
	// }

	// constraint c_b_op_2 {

	// 		if(a_en && b_en){
	// 			if(b_op == XOR_B_2 || b_op == XNOR_B_2){ 																		//ALU_14, ALU_15						
	// 				A dist {walking_ones_true_A := 60, walking_ones_false_A := 40};
	// 				B dist {walking_ones_true_B := 60, walking_ones_false_B := 40};
					
	// 				}
	// 			else if(b_op == SUBONE_B_2 || b_op == ADDTWO_B_2){ 																	//ALU_16, ALU_17
	// 				A dist {MAXPOS := 25, MAXNEG := 50, ZERO := 25,  A_rem_val := 30};
	// 				B dist {MAXPOS := 25, MAXNEG := 50, ZERO := 25,  B_rem_val := 30}; 
					
	// 				// A dist {A_ext := 80, A_rem_val := 20}; 	
	// 				// B dist {B_ext := 80, B_rem_val := 20};
	// 				}

	// 			// b_op inside {l_b_op_2_arr}; 									//ALU_9
	// 			// b_op dist {l_b_op_2_arr[0] := 10, l_b_op_2_arr[1] := 10, l_b_op_2_arr[2] := 40, l_b_op_2_arr[3] := 40}; 									//ALU_9


	// 		}
			
	// 	}


 	virtual function void do_print(uvm_printer printer);
	    super.do_print(printer);
        printer.print_field("a_en", a_en, $bits(a_en), UVM_BIN);
        printer.print_field("b_en", b_en, $bits(b_en), UVM_BIN);

	   if(a_en && !b_en) begin
	   		enum_a_op = e_a_op'(a_op);
	   		// enum_a_op = a_op;
			printer.print_string("a_op", enum_a_op.name());
			if(enum_a_op == ADD_A || enum_a_op == SUB_A) begin
				printer.print_field("A", A, $bits(A), UVM_DEC);
				printer.print_field("B", B, $bits(B), UVM_DEC);
				printer.print_field("C", $signed(C), $bits(C), UVM_DEC);
			end
			else if(enum_a_op == XOR_A || enum_a_op == AND_A_1 || enum_a_op == AND_A_2 || enum_a_op == OR_A || enum_a_op == XNOR_A) begin
				printer.print_field("A", A, $bits(A), UVM_BIN);
				printer.print_field("B", B, $bits(B), UVM_BIN);
				printer.print_field("C", C, $bits(C), UVM_BIN);
			end
		end
				
		else if(!a_en && b_en) begin
			enum_b_op_1 = e_b_op_1'(b_op);
			// enum_b_op_1 = b_op;
			printer.print_string("b_op", enum_b_op_1.name());	
			if(enum_b_op_1 == ADD1_B_1 || enum_b_op_1 == ADD2_B_1) begin
				printer.print_field("A", A, $bits(A), UVM_DEC);
				printer.print_field("B", B, $bits(B), UVM_DEC);
				printer.print_field("C", $signed(C), $bits(C), UVM_DEC);
			end
			
			else if(enum_b_op_1 == NAND_B_1) begin
				printer.print_field("A", A, $bits(A), UVM_BIN);
				printer.print_field("B", B, $bits(B), UVM_BIN);
				printer.print_field("C", C, $bits(C), UVM_BIN);
			end
		end

		else if (a_en && b_en) begin
			enum_b_op_2 = e_b_op_2'(b_op);
			// enum_b_op_2 = b_op;
			printer.print_string("b_op", enum_b_op_2.name());	
			if(b_op == SUBONE_B_2 || b_op == ADDTWO_B_2) begin
				printer.print_field("A", A, $bits(A), UVM_DEC);
				printer.print_field("B", B, $bits(B), UVM_DEC);
				printer.print_field("C", $signed(C), $bits(C), UVM_DEC);
			end
			else if(b_op == XOR_B_2 || b_op == XNOR_B_2) begin
				printer.print_field("A", A, $bits(A), UVM_BIN);
				printer.print_field("B", B, $bits(B), UVM_BIN);
				printer.print_field("C", C, $bits(C), UVM_BIN);
			end				
		end

		else begin	
			printer.print_field("A", A, $bits(A), UVM_HEX);
			printer.print_field("B", B, $bits(B), UVM_HEX);
			printer.print_field("C", C, $bits(C), UVM_HEX);			
		end

		// if(a_op == ADD_A || a_op == SUB_A || b_op == ADD1_B_1 || b_op == ADD2_B_1 || b_op == SUBONE_B_2 || b_op == ADDTWO_B_2) begin
		// 	printer.print_string("")
		// end

		// else if(a_op == XOR_A || a_op == AND_A_1 || a_op == AND_A_2 || a_op == OR_A || a_op == XNOR_A || b_op == NAND_B_1 || b_op == XOR_B_2 || b_op == XNOR_B_2) begin
			
		// end	
		

	
	  	endfunction
	
	// function void post_randomize();
	//    if(a_en && !b_en) begin
	//    		// enum_a_op = e_a_op'(a_op);
	//    		enum_a_op = a_op;
	// 		// printer.print_string("a_op", enum_a_op.name());
	//     	`uvm_info("SEQ_ITEM", $sformatf("a_en=%b, b_en=%b", a_en, b_en), UVM_MEDIUM)
	//     	`uvm_info("SEQ_ITEM", $sformatf("a_op = %0s", enum_a_op.name()), UVM_MEDIUM)

	// 		if(enum_a_op == ADD_A || enum_a_op == SUB_A) begin
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("A=%0d", A), UVM_MEDIUM)
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("B=%0d", B), UVM_MEDIUM)
	// 	    	// `uvm_info("SEQ_ITEM", $sformatf("C=%0d", C), UVM_MEDIUM)
	// 		end
	// 		else if(enum_a_op == XOR_A || enum_a_op == AND_A_1 || enum_a_op == AND_A_2 || enum_a_op == OR_A || enum_a_op == XNOR_A) begin
	// 			`uvm_info("SEQ_ITEM", $sformatf("a_en=%b, b_en=%b", a_en, b_en), UVM_MEDIUM)
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("A=%b", A), UVM_MEDIUM)
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("B=%b", B), UVM_MEDIUM)
	// 	    	// `uvm_info("SEQ_ITEM", $sformatf("C=%b", C), UVM_MEDIUM)		
	// 	    end
	// 	end	
	// 	else if(!a_en && b_en) begin
	// 		// enum_b_op_1 = e_b_op_1'(b_op);
	// 		enum_b_op_1 = b_op;
	// 		// printer.print_string("b_op", enum_b_op_1.name());	
	//     	`uvm_info("SEQ_ITEM", $sformatf("a_op = %0s", enum_a_op.name()), UVM_MEDIUM)

	// 			`uvm_info("SEQ_ITEM", $sformatf("a_en=%b, b_en=%b", a_en, b_en), UVM_MEDIUM)
	// 		if(enum_b_op_1 == ADD1_B_1 || enum_b_op_1 == ADD2_B_1) begin
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("A=%0d", A), UVM_MEDIUM)
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("B=%0d", B), UVM_MEDIUM)
	// 	    	// `uvm_info("SEQ_ITEM", $sformatf("C=%0d", C), UVM_MEDIUM)
	// 		end
			
	// 		else if(enum_b_op_1 == NAND_B_1) begin
	// 			`uvm_info("SEQ_ITEM", $sformatf("a_en=%b, b_en=%b", a_en, b_en), UVM_MEDIUM)
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("A=%b", A), UVM_MEDIUM)
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("B=%b", B), UVM_MEDIUM)
	// 		end
	// 	end

	// 	else if (a_en && b_en) begin
	// 		// enum_b_op_2 = e_b_op_2'(b_op);
	// 		enum_b_op_2 = b_op;
	// 		// printer.print_string("b_op", enum_b_op_2.name());
	//     	`uvm_info("SEQ_ITEM", $sformatf("a_op = %0s", enum_a_op.name()), UVM_MEDIUM)
	
	// 			`uvm_info("SEQ_ITEM", $sformatf("a_en=%b, b_en=%b", a_en, b_en), UVM_MEDIUM)
	// 		if(b_op == SUBONE_B_2 || b_op == ADDTWO_B_2) begin
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("A=%0d", A), UVM_MEDIUM)
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("B=%0d", B), UVM_MEDIUM)
	// 		end
	// 		else if(b_op == XOR_B_2 || b_op == XNOR_B_2) begin
	// 			// printer.print_field("A", A, $bits(A), UVM_BIN);
	// 			`uvm_info("SEQ_ITEM", $sformatf("A=%b", A), UVM_MEDIUM)
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("B=%b", B), UVM_MEDIUM)
	// 		end				
	// 	end

	// 	else begin	
	// 			`uvm_info("SEQ_ITEM", $sformatf("A=%0h", A), UVM_MEDIUM)
	// 	    	`uvm_info("SEQ_ITEM", $sformatf("B=%0h", B), UVM_MEDIUM)		
	// 	end
    // // `uvm_info("SEQ_ITEM", $sformatf("a_en=%b, b_en=%b, A=%0d, B=%0d", a_en, b_en, A, B), UVM_MEDIUM)
	// endfunction



endclass : my_sequence_item
