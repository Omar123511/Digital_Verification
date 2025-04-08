class ALU_sequence_item extends uvm_sequence_item;


	logic ALU_en;

	rand logic a_en, b_en; //operations enable
	
	rand logic [A_OP_WIDTH-1:0] a_op;
	rand logic [B_OP_WIDTH-1:0] b_op;

	rand logic signed [DATA_WIDTH-1:0] A, B;

	logic [OUTPUT_WIDTH-1:0] C;


	/////////////////////////////////////////////////////////////////////////////

	`uvm_object_utils(ALU_sequence_item)
	
	function new (string name = "ALU_sequence_item");
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
	
		!(A_rem_val inside {MAXPOS, ZERO, MAXNEG});
		!(B_rem_val inside {MAXPOS, ZERO, MAXNEG});

	}



	constraint c_unique {
			A != IGNORE;
			B != IGNORE;
		
			a_op != INVALID_A;
	
	}

	

	constraint c_en 		  	 	{ 																					

		(a_en == 0 && b_en == 0) dist {0 := 90, 1 := 10}; 															//ALU_18
		
	}


	constraint c_op {

		if(!a_en && b_en){

			b_op inside {0, 1, 2};									//ALU_9

			}
		else if(a_en && b_en){
	
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
		
	}



 	virtual function void do_print(uvm_printer printer);
	    super.do_print(printer);
        printer.print_field("a_en", a_en, $bits(a_en), UVM_BIN);
        printer.print_field("b_en", b_en, $bits(b_en), UVM_BIN);
	   if(a_en && !b_en) begin
	   		enum_a_op = e_a_op'(a_op);
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
	  	endfunction
	
endclass : ALU_sequence_item
