package p_headers;

	parameter DATA_WIDTH = 5, OUTPUT_WIDTH = 6, A_OP_WIDTH = 3, B_OP_WIDTH = 2, MAXPOSOP = 30, MAXNEGOP = -30, IGNORE = -16, IGNORE_OP = -32;


	// typedef enum {MAXPOS = (((2**DATA_WIDTH)/2)-1), ZERO = 0, MAXNEG = -(((2**DATA_WIDTH)/2)-1)} e_perm;
	typedef enum {MAXPOS = (((2**DATA_WIDTH)/2)-1), ZERO = 0, MAXNEG = -(((2**DATA_WIDTH)/2)-1)} e_perm;

	typedef enum {ADD_A, SUB_A, XOR_A, AND_A_1, AND_A_2, OR_A, XNOR_A, INVALID_A} e_a_op;

	typedef enum {NAND_B_1, ADD1_B_1, ADD2_B_1, INVALID_B_1} e_b_op_1;

	typedef enum {XOR_B_2, XNOR_B_2, SUBONE_B_2, ADDTWO_B_2} e_b_op_2;


	
endpackage : p_headers
