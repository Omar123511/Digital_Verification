import p_headers::*;

interface alu_if (clk, rst_n);

  	input bit clk;    // Clock
    input bit rst_n;  // Asynchronous reset active low
    
    logic ALU_en;   //System enable
    
    logic a_en, b_en; //operations enable
    
    logic [A_OP_WIDTH-1:0] a_op;
    logic [B_OP_WIDTH-1:0] b_op;

    logic signed [DATA_WIDTH-1:0] A, B;

    logic [OUTPUT_WIDTH-1:0] C;
    
	
endinterface
