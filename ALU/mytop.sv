//`timescale 1ns / 1ps
module mytop ();

	bit clk;
	intf if1(clk);

	initial begin
		forever begin
			#5 clk = ~clk; 
		end
	end

	initial begin
		if1.rst_n = 1'b0;
		#10
		if1.rst_n = 1'b1;
		#10
		if1.rst_n = 1'b0;
		#10
		if1.rst_n = 1'b1;
	end



	mytest test_inst0(if1);

	ALU ALU_inst0
	(
		.clk(if1.clk), 
		.rst_n(if1.rst_n),
		
		.ALU_en(if1.ALU_en),
		
		.a_en(if1.a_en), 
		.b_en(if1.b_en),
		
		.a_op(if1.a_op),
		.b_op(if1.b_op),

		.A(if1.A), 
		.B(if1.B),

		.C(if1.C)
	);

	bind ALU ALU_SVA ALU_SVA_inst0(if1);

endmodule : mytop
