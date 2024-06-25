module top ();

	bit clk;

	initial begin
		clk = 0;
		forever begin
			#1 clk = ~clk;
		end
	end

	counter_if counterif(clk);

	counter DUT (counterif);
	counter_tb tb(counterif);

	bind counter SVA SVA_inst0(counterif);

endmodule : top