module top ();


	bit clk;

	always #1 clk = ~clk;

	counter_if counterif (clk);
	counter DUT (counterif.DUT);
	counter_tb tb (counterif.TEST);
	monitor mon(counterif.MONITOR);

	bind counter counter_sva countersva(counterif.DUT);


endmodule : top
