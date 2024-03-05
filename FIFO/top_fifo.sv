module top ();

	bit clk;    // Clock
	
	initial begin
		clk = 0;
		forever begin
			#1 clk = ~clk;
		end
	end

	fifo_interface fifoif(clk);
	FIFO DUT(fifoif.DUT);
	FIFO_golden_model gm(fifoif.GOLDEN_MODEL);
	fifo_tb tb(fifoif.TB);
	monitor mon(fifoif.MONITOR);
	// FIFO_golden_model golden_model(fifoif.DUT);

	


endmodule : top