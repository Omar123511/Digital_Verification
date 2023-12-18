interface counter_if (clk);
	
	input bit clk;
	bit rst_n, load_n, up_down, ce, data_load;

	bit count_out, max_count, zero;




endinterface : counter_if
