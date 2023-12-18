module monitor (counter_if.MONITOR c_if);

	bit clk, rst_n, load_n, up_down, ce, max_count, zero; 
	bit [3:0] data_load, count_out;

	assign clk = c_if.clk;
	assign rst_n = c_if.rst_n;
	assign load_n = c_if.load_n;
	assign up_down = c_if.up_down;
	assign ce = c_if.ce;
	assign max_count = c_if.max_count;
	assign zero = c_if.zero;
	assign data_load = c_if.data_load;
	assign count_out = c_if.count_out;

	initial begin
		$monitor("%0t: data_load = %0d, count_out = %0d, load_n = %0b", $time(), data_load, count_out, load_n);
	end


endmodule : monitor