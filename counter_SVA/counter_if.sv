interface counter_if #(WIDTH = 4)(clk);


	input bit clk;
	bit rst_n, load_n, up_down, ce;
	bit [WIDTH-1 : 0] data_load, count_out;

	bit max_count, zero;



	modport DUT (input clk, rst_n, load_n, up_down, ce, data_load, output count_out, max_count, zero);

	modport TEST (output load_n, up_down, ce, data_load, input clk, rst_n, count_out, max_count, zero);

	modport MONITOR (input clk, rst_n, load_n, up_down, ce, data_load, count_out, max_count, zero);


endinterface : counter_if
