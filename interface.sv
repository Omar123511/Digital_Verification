interface counter_if(clk);


	parameter WIDTH = 4;

	input logic clk;
	logic rst_n;
	logic load_n;
	logic up_down;
	logic ce;
	logic [WIDTH-1:0] data_load;
	logic [WIDTH-1:0] count_out;
	logic max_count;
	logic zero;


	modport DUT (input clk, rst_n, load_n, up_down, ce, data_load, output count_out, max_count, zero);

	modport TB (input clk, count_out, max_count, zero, output rst_n, load_n, up_down, ce, data_load);

	modport SVA (input clk, rst_n, load_n, up_down, ce, data_load, count_out, max_count, zero);


endinterface : counter_if