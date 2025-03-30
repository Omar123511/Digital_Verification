interface intf (input logic i_clk);

	logic i_rst_n;  // Asynchronous reset active low
	logic i_EN;
	logic [3:0] i_address;
	logic [31:0] i_data_in;

	logic [31:0] o_data_out;
	logic o_valid;

	modport DUT (input i_clk, i_rst_n, i_EN, i_address, i_data_in, output o_data_out, o_valid);
	modport TB (output i_rst_n, i_EN, i_address, i_data_in, input i_clk, o_data_out, o_valid);

	
endinterface : intf