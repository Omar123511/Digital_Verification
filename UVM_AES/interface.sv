interface intf (input logic i_clk);

	parameter N=128;

	logic [127:0] in;
    logic [N-1:0] key;
    logic [127:0] out;

	// modport DUT (input i_clk, i_rst_n, i_EN, i_address, i_data_in, output o_data_out, o_valid);
	// modport DUT (input in, key output out);

	
endinterface : intf