module top ();
	import uvm_pkg::*;
	`include "uvm_macros.svh"
	import my_package::*;

	logic i_clk;

	initial begin
		i_clk = 0;
		forever begin
			#1 i_clk = ~i_clk;
		end
	end


	intf AES_inf(i_clk);

	AES_Encrypt AES_inst0 (.in(AES_inf.in), .key(AES_inf.key), .out(AES_inf.out));
	
	initial begin
		uvm_config_db#(virtual intf)::set(null, "uvm_test_top", "vif", AES_inf);
		run_test("my_test");
	end

endmodule : top
