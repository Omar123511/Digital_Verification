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


	intf mem_inf(i_clk);

	memory memory_inst0(mem_inf.DUT);

	
	initial begin
		uvm_config_db#(virtual intf)::set(null, "uvm_test_top", "vif", mem_inf);
		run_test("my_test");
	end

endmodule : top
