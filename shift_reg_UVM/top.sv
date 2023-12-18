import shift_reg_test_pkg::*;

import uvm_pkg::*;
`include "uvm_macros.svh"
module top ();

	bit clk;

	initial begin
		// clk = 0;
		// uvm_component_registry#(shift_reg_test_class)::register_component_type();

		forever #1 clk = ~clk;
	end

	shift_reg_if shift_regif(clk);
	shift_reg DUT (shift_regif);


	initial begin
		uvm_config_db#(virtual shift_reg_if)::set(null, "uvm_test_top", "shift_reg_IF", shift_regif);
		run_test("shift_reg_test");
	end
endmodule : top

