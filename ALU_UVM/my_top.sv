// `include "interface.sv"

module my_top ();

	import uvm_pkg::*;
	`include "uvm_macros.svh"
	
	import pack::*;

	bit clk, rst_n;

	alu_if intf(clk, rst_n);

	ALU DUT (
    .clk (intf.clk),
    .rst_n (intf.rst_n),
   	.ALU_en(intf.ALU_en),
   	.a_en  (intf.a_en),
   	.b_en  (intf.b_en),
   	.a_op  (intf.a_op),
   	.b_op  (intf.b_op),
   	.A     (intf.A),
   	.B     (intf.B),
   	.C     (intf.C)
   );

	always #5 clk = ~clk;

	initial begin
    	rst_n = 0;
  	  	#5 rst_n =1;
  	  	#5 rst_n = 0;
  	  	#5 rst_n =1;
    end

    bind ALU ALU_SVA ALU_SVA_inst0(intf); 

	initial begin
		uvm_config_db#(virtual interface alu_if)::set(null, "uvm_test_top", "my_vif", intf);
	end 

	initial begin
		run_test("my_test");
	end
	

endmodule : my_top