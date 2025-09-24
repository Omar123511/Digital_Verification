
/*######################################################################
## Class Name: Register_File_Sequence_Item  
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .The sequence item contains fields used for generating the stimulus and capturing data from monitors.
######################################################################*/
class Register_File_Sequence_Item extends uvm_sequence_item;
	
    parameter ADDR_WIDTH = 6;
    parameter DATA_WIDTH = 32;
    parameter FPU        = 0;
    parameter ZFINX      = 0;


	logic clk;
    logic rst_n;

	//Read port R1
	rand logic [ADDR_WIDTH-1:0] raddr_a_i;
	logic [DATA_WIDTH-1:0] rdata_a_o;

	//Read port R2
	rand logic [ADDR_WIDTH-1:0] raddr_b_i;
	logic [DATA_WIDTH-1:0] rdata_b_o;

	//Read port R3
	rand logic [ADDR_WIDTH-1:0] raddr_c_i;
	logic [DATA_WIDTH-1:0] rdata_c_o;

	// Write port W1
	rand logic [ADDR_WIDTH-1:0] waddr_a_i;
	rand logic [DATA_WIDTH-1:0] wdata_a_i;
	rand logic                  we_a_i;

	// Write port W2
	rand logic [ADDR_WIDTH-1:0] waddr_b_i;
	rand logic [DATA_WIDTH-1:0] wdata_b_i;
	rand logic                  we_b_i;

	logic [ADDR_WIDTH-1:0] l_addr;
	logic [DATA_WIDTH-1:0] l_data;
	bit l_status;

   `uvm_object_utils(Register_File_Sequence_Item)

   	function new(string name = "Register_File_Sequence_Item");
		super.new(name);
	endfunction

	virtual function void do_print(uvm_printer printer);
		super.do_print(printer);
		printer.print_field("rst_n", rst_n, $bits(rst_n), UVM_HEX);

		printer.print_field("raddr_a_i", raddr_a_i, $bits(raddr_a_i), UVM_HEX);
		printer.print_field("rdata_a_o", rdata_a_o, $bits(rdata_a_o), UVM_HEX);

		printer.print_field("raddr_b_i", raddr_b_i, $bits(raddr_b_i), UVM_HEX);
		printer.print_field("rdata_b_o", rdata_b_o, $bits(rdata_b_o), UVM_HEX);

		printer.print_field("raddr_c_i", raddr_c_i, $bits(raddr_c_i), UVM_HEX);
		printer.print_field("rdata_c_o", rdata_c_o, $bits(rdata_c_o), UVM_HEX);

		printer.print_field("we_a_i", we_a_i, $bits(we_a_i), UVM_HEX);
		printer.print_field("waddr_a_i", raddr_a_i, $bits(waddr_a_i), UVM_HEX);
		printer.print_field("wdata_a_i", wdata_a_i, $bits(wdata_a_i), UVM_HEX);

		printer.print_field("we_b_i", we_b_i, $bits(we_b_i), UVM_HEX);
		printer.print_field("waddr_b_i", waddr_b_i, $bits(waddr_b_i), UVM_HEX);
		printer.print_field("wdata_b_i", wdata_b_i, $bits(wdata_b_i), UVM_HEX);
		
	endfunction



	virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
		Register_File_Sequence_Item rhs_item;
		bit res;

		if (!$cast(rhs_item, rhs)) begin
			`uvm_fatal("COMPARE", "Failed to cast rhs to Register_File_Sequence_Item")
			return 0;
		end
		
		res = 	super.do_compare(rhs, comparer)
				& comparer.compare_field_int("raddr_a_i",    this.raddr_a_i,    rhs_item.raddr_a_i,    32)
				& comparer.compare_field_int("rdata_a_o",    this.rdata_a_o,    rhs_item.rdata_a_o,    32)

				& comparer.compare_field_int("raddr_b_i",    this.raddr_b_i,    rhs_item.raddr_b_i,    32)
				& comparer.compare_field_int("rdata_b_o",    this.rdata_b_o,    rhs_item.rdata_b_o,    32)

				& comparer.compare_field_int("raddr_c_i",    this.raddr_c_i,    rhs_item.raddr_c_i,    32)
				& comparer.compare_field_int("rdata_c_o",    this.rdata_c_o,    rhs_item.rdata_c_o,    32);

		return res;

	endfunction


endclass : Register_File_Sequence_Item
