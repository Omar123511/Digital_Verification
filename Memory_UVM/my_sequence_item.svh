class my_sequence_item extends uvm_sequence_item;


	`uvm_object_utils(my_sequence_item)


	logic 					i_clk;    // Clock
	rand 	logic 			i_rst_n;  // Asynchronous reset active low
	rand 	logic 			i_EN;
	randc 	logic [3:0] 	i_address;
	rand 	logic [31:0] 	i_data_in;

	logic [31:0] 			o_data_out;
	logic 					o_valid;

	
	function new(string name = "my_sequence_item");
		super.new(name);
	endfunction

	constraint c_i_rst_n {
		i_rst_n dist {0 := 20, 1 := 80}; 
	}

	constraint c_i_EN {
		i_EN dist {0 := 30, 1 := 70};
	}

	
endclass : my_sequence_item