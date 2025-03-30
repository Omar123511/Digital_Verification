class my_sequence_item extends uvm_sequence_item;



	`uvm_object_utils(my_sequence_item)

	parameter N=128;


	rand logic [127:0] in;
    rand logic [N-1:0] key;
    logic [127:0] out;


	
	function new(string name = "my_sequence_item");
		super.new(name);
	endfunction

	constraint c_in_key {
		unique {in, key}; 
	}

	
endclass : my_sequence_item