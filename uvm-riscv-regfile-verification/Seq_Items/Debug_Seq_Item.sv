/*######################################################################
## Class Name : Debug_Seq_Item  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Defines a transaction representing Debug Inteface inputs and outputs
######################################################################*/

class Debug_Seq_Item extends uvm_sequence_item;
		`uvm_object_utils(Debug_Seq_Item)
	
		rand bit debug_req_i;
		logic debug_havereset_o;
		logic debug_running_o;
		logic debug_halted_o;

		function new(string name = "Debug_Seq_Item");
			super.new(name);
		endfunction
endclass
