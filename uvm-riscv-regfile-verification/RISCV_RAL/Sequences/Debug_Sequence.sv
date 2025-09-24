/*##############################################################################
## Class Name : Debug_Sequence                                              
## Engineer   : Ahmed Awwad                                                  
## Date       : MAY 2025                                                    
## Description:                                                              
## UVM sequence for the Debug interface. 
##############################################################################*/

class Debug_Sequence extends uvm_sequence #(Debug_Seq_Item);
		`uvm_object_utils(Debug_Sequence); // Register Debug_Sequence with the factory
		
		// Sequence item for the debug interface
		Debug_Seq_Item seq_item;

		function new(string name = "Debug_Sequence");
			super.new(name);
		endfunction

		task body;
				//Define Debug_Sequence
				seq_item = Debug_Seq_Item::type_id::create("seq_item");
				start_item(seq_item);
				seq_item.debug_req_i = 0;
				finish_item(seq_item);
		endtask
endclass


