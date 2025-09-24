/*######################################################################
## Class Name : Debug_Sequencer  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Controls the flow of Debug sequence items to the Debug_Driver
######################################################################*/

class Debug_Sequencer extends uvm_sequencer #(Debug_Seq_Item);

		`uvm_component_utils(Debug_Sequencer)
	
		function new (string name = "Debug_Sequencer", uvm_component parent = null);
			super.new(name,parent);
		endfunction	
endclass
