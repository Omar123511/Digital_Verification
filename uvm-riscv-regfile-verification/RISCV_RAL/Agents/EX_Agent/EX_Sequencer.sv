/*######################################################################
## Class Name : EX_Sequencer  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Controls the flow of EX sequence items to the EX_Driver
######################################################################*/

class EX_Sequencer extends uvm_sequencer #(EX_Seq_Item);

		`uvm_component_utils(EX_Sequencer) // Register EX_Sequencer with the UVM factory
	
		function new (string name = "EX_Sequencer", uvm_component parent = null);
			super.new(name,parent);
		endfunction	
endclass