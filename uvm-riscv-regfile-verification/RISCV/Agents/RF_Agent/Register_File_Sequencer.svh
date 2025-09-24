/*######################################################################
## Class Name: Register_File_Sequencer  
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .The sequencer generates the sequence items to be then send them to the driver.
######################################################################*/
class Register_File_Sequencer extends uvm_sequencer #(Register_File_Sequence_Item);

	`uvm_component_utils(Register_File_Sequencer)

	function new (string name = "Register_File_Sequencer", uvm_component parent = null);
		super.new(name,parent);
	endfunction	
endclass
