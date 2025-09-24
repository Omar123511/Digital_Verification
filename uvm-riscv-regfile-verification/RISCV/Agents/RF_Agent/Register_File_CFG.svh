/*######################################################################
## Class Name: Register_File_CFG  
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .The configuration contains RF_Is_Active for specifying the agent type.
	.It contains virtual interface to map it to the agent components.
######################################################################*/
class Register_File_CFG extends uvm_object;
	`uvm_object_utils(Register_File_CFG)

	uvm_active_passive_enum RF_Is_Active;

	virtual Register_File_Interface RF_vif;

	
	function new(string name = "Register_File_CFG");
		super.new(name);
	endfunction



endclass : Register_File_CFG
