/*######################################################################
## Class Name : EX_Config  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Holds configuration settings for the EX_Agent 
## Contains the virtual interface to the EX stage
## Contains agent activity mode (UVM_ACTIVE/UVM_PASSIVE)
######################################################################*/

class EX_Config extends uvm_object;
		`uvm_object_utils(EX_Config) // Register EX_Config with the UVM factory

		// Virtual interface handle for the EX_Interface
		virtual EX_Interface EX_vif;

		uvm_active_passive_enum EX_is_active; // Enum to define whether agent is active or passive

		function new(string name = "EX_cfg");
			super.new(name);
		endfunction
endclass