/*######################################################################
## Class Name : Debug_Config  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Holds configuration settings for the Debug_Agent 
## Contains the virtual interface to the debug interface
## Contains agent activity mode (UVM_ACTIVE/UVM_PASSIVE)
######################################################################*/

class Debug_Config extends uvm_object;
		`uvm_object_utils(Debug_Config) // Register Debug Config with the UVM factory

		virtual Debug_Interface Debug_vif; // Virtual interface handle for the debug interface

		uvm_active_passive_enum Debug_is_active; // Enum to define whether agent is active or passive

		function new(string name = "Debug_cfg");
			super.new(name);
		endfunction
endclass
