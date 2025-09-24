/*###################################################################### 
## Class Name: Interrupt_Config 
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This class or block is responsible for setting and retrieving configuration 
    data using the UVM Configuration Database. It is used to 
    share handles such as virtual interfaces, agent configurations, and environment 
    parameters between different components of the UVM testbench.
######################################################################*/
class Interrupt_Config extends uvm_object;
	`uvm_object_utils(Interrupt_Config)

	virtual Interrupt_IF Interrupt_vif;

	uvm_active_passive_enum Interrupt_is_active;

	function new(string name = "Interrupt_Config");
		super.new(name);
	endfunction : new

endclass