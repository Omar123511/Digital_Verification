/*###################################################################### 
## Class Name: Interrupt_Sequencer   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This class connects sequences with the driver. It controls the flow 
    of interrupt transactions from sequences to the driver.
######################################################################*/
class Interrupt_Sequencer extends uvm_sequencer #(Interrupt_Seq_Item);

	`uvm_component_utils(Interrupt_Sequencer)
	
	function new (string name = "Interrupt_Sequencer", uvm_component parent = null);
		super.new(name,parent);
	endfunction : new

endclass