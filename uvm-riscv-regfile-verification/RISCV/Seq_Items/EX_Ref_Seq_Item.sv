/*######################################################################
## Class Name : EX_Seq_Item_Ref  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Defines reference transaction representing 
######################################################################*/


class EX_Ref_Seq_Item extends uvm_sequence_item;
	`uvm_object_utils(EX_Ref_Seq_Item) // Register EX_Ref_Seq_Item with the factory
	
	// Reference signals for EX stage		
	logic 		mult_multicycle_o_ref;
	logic 	[31:0]	regfile_alu_wdata_fw_o_ref;
	logic 		branch_decision_o_ref;

	function new(string name = "EX_Ref_Seq_Item");
		super.new(name);
	endfunction
endclass