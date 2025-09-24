/*######################################################################  
## Class Name: Interrupt_Seq_Item    
## Engineer : Abdelrhman Tamer  
## Date: May 2025  
## Description:   
    This sequence item class models interrupt transaction,  
    including signals to be randomized to test the interrupt functionailty.
######################################################################*/
class Interrupt_Seq_Item extends uvm_sequence_item;
	`uvm_object_utils(Interrupt_Seq_Item)
	
	function new (string name = "Interrupt_Seq_Item");
    	super.new(name);
    endfunction : new

	rand int interrupt_id; // ID of the interrupt (3,7,11)

	bit rst_n,acknowledged, Mode, Enable;
	logic [4:0] id;

	// Available interrupt IDs
	local const int Available_ids[] = '{3,7,11};	// assume no custom interrupts

	// Constraints to ensure valid interrupts
	constraint valid_interrupt_id {
		interrupt_id inside {Available_ids};
	}

	function string convert2string();
        return $sformatf("rst_n = %b, interrupt_id = %0d, Mode = %0b, Enable = %0b",rst_n, interrupt_id, Mode, Enable);  
    endfunction : convert2string
endclass
