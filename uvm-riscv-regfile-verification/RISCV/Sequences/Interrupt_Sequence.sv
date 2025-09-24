/*###################################################################### 
## Class Name: Interrupt_Sequence   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This file defines the sequences of interrupt stimulis to be driven 
    to the DUT. It includes various scenarios like no interrupt scenario and interrupt one.
######################################################################*/
class No_Interrupt_Sequence extends uvm_sequence#(Interrupt_Seq_Item);
	`uvm_object_utils(No_Interrupt_Sequence)

	// Number of interrupts to generate
	int num_interrupts;

	function new(string name = "No_Interrupt_Sequence");
	super.new(name);
	endfunction

	task body();
	Interrupt_Seq_Item item;
		item = Interrupt_Seq_Item::type_id::create("item");

		start_item(item);
		item.valid_interrupt_id.constraint_mode(0);// to disable interrupt mode constraint
		if (!item.randomize() with {interrupt_id==0;}) 
		`uvm_error("No_Interrupt_Sequence", "Failed to randomize interrupt item")
		finish_item(item);

	endtask
endclass
/*
/the following sequence is used to generate interrupt different modes(3,7,11);
(irq_i[11], irq_i[7], and irq_i[3] correspond to the Machine External Interrupt (MEI), 
Machine Timer Interrupt (MTI), and Machine Software Interrupt (MSI) respectively.)

*/
/* 
- To enable the interrupt these instructions should be called by instruction agent before calling the interrupt sequence 

li t0, 0x8
csrs mstatus, t0       // Step 1: enable global interrupts

li t0, 0x8
csrs mie, t0           // Enable MSIE (bit 3)

li t0, 0x80
csrs mie, t0           // Enable MTIE (bit 7)

li t0, 0x800
csrs mie, t0           // Enable MEIE (bit 11)

*/

class Interrupt_Sequence extends uvm_sequence#(Interrupt_Seq_Item);
	`uvm_object_utils(Interrupt_Sequence)

	// Number of interrupts to generate
	int num_interrupts;

	function new(string name = "Interrupt_Sequence");
	super.new(name);
	endfunction

	task body();
	Interrupt_Seq_Item item;
	num_interrupts = $urandom_range(0, 10);

    `uvm_info("Interrupt_Sequence", $sformatf("num_interrupts = %0d", num_interrupts), UVM_MEDIUM)

	repeat (num_interrupts) begin
		item = Interrupt_Seq_Item::type_id::create("item");

		start_item(item);
		if (!item.randomize() ) 
		`uvm_error("Interrupt_Sequence", "Failed to randomize interrupt item")
		finish_item(item);
	end
	endtask
endclass
