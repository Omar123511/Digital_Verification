/*###################################################################### 
## Module Name: Interrupt_SVA   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This module contains SystemVerilog Assertions to verify the 
    behaviour of the interrupt interface. These properties ensure timing 
    and functional correctness of the interrupt response logic in the DUT.
######################################################################*/
module Interrupt_SVA (
		input bit clk, rst_n,
		input bit [31:0] irq_i,
		input logic irq_ack_o,
		input logic [4:0] irq_id_o,
		input logic Mode, Enable
		);

	// Function to check if an interrupt ID is valid
	function bit is_valid_id(logic [4:0] id); 
		return (id == 3 || id == 7 || id == 11); 
	endfunction 


	// --------------------------------------------------------------------------
	// Assertion 1: Interrupt acknowledgment is valid
	// --------------------------------------------------------------------------
	property p_valid_ack_id;
	@(posedge clk) disable iff (!rst_n)
	irq_ack_o |-> 
	  is_valid_id(irq_id_o) &&          // ID is valid (3,7,11,16-31)
	  Enable;                           // Interrupts are globally enabled
	endproperty
	ASSERT_VALID_ACK_ID: assert property (p_valid_ack_id);
	COV_VALID_ACK_ID: 	 cover property (p_valid_ack_id);

	// --------------------------------------------------------------------------
	// Assertion 2: Interrupts are held until acknowledged
	// --------------------------------------------------------------------------
	generate 
		for (genvar i = 0; i < 32; i++) 
		begin
			if (is_valid_id(i)) 
			begin
				property p_interrupt_held_until_ack;
					@(posedge clk) disable iff (!rst_n)
					$rose(irq_i[i]) |-> 
					irq_i[i] throughout ##[0:$] 
					(irq_ack_o && irq_id_o == i);
				endproperty
			  ASSERT_INTERRUPT_HELD: assert property (p_interrupt_held_until_ack);
			  COV_INTERRUPT_HELD: cover property (p_interrupt_held_until_ack);
			end
		end 
	endgenerate

	// --------------------------------------------------------------------------
	// Assertion 3: irq_ack_o is a single-cycle pulse
	// --------------------------------------------------------------------------
	property p_ack_pulse;
		@(posedge clk) disable iff (!rst_n || irq_i==0)
		$rose(irq_ack_o) |=> !irq_ack_o;
	endproperty
	ASSERT_ACK_PULSE: assert property (p_ack_pulse);
	COV_ACK_PULSE: cover property (p_ack_pulse);

	// --------------------------------------------------------------------------
	// Assertion 4: No acknowledgment when interrupts are disabled
	// --------------------------------------------------------------------------
	property p_no_ack_when_disabled;
		@(posedge clk) disable iff (!rst_n)
		!Enable |-> !irq_ack_o;
	endproperty
	ASSERT_NO_ACK_WHEN_DISABLED: assert property (p_no_ack_when_disabled);
	COV_NO_ACK_WHEN_DISABLED: cover property (p_no_ack_when_disabled);

	// --------------------------------------------------------------------------
	// Assertion 5: Vectored mode uses correct handler offset 
	// --------------------------------------------------------------------------
	// property p_vectored_mode_handler;
	//   @(posedge clk) disable iff (!rst_n || !Mode)
	//   irq_ack_o && Mode |-> 
	//     PC == (mtvec_base + (irq_id_o * 4));
	// endproperty

endmodule