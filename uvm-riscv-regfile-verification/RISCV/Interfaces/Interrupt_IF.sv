/*###################################################################### 
## Interface Name: interrupt_if   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This interface defines the signal-level connection between the UVM 
    testbench and the DUT interrupt interface. It includes the irq_i input, 
    irq_ack_o, and irq_id_o outputs.
######################################################################*/
interface Interrupt_IF ();
    bit clk;
    bit rst_n;

    //ip
    bit [31:0] irq_i;     // interrupt inputs
    
    //op
    logic [4:0]  irq_id_o;  // Interrupt index for taken interrupt
    logic        irq_ack_o; // Interrupt acknowledge

    //Internal signals
    logic Mode;             // Direct mode = 0 or Vectored mode = 1 // connect to mtvec_mode_o
    logic Enable;           //Global interrupt enable bit // connect to mstatus_n.mie
endinterface