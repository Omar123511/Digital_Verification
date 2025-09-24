/*######################################################################
## Class Name: Instruction_Interface  
## Engineer : Omnia Mohamed
## Date: April 2025
## Description: 
    .Instruction interface
    
######################################################################*/
interface Instruction_Interface;

    bit clk;// clock signal
    bit rst_n;// active low reset.
    logic instr_gnt_i;//It indicates that the Instruction_Driver grant the request.
    logic instr_rvalid_i;//It indicates that the instr_rdata_i is valid. 
    logic [31:0]instr_rdata_i;// Instruction 
    logic instr_req_o;//indicates that the dut is ready to receive data .
    logic [31:0]instr_addr_o;//the address of instruction and it's word aligned

endinterface 