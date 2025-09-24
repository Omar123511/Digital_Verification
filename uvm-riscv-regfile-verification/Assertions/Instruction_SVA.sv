
/*######################################################################
## Module Name: Instruction_SVA 
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This module contains checks related to instruction interface .
    .It is used to verify the handshake between the dut and instruction agent based on open bus interface (obi) protocol.
######################################################################*/
import uvm_pkg::*;
`include "uvm_macros.svh"

module Instruction_SVA(
    input bit clk,
    input bit   rst_n,
    input logic instr_gnt_i,
    input logic instr_rvalid_i,
    input logic [31:0]instr_rdata_i,
    input logic instr_req_o,
    input logic [31:0]instr_addr_o);

    //Check that when reset is asserted low, instr_req_o shall be asserted low.
    property rst_check;
		!rst_n  |-> (instr_req_o==0 );
    endproperty


    //Check that the least significant two bits of instruction set to 11
    property opcode_check; 
        @(posedge clk) disable iff (!rst_n)
        (instr_rvalid_i) |-> (instr_rdata_i[1:0] ==2'b11);
    endproperty

    // Check that instr_addr_o is valid  when instr_req_o is asserted high.
    property instr_addr_o_valid_check; 
        @(posedge clk) disable iff (!rst_n)
        (instr_req_o) |-> (!$isunknown(instr_addr_o));
    endproperty

    //Check that instr_req_o is asserted high until instr_gnt_i is asserted high.
    property instr_req_o_valid_check; 
        @(posedge clk) disable iff (!rst_n)
        $rose(instr_req_o) |-> instr_req_o until (instr_gnt_i);
    endproperty

    //Check that when instr_rvalid_i is asserted high, instr_rdata_i is valid  (not x ). 
    property instr_rdata_i_valid_check;
        @(posedge clk) disable iff (!rst_n)
        (instr_rvalid_i) |-> (!$isunknown(instr_rdata_i));
    endproperty


    //check that when request is asserted low, the grant is asserted low.
    property no_gnt_req;
        @(posedge clk) disable iff (!rst_n)
       !(instr_req_o) |-> !(instr_gnt_i);
    endproperty

    //check that the grant is asserted high for only one cycle.
    property gnt_high_one_cycle;
        @(posedge clk) disable iff (!rst_n)
       (instr_gnt_i) |-> ##1 !(instr_gnt_i);
    endproperty

    //check that the valid is asserted high after gnt is asserted high by one cycle.
    property valid_after_gnt;
        @(posedge clk) disable iff (!rst_n)
       (instr_gnt_i) |-> ##[1:2] (instr_rvalid_i);
    endproperty

    //check that the valid is only asserted high for one cycle.
    property valid_high_one_cycle;
        @(posedge clk) disable iff (!rst_n)
       (instr_rvalid_i) |-> ##1 (!instr_rvalid_i);
    endproperty


    //Check that address remains stable while request is asserted high and no grant.
    property addr_stable_no_gnt;
        @(posedge clk) disable iff (!rst_n)
        (instr_req_o && !instr_gnt_i) |=> $stable(instr_addr_o);
    endproperty

    //Check that address remains stable while gnt is asserted high.
    property addr_stable_gnt;
        @(posedge clk) disable iff (!rst_n)
        (instr_gnt_i) |-> $stable(instr_addr_o);
    endproperty



    rst_check_assert1: assert property(@(posedge clk) rst_check)
			else `uvm_fatal("Instruction_SVA_Failed","=======================rst_check_assert1 failed=======================")
    rst_check_cover1: cover  property(@(posedge clk) rst_check);


    opcode_check_assert2: assert property( opcode_check)
			else `uvm_fatal("Instruction_SVA_Failed","=======================opcode_check_assert2 failed =======================");		
    opcode_check_cover2: cover property( opcode_check);


    instr_addr_o_valid_check_assert3: assert property(instr_addr_o_valid_check)
			else `uvm_fatal("Instruction_SVA_Failed","=======================instr_addr_o_valid_check_assert3 failed =======================");		
    instr_addr_o_valid_check_cover3: cover property( instr_addr_o_valid_check);


    instr_req_o_valid_check_assert4: assert property( instr_req_o_valid_check)
			else `uvm_fatal("Instruction_SVA_Failed","=======================instr_req_o_valid_check_assert4 failed =======================");		
    instr_req_o_valid_check_cover4: cover property( instr_req_o_valid_check);


    instr_rdata_i_valid_check_assert5: assert property(instr_rdata_i_valid_check)
			else `uvm_fatal("Instruction_SVA_Failed","=======================instr_rdata_i_valid_check_assert5 failed =======================")	;	
    instr_rdata_i_valid_check_cover5: cover   property(instr_rdata_i_valid_check);


    no_gnt_req_assert6: assert property(no_gnt_req)
			else `uvm_fatal("Instruction_SVA_Failed","=======================no_gnt_req_assert6 failed =======================")	;	
    no_gnt_req_cover6: cover   property(no_gnt_req);


    gnt_high_one_cycle_assert7: assert property(gnt_high_one_cycle)
			else `uvm_fatal("Instruction_SVA_Failed","=======================gnt_high_one_cycle_assert7 failed =======================")	;	
    gnt_high_one_cycle_cover7: cover   property(gnt_high_one_cycle);


    valid_after_gnt_assert8: assert property(valid_after_gnt)
			else `uvm_fatal("Instruction_SVA_Failed","=======================valid_after_gnt_assert8 failed =======================")	;	
    valid_after_gnt_cover8: cover   property(valid_after_gnt);


    valid_high_one_cycle_assert9: assert property(valid_high_one_cycle)
			else `uvm_fatal("Instruction_SVA_Failed","=======================valid_high_one_cycle_assert9 failed =======================")	;	
    valid_high_one_cycle_cover9: cover   property(valid_high_one_cycle);


    addr_stable_no_gnt_assert10: assert property(addr_stable_no_gnt)
			else `uvm_fatal("Instruction_SVA_Failed","=======================addr_stable_no_gnt_assert10 failed =======================")	;	
    addr_stable_no_gnt_cover10: cover   property(addr_stable_no_gnt);


    addr_stable_gnt_assert11: assert property(addr_stable_gnt)
			else `uvm_fatal("Instruction_SVA_Failed","=======================addr_stable_gnt_assert11 failed =======================")	;	
    addr_stable_gnt_cover11: cover   property(addr_stable_gnt);

    
endmodule
