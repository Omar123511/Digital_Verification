/*######################################################################
## Interface Name: EX_Interface  
## Engineer : Ahmed Awwad
## Date: MAY 2025
## Description: EX stage inputs and outputs interface
######################################################################*/

import cv32e40p_pkg::*;
interface EX_Interface();
 
	// Clock and reset signals
	bit 			clk;
	logic 			rst_n;

	// Write back signals
	logic 			wb_ready_i;
	logic			regfile_alu_we_i;
	logic		[5:0]	regfile_alu_waddr_i;
	
	// ALU interface
	alu_opcode_e		alu_operator_i;
	logic 		[31:0]	alu_operand_a_i;
	logic 		[31:0]	alu_operand_b_i;
	logic 		[31:0]	alu_operand_c_i;
	logic 			alu_en_i;
	logic			apu_en_i;
	logic			lsu_en_i;
	logic			csr_access_i;
	logic			apu_rvalid_i;
	logic			lsu_ready_ex_i;
	logic			branch_in_ex_i;

	// Multiplier interface
	mul_opcode_e		mult_operator_i;
	logic 		[31:0]	mult_operand_a_i;
	logic 		[31:0]	mult_operand_b_i;
	logic 			mult_en_i;
	logic 		[1:0]	mult_signed_mode_i;
	logic 			mult_multicycle_o;

	// ALU and multiplier control
	logic			alu_is_subrot_i;
	logic			alu_is_clpx_i;
	logic		[1:0]	alu_vec_mode_i;
	logic		[4:0]	bmask_b_i;
	logic			mult_is_clpx_i;
	logic		[31:0]	mult_operand_c_i;
	logic			mult_sel_subword_i;
	logic		[4:0]	mult_imm_i;

	// EX stage outputs
	logic 		[31:0]	regfile_alu_wdata_fw_o;
	logic 			branch_decision_o;
	logic 		[31:0]	jump_target_o;
	logic 		[5:0]	regfile_alu_waddr_fw_o;
	logic 			regfile_alu_we_fw_o;
	logic 			ex_valid_o;
	logic 			ex_ready_o;

	// DUT Modport definition
	modport ex_dut(output mult_multicycle_o, regfile_alu_wdata_fw_o, branch_decision_o, jump_target_o, 
			regfile_alu_waddr_fw_o, regfile_alu_we_fw_o, ex_valid_o, ex_ready_o,
			input clk, rst_n, wb_ready_i, apu_en_i, lsu_en_i, csr_access_i, alu_operator_i, bmask_b_i, lsu_ready_ex_i, mult_is_clpx_i, alu_vec_mode_i, alu_operand_a_i, alu_operand_b_i, alu_is_clpx_i, alu_is_subrot_i, 
			alu_operand_c_i, alu_en_i, mult_operator_i, mult_imm_i, branch_in_ex_i, apu_rvalid_i, mult_operand_a_i, mult_operand_b_i, mult_operand_c_i, mult_sel_subword_i, mult_en_i, mult_signed_mode_i, regfile_alu_waddr_i);

endinterface
