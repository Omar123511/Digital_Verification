
/*######################################################################
## Module Name: EX_SVA 
## Engineer : Ahmed Awwad
## Date: May 2025
## Description:
    .This module contains checks related to EX interface .
######################################################################*/
module EX_SVA(EX_Interface ex_ifc);

	import cv32e40p_pkg::*;

	always_comb 
	begin 
		if(!ex_ifc.rst_n) begin
			ex_assert_rst_result: 		assert final (ex_ifc.regfile_alu_wdata_fw_o == 0);
			ex_assert_rst_mult_multi_cycle:	assert final (ex_ifc.mult_multicycle_o == 0);
			ex_assert_rst_branch_decision: 	assert final (ex_ifc.branch_decision_o == 0);
			ex_assert_rst_jump_addr: 	assert final (ex_ifc.jump_target_o == 0);
			ex_assert_rst_w_addr: 		assert final (ex_ifc.regfile_alu_waddr_fw_o == 0);
			ex_assert_rst_w_enable: 	assert final (ex_ifc.regfile_alu_we_fw_o == 0);
			ex_assert_rst_ex_valid: 	assert final (ex_ifc.ex_valid_o == 0);
			ex_assert_rst_ex_ready: 	assert final (ex_ifc.ex_ready_o == 1);
		end else begin
			ex_assert_jump_addr: 		assert final (ex_ifc.jump_target_o == ex_ifc.alu_operand_c_i);
			ex_assert_w_addr: 		assert final (ex_ifc.regfile_alu_waddr_fw_o == ex_ifc.regfile_alu_waddr_i);
			ex_assert_w_en: 		assert final (ex_ifc.regfile_alu_we_fw_o  == ex_ifc.regfile_alu_we_i);
		end 
	end

	property alu_single_cycle_instruction(op);
  		@(posedge ex_ifc.clk)
 		 disable iff (!ex_ifc.rst_n | ex_ifc.lsu_en_i)
  		$rose(ex_ifc.alu_en_i) && $past(ex_ifc.ex_ready_o) && ex_ifc.alu_operator_i == op |->  ex_ifc.ex_valid_o;
	endproperty

	ex_assert_add_cycles:  assert property (alu_single_cycle_instruction(ALU_ADD));
	ex_assert_sub_cycles:  assert property (alu_single_cycle_instruction(ALU_SUB));
	ex_assert_xor_cycles:  assert property (alu_single_cycle_instruction(ALU_XOR));
	ex_assert_or_cycles:   assert property (alu_single_cycle_instruction(ALU_OR));
	ex_assert_and_cycles:  assert property (alu_single_cycle_instruction(ALU_AND));
	ex_assert_sra_cycles:  assert property (alu_single_cycle_instruction(ALU_SRA));
	ex_assert_srl_cycles:  assert property (alu_single_cycle_instruction(ALU_SRL));
	ex_assert_sll_cycles:  assert property (alu_single_cycle_instruction(ALU_SLL));
	ex_assert_slts_cycles: assert property (alu_single_cycle_instruction(ALU_SLTS));
	ex_assert_sltu_cycles: assert property (alu_single_cycle_instruction(ALU_SLTU));
	ex_assert_eq_cycles:   assert property (alu_single_cycle_instruction(ALU_EQ));
	ex_assert_ne_cycles:   assert property (alu_single_cycle_instruction(ALU_NE));
	ex_assert_lts_cycles:  assert property (alu_single_cycle_instruction(ALU_LTS));
	ex_assert_ltu_cycles:  assert property (alu_single_cycle_instruction(ALU_LTU));
	ex_assert_ges_cycles:  assert property (alu_single_cycle_instruction(ALU_GES));
	ex_assert_geu_cycles:  assert property (alu_single_cycle_instruction(ALU_GEU));

	ex_cover_add_cycles:  cover property (alu_single_cycle_instruction(ALU_ADD));
	ex_cover_sub_cycles:  cover property (alu_single_cycle_instruction(ALU_SUB));
	ex_cover_xor_cycles:  cover property (alu_single_cycle_instruction(ALU_XOR));
	ex_cover_or_cycles:   cover property (alu_single_cycle_instruction(ALU_OR));
	ex_cover_and_cycles:  cover property (alu_single_cycle_instruction(ALU_AND));
	ex_cover_sra_cycles:  cover property (alu_single_cycle_instruction(ALU_SRA));
	ex_cover_srl_cycles:  cover property (alu_single_cycle_instruction(ALU_SRL));
	ex_cover_sll_cycles:  cover property (alu_single_cycle_instruction(ALU_SLL));
	ex_cover_slts_cycles: cover property (alu_single_cycle_instruction(ALU_SLTS));
	ex_cover_sltu_cycles: cover property (alu_single_cycle_instruction(ALU_SLTU));
	ex_cover_eq_cycles:   cover property (alu_single_cycle_instruction(ALU_EQ));
	ex_cover_ne_cycles:   cover property (alu_single_cycle_instruction(ALU_NE));
	ex_cover_lts_cycles:  cover property (alu_single_cycle_instruction(ALU_LTS));
	ex_cover_ltu_cycles:  cover property (alu_single_cycle_instruction(ALU_LTU));
	ex_cover_ges_cycles:  cover property (alu_single_cycle_instruction(ALU_GES));
	ex_cover_geu_cycles:  cover property (alu_single_cycle_instruction(ALU_GEU));

	property alu_multicycle_instruction(op);
  		@(posedge ex_ifc.clk)
 		disable iff (!ex_ifc.rst_n)
  		ex_ifc.alu_en_i && $past(ex_ifc.ex_ready_o) && ex_ifc.alu_operator_i == op |-> ##[2:34] ex_ifc.ex_valid_o;
	endproperty

	ex_assert_divu_cycles: assert property (alu_multicycle_instruction(ALU_DIVU));
	ex_assert_div_cycles:  assert property (alu_multicycle_instruction(ALU_DIV));
	ex_assert_remu_cycles: assert property (alu_multicycle_instruction(ALU_REMU));
	ex_assert_rem_cycles:  assert property (alu_multicycle_instruction(ALU_REM));

	ex_cover_divu_cycles: cover property (alu_multicycle_instruction(ALU_DIVU));
	ex_cover_div_cycles:  cover property (alu_multicycle_instruction(ALU_DIV));
	ex_cover_remu_cycles: cover property (alu_multicycle_instruction(ALU_REMU));
	ex_cover_rem_cycles:  cover property (alu_multicycle_instruction(ALU_REM));

	property alu_div_zero_instruction(op);
  		@(posedge ex_ifc.clk)
 		disable iff (!ex_ifc.rst_n)
  		ex_ifc.alu_en_i && $past(ex_ifc.ex_ready_o) && ex_ifc.alu_operator_i == op && ex_ifc.alu_operand_a_i == 0 |-> ##34 ex_ifc.ex_valid_o;
	endproperty

	ex_assert_divu_zero_cycles: assert property (alu_div_zero_instruction(ALU_DIVU));
	ex_assert_div_zero_cycles:  assert property (alu_div_zero_instruction(ALU_DIV));
	ex_assert_remu_zero_cycles: assert property (alu_div_zero_instruction(ALU_REMU));
	ex_assert_rem_zero_cycles:  assert property (alu_div_zero_instruction(ALU_REM));

	ex_cover_divu_zero_cycles: cover property (alu_div_zero_instruction(ALU_DIVU));
	ex_cover_div_zero_cycles:  cover property (alu_div_zero_instruction(ALU_DIV));
	ex_cover_remu_zero_cycles: cover property (alu_div_zero_instruction(ALU_REMU));
	ex_cover_rem_zero_cycles:  cover property (alu_div_zero_instruction(ALU_REM));

	property mult_single_cycle_instruction(op);
  		@(posedge ex_ifc.clk)
 		 disable iff (!ex_ifc.rst_n)
  		ex_ifc.mult_en_i && $past(ex_ifc.ex_ready_o) && ex_ifc.mult_operator_i == op |->  ex_ifc.ex_valid_o;
	endproperty

	ex_assert_mul_cycles:  assert property (mult_single_cycle_instruction(MUL_MAC32));

	ex_cover_mul_cycles:  cover property (mult_single_cycle_instruction(MUL_MAC32));

	property mult_multicycle_instruction(op);
  		@(posedge ex_ifc.clk)
 		disable iff (!ex_ifc.rst_n)
  		ex_ifc.mult_en_i && $past(ex_ifc.ex_ready_o) && ex_ifc.mult_operator_i == op |-> ##1 ex_ifc.mult_multicycle_o[*3] ##1 ex_ifc.ex_valid_o;
	endproperty

	ex_assert_mulh_cycles:  assert property (mult_multicycle_instruction(MUL_H));

	ex_cover_mulh_cycles:  cover property (mult_multicycle_instruction(MUL_H));

	property multicycle_single_cycle_instruction(op);
  		@(posedge ex_ifc.clk)
 		 disable iff (!ex_ifc.rst_n)
  		ex_ifc.mult_en_i && $past(ex_ifc.ex_ready_o) && ex_ifc.mult_operator_i == op |->  !ex_ifc.mult_multicycle_o;
	endproperty

	ex_assert_mul_multicycle: assert property (multicycle_single_cycle_instruction(MUL_MAC32));

	ex_cover_mul_multicycle:  cover property (multicycle_single_cycle_instruction(MUL_MAC32));
endmodule
