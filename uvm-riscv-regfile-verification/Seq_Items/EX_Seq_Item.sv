/*######################################################################
## Class Name : EX_Seq_Item  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Defines a transaction representing EX Stage inputs and outputs
######################################################################*/


class EX_Seq_Item extends uvm_sequence_item;
		`uvm_object_utils(EX_Seq_Item)
		
		//EX_Stage transaction signals	
		rand logic 			rst_n;
		rand logic 			wb_ready_i;
	
		rand alu_opcode_e		alu_operator_i;
		rand logic 		[31:0]	alu_operand_a_i;
		rand logic 		[31:0]	alu_operand_b_i;
		rand logic 		[31:0]	alu_operand_c_i;
		rand logic 			alu_en_i;

		rand mul_opcode_e 		mult_operator_i;
		rand logic 		[31:0]	mult_operand_a_i;
		rand logic 		[31:0]	mult_operand_b_i;
		rand logic 			mult_en_i;
		rand logic 		[1:0]	mult_signed_mode_i;
			logic 			mult_multicycle_o;
			logic			apu_en_i;
			logic			lsu_en_i;
			logic			csr_access_i;
			logic			apu_rvalid_i;
			logic			lsu_ready_ex_i;
			logic			branch_in_ex_i;

		rand logic			regfile_alu_we_i;
		rand logic		[5:0]	regfile_alu_waddr_i;
			logic 		[31:0]	regfile_alu_wdata_fw_o;
			logic 			branch_decision_o;
			logic 		[31:0]	jump_target_o;
			logic 		[5:0]	regfile_alu_waddr_fw_o;
			logic 			regfile_alu_we_fw_o;
			logic 			ex_valid_o;
			logic 			ex_ready_o;
			logic			alu_is_subrot_i;
			logic			alu_is_clpx_i;
			logic		[1:0]	alu_vec_mode_i;
			logic		[4:0]	bmask_b_i;
			logic			mult_is_clpx_i;
			logic		[31:0]	mult_operand_c_i;
			logic			mult_sel_subword_i;
			logic		[4:0]	mult_imm_i;

		function new(string name = "EX_Seq_Item");
			super.new(name);
		endfunction

		constraint a_op { alu_operator_i inside {
    			ALU_ADD, ALU_SUB, ALU_XOR, ALU_AND, ALU_OR,
    			ALU_SLTS, ALU_SLTU,
    			ALU_SLL, ALU_SRL, ALU_SRA
  		}; }

		constraint m_op { mult_operator_i inside {
    			MUL_I, MUL_H
  		}; }

  		constraint no_parallel_units {
    			!(alu_en_i && mult_en_i);
 		}

       		function string convert2string();
			string str;
			$sformat(str, "EX_Seq_Item:\n");
			$sformat(str, "%sInputs:\n", str);
			$sformat(str, "%s  rst_n: %0b  wb_ready_i: %0b\n", str, rst_n, wb_ready_i);
            
			if (alu_en_i) begin
				$sformat(str, "%s  ALU Operation (enabled):\n", str);
				$sformat(str, "%s    op: %s  a: 0x%0h  b: 0x%0h  c: 0x%0h\n", 
				str, alu_operator_i.name(), alu_operand_a_i, alu_operand_b_i, alu_operand_c_i);
            		end
            
			if (mult_en_i) begin
				$sformat(str, "%s  MULT Operation (enabled):\n", str);
				$sformat(str, "%s    op: %s  a: 0x%0h  b: 0x%0h  signed_mode: %0b\n", 
				str, mult_operator_i.name(), mult_operand_a_i, mult_operand_b_i, mult_signed_mode_i);
			end
            
			$sformat(str, "%sOutputs:\n", str);
			$sformat(str, "%s  wdata_fw: 0x%0h  branch: %0b  jump_target: 0x%0h\n", 
			str, regfile_alu_wdata_fw_o, branch_decision_o, jump_target_o);
			$sformat(str, "%s  waddr_fw: 0x%0h  we_fw: %0b  ex_valid: %0b  ex_ready: %0b\n", 
			str, regfile_alu_waddr_fw_o, regfile_alu_we_fw_o, ex_valid_o, ex_ready_o);
            
			return str;
		endfunction
	endclass