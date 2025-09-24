
/*######################################################################
## Class Name : EX_Coverage  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Defines functional coverage points for EX stage
######################################################################*/

class EX_Coverage extends uvm_component;
	`uvm_component_utils(EX_Coverage) // Register the component with the factory

	// Declare analysis export and FIFO to receive sequence items
	EX_Seq_Item cov_item;
	uvm_analysis_export #(EX_Seq_Item) cov_export;
	uvm_tlm_analysis_fifo #(EX_Seq_Item) cov_fifo;

	// Coverage group for execution stage signals
	covergroup EX_Stage_grp;
		// Coverpoint for ALU opcodes when ALU is enabled
		alu_opcode: coverpoint cov_item.alu_operator_i iff(cov_item.alu_en_i) {
				bins alu_operator_ADD  = {ALU_ADD};
				bins alu_operator_SUB  = {ALU_SUB};
				bins alu_operator_XOR  = {ALU_XOR};
				bins alu_operator_OR   = {ALU_OR};
				bins alu_operator_AND  = {ALU_AND};
				bins alu_operator_SRA  = {ALU_SRA};
				bins alu_operator_SRL  = {ALU_SRL};
				bins alu_operator_SLL  = {ALU_SLL};
				bins alu_operator_SLTS = {ALU_SLTS};
				bins alu_operator_SLTU = {ALU_SLTU};
				bins alu_operator_DIVU = {ALU_DIVU};
				bins alu_operator_DIV  = {ALU_DIV};
				bins alu_operator_REMU = {ALU_REMU};
				bins alu_operator_REM  = {ALU_REM};
				bins alu_operator_EQ   = {ALU_EQ};
				bins alu_operator_NE   = {ALU_NE};
				bins alu_operator_LTS  = {ALU_LTS};	
				bins alu_operator_LTU  = {ALU_LTU};	
				bins alu_operator_GES  = {ALU_GES};	
				bins alu_operator_GEU  = {ALU_GEU};
        	}

		// Coverpoint for multiplier opcodes when multiplier is enabled
		mult_opcode: coverpoint cov_item.mult_operator_i iff(cov_item.mult_en_i){
				bins mult_operator_MUL   = {MUL_MAC32};
				bins mult_operator_MULH  = {MUL_H};
        	}

		// Coverpoints for ALU operands signed and unsigned cases
		alu_operand_a_unsigned: coverpoint cov_item.alu_operand_a_i iff(cov_item.alu_operator_i inside {ALU_ADD, ALU_SUB, ALU_AND, ALU_OR, ALU_XOR, ALU_SRL, ALU_SLL, ALU_SLTU, ALU_DIVU, ALU_REMU, ALU_EQ, ALU_NE, ALU_LTU, ALU_GEU}) {
				bins max_unsigned = {32'hFFFFFFFF};
				bins zero = {0};
				bins positive = {[1 : 32'h7FFFFFFE]};
		}

		alu_operand_a_signed: coverpoint cov_item.alu_operand_a_i iff(cov_item.alu_operator_i inside {ALU_SLTS, ALU_DIV, ALU_REM, ALU_SRA, ALU_LTS, ALU_GES}) {
				bins max_signed = {32'h7FFFFFFF};
				bins zero = {0};
				bins min_signed = {32'h80000000};
				bins positive = {[1 : 32'h7FFFFFFE]};
				bins negative = {[32'h80000001 : 32'hFFFFFFFF ]};


		}

		alu_operand_b_unsigned: coverpoint cov_item.alu_operand_b_i iff(cov_item.alu_operator_i inside {ALU_ADD, ALU_SUB, ALU_AND, ALU_OR, ALU_XOR, ALU_SRL, ALU_SLL, ALU_SLTU, ALU_DIVU, ALU_REMU, ALU_EQ, ALU_NE, ALU_LTU, ALU_GEU}) {
				bins max_unsigned = {32'hFFFFFFFF};
				bins zero = {0};
				bins positive = {[1 : 32'h7FFFFFFE]};
		}

		alu_operand_b_signed: coverpoint cov_item.alu_operand_b_i iff(cov_item.alu_operator_i inside {ALU_SLTS, ALU_DIV, ALU_REM, ALU_SRA, ALU_LTS, ALU_GES}) {
				bins max_signed = {32'h7FFFFFFF};
				bins zero = {0};
				bins min_signed = {32'h80000000};
				bins positive = {[1 : 32'h7FFFFFFE]};
				bins negative = {[32'h80000001 : 32'hFFFFFFFF]};
		}

		// Coverpoints for multiplier operands with signed/unsigned logic
		mult_operand_a_unsigned: coverpoint cov_item.mult_operand_a_i iff(cov_item.mult_signed_mode_i[0] == 0) {
				bins max_unsigned = {32'hFFFFFFFF};
				bins zero = {0};
				bins positive = {[1 : 32'h7FFFFFFE]};
		}

		mult_operand_a_signed: coverpoint cov_item.mult_operand_a_i iff(cov_item.mult_signed_mode_i[0] == 1) {
				bins max_signed = {32'h7FFFFFFF};
				bins zero = {0};
				bins min_signed = {32'h80000000};
				bins positive = {[1 : 32'h7FFFFFFE]};
				bins negative = {[32'h80000001 : 32'hFFFFFFFF]};
		}

		mult_operand_b_unsigned: coverpoint cov_item.mult_operand_b_i iff(cov_item.mult_signed_mode_i[1] == 0) {
				bins max_unsigned = {32'hFFFFFFFF};
				bins zero = {0};
				bins positive = {[1 : 32'h7FFFFFFE]};
		}

		mult_operand_b_signed: coverpoint cov_item.mult_operand_b_i iff(cov_item.mult_signed_mode_i[1] == 1) {
				bins max_signed = {32'h7FFFFFFF};
				bins zero = {0};
				bins min_signed = {32'h80000000};
				bins positive = {[1 : 32'h7FFFFFFE]};
				bins negative = {[32'h80000001 : 32'hFFFFFFFF]};
		}

		mult_op_signed_mode: coverpoint cov_item.mult_signed_mode_i iff(cov_item.mult_en_i & cov_item.mult_operator_i == MUL_H) {
				bins MULH   = {3};
				bins MULHSU = {1};
				bins MULHU  = {0};
				ignore_bins MULHUS = {2};
		}
 
		// ALU and multiplier enable signal coverpoints
		alu_en: coverpoint cov_item.alu_en_i;
		mult_en: coverpoint cov_item.mult_en_i;

		// Coverpoint to ALU operands are diffrent comparisons
		alu_operands_comp: coverpoint (cov_item.alu_operand_a_i > cov_item.alu_operand_b_i ? 2 : cov_item.alu_operand_a_i == cov_item.alu_operand_b_i ? 1 : 0) {
			bins gt = {2}; 			
			bins equal = {1};
			bins lt = {0};
		}

		// Coverpoint to check if multiplier operands are equal
		mult_operands_equal: coverpoint (cov_item.mult_operand_a_i == cov_item.mult_operand_b_i) {
 			bins equal = {1};
			bins not_equal = {0};
		}

		// Shift amount coverpoint for shift ALU operations
		shift_amount: coverpoint cov_item.alu_operand_b_i[4:0] 
			iff (cov_item.alu_operator_i inside {ALU_SRA, ALU_SRL, ALU_SLL}) {
				bins zero_shift = {0};
				bins full_shift = {31};
				bins partial_shifts = {[1:30]};
		}

		//Cross coverage: ALU unsigned/signed operands
		alu_cross_operands_U: cross alu_operand_a_unsigned, alu_operand_b_unsigned{
			bins pos_pos = binsof(alu_operand_a_unsigned.positive) && binsof(alu_operand_b_unsigned.positive);
			bins zero_zero = binsof(alu_operand_a_unsigned.zero) && binsof(alu_operand_b_unsigned.zero);
			bins max_max = binsof(alu_operand_a_unsigned.max_unsigned) && binsof(alu_operand_b_unsigned.max_unsigned);
			bins pos_zero = (binsof(alu_operand_a_unsigned.positive) && binsof(alu_operand_b_unsigned.zero)) ||
				(binsof(alu_operand_a_unsigned.zero) && binsof(alu_operand_b_unsigned.positive));
			bins pos_max = (binsof(alu_operand_a_unsigned.positive) && binsof(alu_operand_b_unsigned.max_unsigned)) ||
				(binsof(alu_operand_a_unsigned.max_unsigned) && binsof(alu_operand_b_unsigned.positive));
			bins zero_max = (binsof(alu_operand_a_unsigned.zero) && binsof(alu_operand_b_unsigned.max_unsigned)) ||
				(binsof(alu_operand_a_unsigned.max_unsigned) && binsof(alu_operand_b_unsigned.zero));
		}
		
		alu_cross_operands_S: cross alu_operand_a_signed, alu_operand_b_signed{
			bins pos_pos = binsof(alu_operand_a_signed.positive) && binsof(alu_operand_b_signed.positive);
			bins neg_neg = binsof(alu_operand_a_signed.negative) && binsof(alu_operand_b_signed.negative);
			bins zero_zero = binsof(alu_operand_a_signed.zero) && binsof(alu_operand_b_signed.zero);
			bins max_max = binsof(alu_operand_a_signed.max_signed) && binsof(alu_operand_b_signed.max_signed);
			bins min_min = binsof(alu_operand_a_signed.min_signed) && binsof(alu_operand_b_signed.min_signed);
			bins pos_neg = (binsof(alu_operand_a_signed.positive) && binsof(alu_operand_b_signed.negative)) ||
				(binsof(alu_operand_a_signed.negative) && binsof(alu_operand_b_signed.positive));
			bins pos_zero = (binsof(alu_operand_a_signed.positive) && binsof(alu_operand_b_signed.zero)) ||
				(binsof(alu_operand_a_signed.zero) && binsof(alu_operand_b_signed.positive));
			bins pos_max = (binsof(alu_operand_a_signed.positive) && binsof(alu_operand_b_signed.max_signed)) ||
				(binsof(alu_operand_a_signed.max_signed) && binsof(alu_operand_b_signed.positive));
			bins pos_min = (binsof(alu_operand_a_signed.positive) && binsof(alu_operand_b_signed.min_signed)) ||
				(binsof(alu_operand_a_signed.min_signed) && binsof(alu_operand_b_signed.positive));
			bins neg_zero = (binsof(alu_operand_a_signed.negative) && binsof(alu_operand_b_signed.zero)) ||
				(binsof(alu_operand_a_signed.zero) && binsof(alu_operand_b_signed.negative));
			bins neg_max = (binsof(alu_operand_a_signed.negative) && binsof(alu_operand_b_signed.max_signed)) ||
				(binsof(alu_operand_a_signed.max_signed) && binsof(alu_operand_b_signed.negative));
			bins neg_min = (binsof(alu_operand_a_signed.negative) && binsof(alu_operand_b_signed.min_signed)) ||
				(binsof(alu_operand_a_signed.min_signed) && binsof(alu_operand_b_signed.negative));
			bins zero_max = (binsof(alu_operand_a_signed.zero) && binsof(alu_operand_b_signed.max_signed)) ||
				(binsof(alu_operand_a_signed.max_signed) && binsof(alu_operand_b_signed.zero));
			bins zero_min = (binsof(alu_operand_a_signed.zero) && binsof(alu_operand_b_signed.min_signed)) ||
				(binsof(alu_operand_a_signed.min_signed) && binsof(alu_operand_b_signed.zero));
			bins max_min = (binsof(alu_operand_a_signed.max_signed) && binsof(alu_operand_b_signed.min_signed)) ||
				(binsof(alu_operand_a_signed.min_signed) && binsof(alu_operand_b_signed.max_signed));
			}

		// Cross coverage: ALU opcode with unsigned operands
		alu_op_x_operands_U: cross alu_opcode, alu_cross_operands_U {
			ignore_bins non_unsigned_ops = !binsof(alu_opcode) intersect {ALU_ADD, ALU_SUB, ALU_AND, ALU_OR, ALU_XOR, ALU_DIVU, ALU_REMU};
		}

		// Cross coverage: ALU compare with operands
		alu_compare_x_operands: cross alu_opcode, alu_operands_comp {
			ignore_bins non_unsigned_ops = !binsof(alu_opcode) intersect {ALU_SLTU, ALU_EQ, ALU_NE, ALU_LTU, ALU_GEU, ALU_SLTS, ALU_LTS, ALU_GES};
		}

		// Cross coverage: ALU opcode with signed operands
		alu_op_x_operands_S: cross alu_opcode, alu_cross_operands_S {
			ignore_bins non_signed_ops = !binsof(alu_opcode) intersect {ALU_DIV, ALU_REM};
		}

		// Cross coverage: Multiplier unsigned operands
		mul_cross_operands_U: cross mult_operand_a_unsigned, mult_operand_b_unsigned{
			bins pos_pos = binsof(mult_operand_a_unsigned.positive) && binsof(mult_operand_b_unsigned.positive);
			bins zero_zero = binsof(mult_operand_a_unsigned.zero) && binsof(mult_operand_b_unsigned.zero);
			bins max_max = binsof(mult_operand_a_unsigned.max_unsigned) && binsof(mult_operand_b_unsigned.max_unsigned);
			bins pos_zero = (binsof(mult_operand_a_unsigned.positive) && binsof(mult_operand_b_unsigned.zero)) ||
				(binsof(mult_operand_a_unsigned.zero) && binsof(mult_operand_b_unsigned.positive));
			bins pos_max = (binsof(mult_operand_a_unsigned.positive) && binsof(mult_operand_b_unsigned.max_unsigned)) ||
				(binsof(mult_operand_a_unsigned.max_unsigned) && binsof(mult_operand_b_unsigned.positive));
			bins zero_max = (binsof(mult_operand_a_unsigned.zero) && binsof(mult_operand_b_unsigned.max_unsigned)) ||
				(binsof(mult_operand_a_unsigned.max_unsigned) && binsof(mult_operand_b_unsigned.zero));
		}

    		// Cross coverage: Multiplier opcode with signed operands
		mul_op_x_operands_S: cross mult_opcode, mult_operand_a_signed, mult_operand_b_signed  iff(cov_item.mult_signed_mode_i == 2'b11) {
			bins mulh_pos_pos = binsof(mult_operand_a_signed.positive) && binsof(mult_operand_b_signed.positive);
			bins mulh_neg_neg = binsof(mult_operand_a_signed.negative) && binsof(mult_operand_b_signed.negative);
			bins mulh_zero_zero = binsof(mult_operand_a_signed.zero) && binsof(mult_operand_b_signed.zero);
			bins mulh_max_max = binsof(mult_operand_a_signed.max_signed) && binsof(mult_operand_b_signed.max_signed);
			bins mulh_min_min = binsof(mult_operand_a_signed.min_signed) && binsof(mult_operand_b_signed.min_signed);
			bins mulh_pos_neg = (binsof(mult_operand_a_signed.positive) && binsof(mult_operand_b_signed.negative)) ||
				(binsof(mult_operand_a_signed.negative) && binsof(mult_operand_b_signed.positive));
			bins mulh_pos_zero = (binsof(mult_operand_a_signed.positive) && binsof(mult_operand_b_signed.zero)) ||
				(binsof(mult_operand_a_signed.zero) && binsof(mult_operand_b_signed.positive));
			bins mulh_pos_max = (binsof(mult_operand_a_signed.positive) && binsof(mult_operand_b_signed.max_signed)) ||
				(binsof(mult_operand_a_signed.max_signed) && binsof(mult_operand_b_signed.positive));
			bins mulh_pos_min = (binsof(mult_operand_a_signed.positive) && binsof(mult_operand_b_signed.min_signed)) ||
				(binsof(mult_operand_a_signed.min_signed) && binsof(mult_operand_b_signed.positive));
			bins mulh_neg_zero = (binsof(mult_operand_a_signed.negative) && binsof(mult_operand_b_signed.zero)) ||
				(binsof(mult_operand_a_signed.zero) && binsof(mult_operand_b_signed.negative));
			bins mulh_neg_max = (binsof(mult_operand_a_signed.negative) && binsof(mult_operand_b_signed.max_signed)) ||
				(binsof(mult_operand_a_signed.max_signed) && binsof(mult_operand_b_signed.negative));
			bins mulh_neg_min = (binsof(mult_operand_a_signed.negative) && binsof(mult_operand_b_signed.min_signed)) ||
				(binsof(mult_operand_a_signed.min_signed) && binsof(mult_operand_b_signed.negative));
			bins mulh_zero_max = (binsof(mult_operand_a_signed.zero) && binsof(mult_operand_b_signed.max_signed)) ||
				(binsof(mult_operand_a_signed.max_signed) && binsof(mult_operand_b_signed.zero));
			bins mulh_zero_min = (binsof(mult_operand_a_signed.zero) && binsof(mult_operand_b_signed.min_signed)) ||
				(binsof(mult_operand_a_signed.min_signed) && binsof(mult_operand_b_signed.zero));
			bins mulh_max_min = (binsof(mult_operand_a_signed.max_signed) && binsof(mult_operand_b_signed.min_signed)) ||
				(binsof(mult_operand_a_signed.min_signed) && binsof(mult_operand_b_signed.max_signed)); 
			ignore_bins ignore_mac32 = binsof(mult_opcode.mult_operator_MUL);
		}

		// Cross coverage: Multiplier opcode with unsigned operands
		mul_op_x_operands_U: cross mult_opcode, mul_cross_operands_U iff(cov_item.mult_signed_mode_i == 2'b00);

		// Cross coverage: Multiplier opcode with signed a and unsigned b
		mul_op_x_operands_SU: cross mult_opcode, mult_operand_a_signed, mult_operand_b_unsigned iff(cov_item.mult_signed_mode_i == 2'b01){
			bins mulh_pos_pos = binsof(mult_operand_a_signed.positive) && binsof(mult_operand_b_unsigned.positive);
			bins mulh_pos_zero = (binsof(mult_operand_a_signed.positive) && binsof(mult_operand_b_unsigned.zero)) || 
                       		(binsof(mult_operand_a_signed.zero) && binsof(mult_operand_b_unsigned.positive));
			bins mulh_pos_max = binsof(mult_operand_a_signed.positive) && binsof(mult_operand_b_unsigned.max_unsigned);
			bins mulh_neg_pos = binsof(mult_operand_a_signed.negative) && binsof(mult_operand_b_unsigned.positive);
			bins mulh_neg_zero = binsof(mult_operand_a_signed.negative) && binsof(mult_operand_b_unsigned.zero);
			bins mulh_neg_max = binsof(mult_operand_a_signed.negative) && binsof(mult_operand_b_unsigned.max_unsigned);
			bins mulh_zero_zero = binsof(mult_operand_a_signed.zero) && binsof(mult_operand_b_unsigned.zero);
			bins mulh_zero_max = binsof(mult_operand_a_signed.zero) && binsof(mult_operand_b_unsigned.max_unsigned);
			bins mulh_min_zero = binsof(mult_operand_a_signed.min_signed) && binsof(mult_operand_b_unsigned.zero);
			bins mulh_min_pos = binsof(mult_operand_a_signed.min_signed) && binsof(mult_operand_b_unsigned.positive);
			bins mulh_min_max = binsof(mult_operand_a_signed.min_signed) && binsof(mult_operand_b_unsigned.max_unsigned);
			bins mulh_max_min = binsof(mult_operand_a_signed.max_signed) && binsof(mult_operand_b_unsigned.zero);
			bins mulh_max_max = binsof(mult_operand_a_signed.max_signed) && binsof(mult_operand_b_unsigned.max_unsigned);
			bins mulh_max_pos = binsof(mult_operand_a_signed.max_signed) && binsof(mult_operand_b_unsigned.positive);
			ignore_bins ignore_mac32 = binsof(mult_opcode.mult_operator_MUL);
		}
		
		// Cross coverage: Shift opcodes with signed and unsigned operand a
		shift_op_x_shift_operand_U: cross alu_opcode, alu_operand_a_unsigned {
    			ignore_bins non_shift_ops = !binsof(alu_opcode) intersect {ALU_SRL, ALU_SLL};
		}

		shift_op_x_shift_operand_S: cross alu_opcode, alu_operand_a_signed {
    			ignore_bins non_shift_ops = !binsof(alu_opcode) intersect {ALU_SRA};
		}

		// Cross coverage: Shift operations with shift amount
    		shift_op_x_shift_amount: cross alu_opcode, shift_amount {
			ignore_bins non_shift_ops = !binsof(alu_opcode) intersect {ALU_SRA, ALU_SRL, ALU_SLL};
		}
	endgroup

	function new(string name = "EX_Coverage", uvm_component parent = null);
		super.new(name,parent);
		EX_Stage_grp = new();	// Create an instance of the covergroup	
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		//create analysis export and FIFO
		cov_export = new("cov_export", this);
		cov_fifo = new("cov_fifo", this);
	endfunction

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		cov_export.connect(cov_fifo.analysis_export); //connect export to FIFO
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
		forever begin
			cov_fifo.get(cov_item);
			EX_Stage_grp.sample(); // Sample covergroup with the item
		end
	endtask

	function void report_phase (uvm_phase phase);
		`uvm_info("EX_Coverage", $sformatf("EX_Coverage =%0d%%", EX_Stage_grp.get_coverage), UVM_NONE);
	endfunction
endclass
