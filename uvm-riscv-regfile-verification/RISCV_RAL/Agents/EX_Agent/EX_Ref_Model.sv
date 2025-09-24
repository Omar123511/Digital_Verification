/*######################################################################
## Class Name : EX_Ref_Model  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Golden Model for EX Stage reference outputs
## Sends the reference transactions to Scoreboard
######################################################################*/


class EX_Ref_Model extends uvm_component;

		`uvm_component_utils(EX_Ref_Model) // Register EX_Ref_Model with the UVM factory

		// Analysis export to receive sequence items from monitor
		uvm_analysis_export #(EX_Seq_Item) ex_model_export;

		// FIFO buffer for incoming EX_Seq_Items
		uvm_tlm_analysis_fifo #(EX_Seq_Item) ex_model_fifo;

		// Sequence item handles
		EX_Seq_Item seq_item_ex;
		EX_Ref_Seq_Item ref_seq_item;

		// Output port for sending reference model outputs to scoreboard
		uvm_analysis_port #(EX_Ref_Seq_Item) ref_ap;

		// Reference model internal signal flags
		logic		[63:0]	mult_full_result;
		// Partial operands for multiplication
		logic 	[15:0] 	AH;
		logic 	[15:0] 	AL;
		logic 	[15:0]	BH;
		logic 	[15:0] 	BL;

		// Partial multiplication results
		logic 	[31:0] 	ALxBL;
		logic 	[32:0] 	AHxBH;

		// Signed versions of partial operands
		logic signed [15:0] AL_signed;
		logic signed [15:0] AH_signed;
		logic signed [15:0] BL_signed;
		logic signed [15:0] BH_signed;

		int error_count, correct_count;

		function new(string name = "ex_model", uvm_component parent = null);
			super.new(name, parent);
		endfunction

		// Build phase: Initialize the analysis ports
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			ex_model_export = new("ex_model_export", this);
			ex_model_fifo = new("ex_model_fifo", this);
			ref_ap = new("ref_ap", this);
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			ex_model_export.connect(ex_model_fifo.analysis_export);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				// Get transaction from monitor
				ex_model_fifo.get(seq_item_ex);
			
				// Create reference item
				ref_seq_item = EX_Ref_Seq_Item::type_id::create("ref_seq_item");

				// Call reference model logic
				Ref_Model(seq_item_ex, ref_seq_item);

				// Write reference result to analysis port
				ref_ap.write(ref_seq_item);

				
			end
		endtask

		task Ref_Model(input EX_Seq_Item seq_item_chk, output EX_Ref_Seq_Item ref_seq_item);
			// Create and initialize reference output	
			ref_seq_item = EX_Ref_Seq_Item::type_id::create("ref_seq_item");
			ref_seq_item.regfile_alu_wdata_fw_o_ref = 0;
			ref_seq_item.mult_multicycle_o_ref = 0;
			ref_seq_item.branch_decision_o_ref = 0;

			// Reset condition: clear all outputs
			if(!seq_item_chk.rst_n) begin
				ref_seq_item.regfile_alu_wdata_fw_o_ref = 0;
				ref_seq_item.branch_decision_o_ref = 0;
				ref_seq_item.mult_multicycle_o_ref = 0;
			end 
			// ALU operations	
			else if(seq_item_chk.alu_en_i)
			begin
				ref_seq_item.mult_multicycle_o_ref = 0;
				ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i == seq_item_chk.alu_operand_b_i);
				case(seq_item_chk.alu_operator_i)
					// Basic arthimitic and logic operations
					ALU_ADD:  ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.alu_operand_a_i + seq_item_chk.alu_operand_b_i;				
					ALU_SUB:  ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.alu_operand_a_i - seq_item_chk.alu_operand_b_i;
					ALU_XOR:  ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.alu_operand_a_i ^ seq_item_chk.alu_operand_b_i;
					ALU_AND:  ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.alu_operand_a_i & seq_item_chk.alu_operand_b_i;
					ALU_OR:   ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.alu_operand_a_i | seq_item_chk.alu_operand_b_i;
					
					// Signed/Unsigned comparisons
          ALU_EQ:   begin
						ref_seq_item.regfile_alu_wdata_fw_o_ref = (seq_item_chk.alu_operand_a_i == seq_item_chk.alu_operand_b_i)? 32'hffffffff:0; 
						ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i == seq_item_chk.alu_operand_b_i);
					end
					ALU_NE:   begin
						ref_seq_item.regfile_alu_wdata_fw_o_ref = (seq_item_chk.alu_operand_a_i != seq_item_chk.alu_operand_b_i)? 32'hffffffff:0;
						ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i != seq_item_chk.alu_operand_b_i);
					end
					ALU_LTS:  begin
						ref_seq_item.regfile_alu_wdata_fw_o_ref = ($signed(seq_item_chk.alu_operand_a_i) < $signed(seq_item_chk.alu_operand_b_i))? 32'hffffffff:0;
						ref_seq_item.branch_decision_o_ref = ($signed(seq_item_chk.alu_operand_a_i) < $signed(seq_item_chk.alu_operand_b_i));
					end
					ALU_LTU:  begin
						ref_seq_item.regfile_alu_wdata_fw_o_ref = (seq_item_chk.alu_operand_a_i < seq_item_chk.alu_operand_b_i)? 32'hffffffff:0;
						ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i < seq_item_chk.alu_operand_b_i);
					end
					ALU_GES:  begin
						ref_seq_item.regfile_alu_wdata_fw_o_ref = ($signed(seq_item_chk.alu_operand_a_i) >= $signed(seq_item_chk.alu_operand_b_i))? 32'hffffffff:0;
						ref_seq_item.branch_decision_o_ref = ($signed(seq_item_chk.alu_operand_a_i) >= $signed(seq_item_chk.alu_operand_b_i));
					end
					ALU_GEU:  begin
						ref_seq_item.regfile_alu_wdata_fw_o_ref = (seq_item_chk.alu_operand_a_i >= seq_item_chk.alu_operand_b_i)? 32'hffffffff:0;
						ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i >= seq_item_chk.alu_operand_b_i);
					end
					ALU_SLTS: begin
						ref_seq_item.regfile_alu_wdata_fw_o_ref = {31'b0, $signed(seq_item_chk.alu_operand_a_i) < $signed(seq_item_chk.alu_operand_b_i)};
						ref_seq_item.branch_decision_o_ref = $signed(seq_item_chk.alu_operand_a_i) < $signed(seq_item_chk.alu_operand_b_i);
					end
					ALU_SLTU: begin
						ref_seq_item.regfile_alu_wdata_fw_o_ref = {31'b0, seq_item_chk.alu_operand_a_i < seq_item_chk.alu_operand_b_i};
						ref_seq_item.branch_decision_o_ref = seq_item_chk.alu_operand_a_i < seq_item_chk.alu_operand_b_i;
					end
					
					// Division and Remainder
					ALU_DIVU: ref_seq_item.regfile_alu_wdata_fw_o_ref = (seq_item_chk.alu_operand_a_i == 0) ? 32'hFFFFFFFF : seq_item_chk.alu_operand_b_i / seq_item_chk.alu_operand_a_i;
					ALU_DIV:  begin
						if(seq_item_chk.alu_operand_a_i == 0)
							ref_seq_item.regfile_alu_wdata_fw_o_ref = 32'hFFFFFFFF;
						else							ref_seq_item.regfile_alu_wdata_fw_o_ref = $signed(seq_item_chk.alu_operand_b_i)/$signed(seq_item_chk.alu_operand_a_i);
			
					end
					ALU_REMU: ref_seq_item.regfile_alu_wdata_fw_o_ref = (seq_item_chk.alu_operand_a_i == 0) ? seq_item_chk.alu_operand_b_i : seq_item_chk.alu_operand_b_i % seq_item_chk.alu_operand_a_i;
					ALU_REM:  begin
						if(seq_item_chk.alu_operand_a_i == 0)
							ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.alu_operand_b_i;
						else							ref_seq_item.regfile_alu_wdata_fw_o_ref = $signed(seq_item_chk.alu_operand_b_i)%$signed(seq_item_chk.alu_operand_a_i);
			
					end
					
					// Shifts
					ALU_SLL:  ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.alu_operand_a_i << seq_item_chk.alu_operand_b_i[4:0];
					ALU_SRL:  ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.alu_operand_a_i >> seq_item_chk.alu_operand_b_i[4:0];
					ALU_SRA:  ref_seq_item.regfile_alu_wdata_fw_o_ref = $signed(seq_item_chk.alu_operand_a_i) >>> seq_item_chk.alu_operand_b_i[4:0];
				endcase
			end 
			// Multiplier logic
			else if(seq_item_chk.mult_en_i)
			begin
				ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i == seq_item_chk.alu_operand_b_i);
				ref_seq_item.mult_multicycle_o_ref = 0;

				// Split 32-bit operands into 16-bit parts
				AH = seq_item_chk.mult_operand_a_i[31:16];
				AL = seq_item_chk.mult_operand_a_i[15:0];
				BH = seq_item_chk.mult_operand_b_i[31:16];
				BL = seq_item_chk.mult_operand_b_i[15:0];

				// Sign-extend operands for signed modes
				BH_signed = {BH[15], BH};
				BL_signed = {BL[15], BL};
				AH_signed = {AH[15], AH};
				AL_signed = {AL[15], AL};
				case(seq_item_chk.mult_operator_i)
					// Full multiply - result in lower 32 bits
					MUL_I: begin
						case(seq_item_chk.mult_signed_mode_i)
							2'b00: begin
								ALxBL = AL*BL;
								AHxBH = AH*BH;
								mult_full_result = {AHxBH, 32'b0} + {32'b0, ALxBL};
							end
							2'b01: begin							
								ALxBL = $signed(AL_signed) * $signed({1'b0, BL});
								AHxBH = $signed(AH_signed) * $signed({1'b0, BH});
								mult_full_result = {AHxBH, 32'b0} + {32'b0, ALxBL};
							end
							2'b10: begin							
								ALxBL = $signed(BL_signed) * $signed({1'b0, AL});
								AHxBH = $signed(BH_signed) * $signed({1'b0, AH});
								mult_full_result = {AHxBH, 32'b0} + {32'b0, ALxBL};
							end
							2'b11: begin							
								ALxBL = $signed(AL_signed)*$signed(BL_signed);
								AHxBH = $signed(AH_signed)*$signed(BH_signed);
								mult_full_result = {AHxBH, 32'b0} + {32'b0, ALxBL};
							end
						endcase
						ref_seq_item.regfile_alu_wdata_fw_o_ref = mult_full_result[31:0];
					end
					MUL_MAC32: case(seq_item_chk.mult_signed_mode_i)
						2'b00: ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.mult_operand_a_i * seq_item_chk.mult_operand_b_i;
						2'b01: ref_seq_item.regfile_alu_wdata_fw_o_ref = $signed(seq_item_chk.mult_operand_a_i) * seq_item_chk.mult_operand_b_i;
						2'b10: ref_seq_item.regfile_alu_wdata_fw_o_ref = seq_item_chk.mult_operand_a_i * $signed(seq_item_chk.mult_operand_b_i);
						2'b11: ref_seq_item.regfile_alu_wdata_fw_o_ref = $signed(seq_item_chk.mult_operand_a_i) * $signed(seq_item_chk.mult_operand_b_i);
					endcase
					// High multiply - result in upper 32 bits
					MUL_H: begin
						case(seq_item_chk.mult_signed_mode_i)
							2'b00: begin
								mult_full_result = { 32'b0, seq_item_chk.mult_operand_a_i } * {32'b0, seq_item_chk.mult_operand_b_i};
							end
							2'b01: begin
								mult_full_result = $signed( { {32{seq_item_chk.mult_operand_a_i[31]}}, seq_item_chk.mult_operand_a_i } ) * {32'b0, seq_item_chk.mult_operand_b_i};
							end
							2'b10: begin							
								mult_full_result = { 32'b0, seq_item_chk.mult_operand_a_i } * $signed( { {32{seq_item_chk.mult_operand_b_i[31]}}, seq_item_chk.mult_operand_b_i } );
							end
							2'b11: begin
								mult_full_result = $signed( { {32{seq_item_chk.mult_operand_a_i[31]}}, seq_item_chk.mult_operand_a_i } ) * $signed( { {32{seq_item_chk.mult_operand_b_i[31]}}, seq_item_chk.mult_operand_b_i } );
							end
						endcase
						ref_seq_item.regfile_alu_wdata_fw_o_ref = mult_full_result[63:32];
					end
					endcase
			
             		end
			if(seq_item_chk.rst_n)
case(seq_item_chk.alu_operator_i)
          				ALU_EQ:   begin
						ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i == seq_item_chk.alu_operand_b_i);
					end
					ALU_NE:   begin
						ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i != seq_item_chk.alu_operand_b_i);
					end
					ALU_LTS:  begin
						ref_seq_item.branch_decision_o_ref = ($signed(seq_item_chk.alu_operand_a_i) < $signed(seq_item_chk.alu_operand_b_i));
					end
					ALU_LTU:  begin
						ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i < seq_item_chk.alu_operand_b_i);
					end
					ALU_GES:  begin
						ref_seq_item.branch_decision_o_ref = ($signed(seq_item_chk.alu_operand_a_i) >= $signed(seq_item_chk.alu_operand_b_i));
					end
					ALU_GEU:  begin
						ref_seq_item.branch_decision_o_ref = (seq_item_chk.alu_operand_a_i >= seq_item_chk.alu_operand_b_i);
					end
					ALU_SLTS: begin
						ref_seq_item.branch_decision_o_ref = $signed(seq_item_chk.alu_operand_a_i) < $signed(seq_item_chk.alu_operand_b_i);
					end
					ALU_SLTU: begin
						ref_seq_item.branch_decision_o_ref = seq_item_chk.alu_operand_a_i < seq_item_chk.alu_operand_b_i;
					end
             		endcase 
		endtask
	endclass