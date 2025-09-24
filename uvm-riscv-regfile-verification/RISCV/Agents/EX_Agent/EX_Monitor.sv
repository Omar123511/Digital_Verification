/*######################################################################
## Class Name : EX_Monitor  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Monitors the EX stage (ex_vif) signals
## Captures executed transactions and sends them to reference model
## and corresponding subscribers 
######################################################################*/

class EX_Monitor extends uvm_monitor;

		`uvm_component_utils(EX_Monitor) // Register EX_Monitor with the UVM factory

		// Virtual interface handle to connect with DUT
		virtual EX_Interface EX_vif;

		// Sequence item for storing signals observed on the interface
		EX_Seq_Item rsp_seq_item;

		// Analysis port for sending collected sequence items
		uvm_analysis_port #(EX_Seq_Item) mon_ap;

		function new(string name = "EX_Monitor", uvm_component parent = null);
			super.new(name,parent);
		endfunction

		// Build phase: Initialize the analysis port
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			mon_ap = new("mon_ap", this);
		endfunction

		// Run phase: Capture and analyze signals from the Debug interface
		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				rsp_seq_item = EX_Seq_Item::type_id::create("rsp_seq_item");

				// Capture signals from the Debug interface
				@(posedge EX_vif.clk);
				rsp_seq_item.rst_n = EX_vif.rst_n;
				rsp_seq_item.wb_ready_i = EX_vif.wb_ready_i;

				rsp_seq_item.alu_operator_i = EX_vif.alu_operator_i;
				rsp_seq_item.alu_operand_a_i = EX_vif.alu_operand_a_i;
				rsp_seq_item.alu_operand_b_i = EX_vif.alu_operand_b_i;
				rsp_seq_item.alu_operand_c_i = EX_vif.alu_operand_c_i;
				rsp_seq_item.alu_en_i = EX_vif.alu_en_i;

				rsp_seq_item.mult_operator_i = EX_vif.mult_operator_i; 
				rsp_seq_item.mult_operand_a_i = EX_vif.mult_operand_a_i; 
				rsp_seq_item.mult_operand_b_i = EX_vif.mult_operand_b_i; 
				rsp_seq_item.mult_en_i = EX_vif.mult_en_i; 
				rsp_seq_item.mult_signed_mode_i = EX_vif.mult_signed_mode_i; 
	
				rsp_seq_item.alu_is_subrot_i = EX_vif.alu_is_subrot_i;
				rsp_seq_item.alu_is_clpx_i = EX_vif.alu_is_clpx_i;
				rsp_seq_item.alu_vec_mode_i = EX_vif.alu_vec_mode_i;
				rsp_seq_item.bmask_b_i = EX_vif.bmask_b_i;
				rsp_seq_item.mult_is_clpx_i = EX_vif.mult_is_clpx_i;
				rsp_seq_item.mult_operand_c_i = EX_vif.mult_operand_c_i;
				rsp_seq_item.mult_sel_subword_i = EX_vif.mult_sel_subword_i;

				rsp_seq_item.mult_multicycle_o = EX_vif.mult_multicycle_o;
				rsp_seq_item.regfile_alu_wdata_fw_o = EX_vif.regfile_alu_wdata_fw_o; 
				rsp_seq_item.branch_decision_o = EX_vif.branch_decision_o; 
				rsp_seq_item.jump_target_o = EX_vif.jump_target_o; 
				rsp_seq_item.regfile_alu_waddr_fw_o = EX_vif.regfile_alu_waddr_fw_o; 
				rsp_seq_item.regfile_alu_we_fw_o = EX_vif.regfile_alu_we_fw_o; 
				rsp_seq_item.ex_valid_o = EX_vif.ex_valid_o; 
				rsp_seq_item.ex_ready_o = EX_vif.ex_ready_o; 

				// Send the sequence item to the analysis port
				mon_ap.write(rsp_seq_item);
				`uvm_info("EX_Monitor", rsp_seq_item.convert2string(), UVM_HIGH)
		end
	endtask
endclass