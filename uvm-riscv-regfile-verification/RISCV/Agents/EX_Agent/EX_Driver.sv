/*######################################################################
## Class Name : EX_Driver  
## Engineer   : Ahmed Awwad
## Date       : MAY 2025
## Description: 
## Drives instruction execution transactions to the EX stage interface 
######################################################################*/

class EX_Driver extends uvm_driver #(EX_Seq_Item);

		`uvm_component_utils(EX_Driver) // Register EX_Driver with the UVM factory

		// Virtual interface handle for driving DUT signals
		virtual EX_Interface EX_vif;

		// Sequence item that holds the stimulus data for the Debug interface
		EX_Seq_Item stim_seq_item;

		function new(string name = "EX_Driver", uvm_component parent = null);
			super.new(name,parent);
		endfunction

		// Build phase: Set up any required configurations or subcomponents
		function void build_phase(uvm_phase phase);
			super.build_phase(phase);	
		endfunction

		// Connect phase: Connect any necessary ports or interfaces
		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
		endfunction

		// Run phase: Drives the stimulus based on received sequence items
		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				// Create a new sequence item to hold the stimulus
				stim_seq_item = EX_Seq_Item::type_id::create("stim_seq_item");

				// Get the next sequence item from the sequencer
				seq_item_port.get_next_item(stim_seq_item);

				// Drive the stimulus to the virtual interface
				@(negedge EX_vif.clk);
				EX_vif.rst_n = stim_seq_item.rst_n;
				EX_vif.wb_ready_i = stim_seq_item.wb_ready_i;

				EX_vif.alu_operator_i = stim_seq_item.alu_operator_i;
				EX_vif.alu_operand_a_i = stim_seq_item.alu_operand_a_i;
				EX_vif.alu_operand_b_i = stim_seq_item.alu_operand_b_i;
				EX_vif.alu_operand_c_i = stim_seq_item.alu_operand_c_i;
				EX_vif.alu_en_i = stim_seq_item.alu_en_i;

				EX_vif.mult_operator_i = stim_seq_item.mult_operator_i; 
				EX_vif.mult_operand_a_i = stim_seq_item.mult_operand_a_i; 
				EX_vif.mult_operand_b_i = stim_seq_item.mult_operand_b_i; 
				EX_vif.mult_operand_c_i = stim_seq_item.mult_operand_c_i;
				EX_vif.mult_en_i = stim_seq_item.mult_en_i; 
				EX_vif.mult_signed_mode_i = stim_seq_item.mult_signed_mode_i;
				EX_vif.alu_is_subrot_i = stim_seq_item.alu_is_subrot_i;
				EX_vif.apu_rvalid_i = stim_seq_item.apu_rvalid_i;
				EX_vif.apu_en_i = stim_seq_item.apu_en_i;
				EX_vif.lsu_en_i = stim_seq_item.lsu_en_i;
				EX_vif.csr_access_i = stim_seq_item.csr_access_i;
				EX_vif.lsu_ready_ex_i = stim_seq_item.lsu_ready_ex_i;
				EX_vif.branch_in_ex_i = stim_seq_item.branch_in_ex_i;
				EX_vif.regfile_alu_we_i = stim_seq_item.regfile_alu_we_i;
				EX_vif.alu_is_clpx_i = stim_seq_item.alu_is_clpx_i;
				EX_vif.alu_vec_mode_i = stim_seq_item.alu_vec_mode_i;
				EX_vif.bmask_b_i = stim_seq_item.bmask_b_i;
				EX_vif.mult_is_clpx_i = stim_seq_item.mult_is_clpx_i;
				EX_vif.mult_operand_c_i = stim_seq_item.mult_operand_c_i;
				EX_vif.mult_sel_subword_i = stim_seq_item.mult_sel_subword_i;
				EX_vif.mult_imm_i = stim_seq_item.mult_imm_i;
				EX_vif.regfile_alu_waddr_i = stim_seq_item.regfile_alu_waddr_i;

				// Mark the sequence item as done
				seq_item_port.item_done();
				`uvm_info("EX_Driver", stim_seq_item.convert2string, UVM_HIGH)
			end
		endtask
	endclass
