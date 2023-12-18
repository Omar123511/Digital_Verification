package shift_reg_scoreboard_pkg;
	

	import uvm_pkg::*;
	`include "uvm_macros.svh"

	import shift_reg_seq_item_pkg::*;
	

	class shift_reg_scoreboard extends uvm_scoreboard;
		`uvm_component_utils(shift_reg_scoreboard);
		uvm_analysis_export #(shift_reg_seq_item) sb_export;
		uvm_tlm_analysis_fifo #(shift_reg_seq_item) sb_fifo;

		shift_reg_seq_item seq_item_sb;
		logic [5:0] shift_reg_out_ref;

		int error_count = 0;
		int correct_count = 0;


		function new(string name = "shift_reg_scoreboard", uvm_component parent = null);
			super.new(name, parent);
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			sb_export = new("sb_export", this);
			sb_fifo = new("sb_fifo", this);
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			sb_export.connect(sb_fifo.analysis_export);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				sb_fifo.get(seq_item_sb);
				ref_model(seq_item_sb);
				if (seq_item_sb.dataout != shift_reg_out_ref) begin
					`uvm_error("run_phase", $sformatf("Comparison failed, Transaction recieved by DUT: %0b   While the ref_out: %0b", seq_item_sb.convert2string(), shift_reg_out_ref));
					error_count++;
				end
				else begin
					`uvm_info("run_phase", $sformatf("Correct dataout: %0b", seq_item_sb.convert2string()), UVM_NONE);
					correct_count++;
				end
			end
			
		endtask : run_phase



		task ref_model(shift_reg_seq_item seq_item_chk);
			if(seq_item_chk.reset)
				shift_reg_out_ref = 0;
			else begin
				if (seq_item_chk.mode) begin
					if (seq_item_chk.direction) begin
						shift_reg_out_ref = {seq_item_chk.datain[4:0], seq_item_chk.datain[5]};
					end
					else begin
						shift_reg_out_ref = {seq_item_chk.datain[0], seq_item_chk.datain[5:1]};
					end
				end
				else begin
					if (seq_item_chk.direction) begin
						shift_reg_out_ref = {seq_item_chk.datain[4:0], seq_item_chk.serial_in};
					end
					else begin
						shift_reg_out_ref = {seq_item_chk.serial_in, seq_item_chk.datain[5:1]};
					end
				end
			end
			
		endtask : ref_model


		function void report_phase(uvm_phase phase);
			super.report_phase(phase);
			`uvm_info("report_phase", $sformatf("Total successful transactions: %0d", correct_count), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total failed transactions: %0d", error_count), UVM_MEDIUM);

		endfunction

	endclass : shift_reg_scoreboard
endpackage : shift_reg_scoreboard_pkg
