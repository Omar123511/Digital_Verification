package shift_reg_coverage_collector_pkg;

	import uvm_pkg::*;
	`include "uvm_macros.svh"

	import  shift_reg_seq_item_pkg::*;
	


	class shift_reg_coverage_collector extends uvm_component;
		`uvm_component_utils(shift_reg_coverage_collector);
		uvm_analysis_export #(shift_reg_seq_item) cov_export;
		uvm_tlm_analysis_fifo #(shift_reg_seq_item) cov_fifo;
		shift_reg_seq_item seq_item_cov;

		//covergroups

		function new(string name = "shift_reg_coverage_collector", uvm_component parent = null);
			super.new(name, parent);
			//create the covergroups
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			cov_export = new("cov_export", this);
			cov_fifo = new("cov_fifo", this);
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			cov_export.connect(cov_fifo.analysis_export);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				cov_fifo.get(seq_item_cov);
				//covergroups sample() method calls  <-------- coverage collector samples the DUT outputs for functional coverage
			end

			
		endtask : run_phase
		
	endclass : shift_reg_coverage_collector
	
endpackage : shift_reg_coverage_collector_pkg
