package shift_reg_env_pkg;
	import uvm_pkg::*;
	`include "uvm_macros.svh"
	import shift_reg_driver_pkg::*;
	import shift_reg_sequencer_pkg::*;
	import shift_reg_agt_pkg::*;
	import shift_reg_scoreboard_pkg::*;
	import shift_reg_coverage_collector_pkg::*;
	
	

		// import shift_reg_seq_item_pkg::*;
	
	class shift_reg_env extends uvm_env;

		`uvm_component_utils(shift_reg_env);

		// shift_reg_driver driver;
		// shift_reg_sequencer sqr;
		shift_reg_agt agt;
		shift_reg_scoreboard sb;
		shift_reg_coverage_collector cov;


		function new (string name = "shift_reg_env", uvm_component parent = null);
			super.new(name, parent);
			
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			// driver = shift_reg_driver::type_id::create("driver", this);
			// sqr = shift_reg_sequencer::type_id::create("sqr", this);
			agt = shift_reg_agt::type_id::create("agt", this);
			sb = shift_reg_scoreboard::type_id::create("sb", this);
			cov = shift_reg_coverage_collector::type_id::create("cov", this);

		endfunction

		function void connect_phase(uvm_phase phase);
			agt.agt_ap.connect(sb.sb_export);
			agt.agt_ap.connect(cov.cov_export);

		endfunction
		
	endclass : shift_reg_env
	
endpackage : shift_reg_env_pkg
