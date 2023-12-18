// `ifndef SHIFT_REG_TEST
// `define SHIFT_REG_TEST

package shift_reg_test_pkg;
	import shift_reg_env_pkg::*;
	import shift_reg_config_pkg::*;
	import shift_reg_main_sequence_pkg::*;
	import shift_reg_reset_sequence_pkg::*;
	
	
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	

	

	class shift_reg_test extends uvm_test;

		`uvm_component_utils(shift_reg_test)
		
		shift_reg_env env;
		shift_reg_config shift_reg_cfg;
		virtual shift_reg_if shift_reg_vif;
		shift_reg_main_sequence main_seq;
		shift_reg_reset_sequence reset_seq;

		function new (string name = "shift_reg_test", uvm_component parent = null);
			super.new(name, parent);
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			env = shift_reg_env::type_id::create("env", this);
			shift_reg_cfg = shift_reg_config::type_id::create("shift_reg_cfg", this);
			main_seq = shift_reg_main_sequence::type_id::create("main_seq", this);
			reset_seq = shift_reg_reset_sequence::type_id::create("reset_seq", this);


			if(!uvm_config_db #(virtual shift_reg_if)::get(this, "", "shift_reg_IF", shift_reg_cfg.shift_reg_vif))
				`uvm_fatal("build_phase", "Unable to get vif of shift_reg from uvm_config_db");

			uvm_config_db #(shift_reg_config)::set(this, "*", "CFG", shift_reg_cfg);
		endfunction


		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			
			phase.raise_objection(this);
			// #100; `uvm_info("run_phase", "Welcome to UVM env", UVM_MEDIUM);
			
			`uvm_info("run_phase", "Reset asserted", UVM_LOW)
			reset_seq.start(env.agt.sqr);
			`uvm_info("run_phase", "Reset deasserted", UVM_LOW)


			`uvm_info("run_phase", "Stimulus generation started", UVM_LOW)
			main_seq.start(env.agt.sqr);
			`uvm_info("run_phase", "Stimulus generation ended", UVM_LOW)


			phase.drop_objection(this);
			
		endtask

	endclass : shift_reg_test
	
endpackage : shift_reg_test_pkg