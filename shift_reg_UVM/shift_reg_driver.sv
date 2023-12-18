package shift_reg_driver_pkg;
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	import shift_reg_config_pkg::*;
	import shift_reg_seq_item_pkg::*;
	


	class shift_reg_driver extends uvm_driver #(shift_reg_seq_item);

		`uvm_component_utils(shift_reg_driver);

		virtual shift_reg_if shift_reg_vif;

		shift_reg_config shift_reg_cfg;

		shift_reg_seq_item stim_seq_item;

		function new(string name = "shift_reg_driver", uvm_component parent = null);
			super.new(name, parent);
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			if(!uvm_config_db #(shift_reg_config)::get(this, "", "CFG", shift_reg_cfg))
				`uvm_fatal("build_phase", "Driver - Unable to get config obj");
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			shift_reg_vif = shift_reg_cfg.shift_reg_vif;
			
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				stim_seq_item = shift_reg_seq_item::type_id::create("stim_seq_item");
				seq_item_port.get_next_item(stim_seq_item);
				shift_reg_vif.reset = stim_seq_item.reset;
				shift_reg_vif.serial_in = stim_seq_item.serial_in;
				shift_reg_vif.direction = stim_seq_item.direction;
				shift_reg_vif.mode = stim_seq_item.mode;
				shift_reg_vif.datain = stim_seq_item.datain;
			// @(negedge shift_reg_vif.clk); shift_reg_vif.reset = 0;  
				@(negedge shift_reg_vif.clk);
				seq_item_port.item_done();
				`uvm_info("run_phase", stim_seq_item.convert2string_stimulus(), UVM_HIGH)
			end
			
		endtask : run_phase

		
	endclass : shift_reg_driver
	
endpackage : shift_reg_driver_pkg


	// task run_phase(uvm_phase phase);
	// 		shift_reg_vif.reset = 1;
	// 		shift_reg_vif.serial_in = 0;
	// 		shift_reg_vif.direction = 0;
	// 		shift_reg_vif.mode = 0;
	// 		shift_reg_vif.datain = 0;
	// 		@(negedge shift_reg_vif.clk); shift_reg_vif.reset = 0;  
	// 		forever begin
	// 			@(negedge shift_reg_vif.clk);
	// 			shift_reg_vif.serial_in = $random;
	// 			shift_reg_vif.direction = $random;
	// 			shift_reg_vif.mode = $random;
	// 			shift_reg_vif.datain = $random;

	// 		end
			
	// 	endtask : run_phase
