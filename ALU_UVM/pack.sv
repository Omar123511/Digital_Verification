`include "alu_interface.sv"


package pack;

	import p_headers::*;
	
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	
	`include "my_cfg.svh"
	`include "my_sequence_item.svh"
	`include "my_sequence.svh"
	`include "my_sequencer.svh"
	`include "my_driver.svh"
	`include "my_monitor.svh"
	`include "my_agent.svh"
	`include "my_scoreboard.svh"
	`include "my_coverage_collector.svh"
	`include "my_env.svh"
	`include "my_test.svh"
	



	// bit done;
	// function void my_scoreboard::phase_ready_to_end(uvm_phase phase);
	// 	if (phase.is(uvm_run_phase::get)) begin
	// 		if (done != 1) begin 	//replace 4 with config obj
	// 			phase.raise_objection(this, "Test not ready yet");
	// 			fork
	// 			    `uvm_info("PRTESTING", "Phase Ready Testing", UVM_LOW);
	// 				wait_for_ready_to_finish();
	// 				// $display("---------------------->no_items = %0d", no_items);
	// 				// wait_for_ok();
	// 				phase.drop_objection(this, "Test ready to end");
	// 			join_none
	// 		end
	// 	end
	// endfunction : phase_ready_to_end
 
	// task my_test::wait_for_ready_to_finish();
	// 	wait(env.agt.driv.no_items == 4);
	// 	done = 1;
	// endtask: wait_for_ready_to_finish


	
endpackage : pack


