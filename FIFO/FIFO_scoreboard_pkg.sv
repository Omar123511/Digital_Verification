package FIFO_scoreboard_pkg;

	import FIFO_transaction_pkg::*;
	import shared_pkg::*;
	

	class FIFO_scoreboard;

		parameter FIFO_WIDTH = 16 ;
		parameter FIFO_DEPTH = 8 ;

		// bit [FIFO_WIDTH-1:0] data_out;
		// bit wr_ack, overflow;
		// bit full, empty, almostfull, almostempty, underflow;

		logic [6:0] l_dut_flags, l_golden_flags;



		function void check_data(FIFO_transaction trans_DUT, golden_model_trans);
			// reference_model(F_fxn);
			l_dut_flags = {trans_DUT.wr_ack, trans_DUT.overflow, trans_DUT.full, trans_DUT.empty, trans_DUT.almostfull, trans_DUT.almostempty, trans_DUT.underflow};
			l_golden_flags = {golden_model_trans.wr_ack, golden_model_trans.overflow, golden_model_trans.full, golden_model_trans.empty, golden_model_trans.almostfull, golden_model_trans.almostempty, golden_model_trans.underflow};
			if ((l_dut_flags === l_golden_flags) && (trans_DUT.data_out === golden_model_trans.data_out)) begin
				$display("Test passed successfully");
				correct_count++; 
			end
			else begin
				$display("Test failed");
				error_count++;

			end
			

			
		endfunction

		// function reference_model(FIFO_TRANSACTION F_ref);
			
			

			
			
		// endfunction : reference_model
		

	endclass : FIFO_scoreboard

	
		
	
endpackage : FIFO_scoreboard_pkg