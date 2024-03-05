import shared_pkg::*;
import FIFO_transaction_pkg::*;
import FIFO_coverage_pkg::*;
import FIFO_scoreboard_pkg::*;




module monitor (fifo_interface.MONITOR fifoif);

	FIFO_transaction trans;
	FIFO_transaction golden_model_trans;

	FIFO_scoreboard score;
	FIFO_coverage cov;

	initial begin
		trans = new();
		score = new();
		cov = new();
		golden_model_trans = new();

		forever begin
			@(negedge fifoif.clk);
			// trans.clk = fifoif.clk;
			trans.rst_n = fifoif.rst_n;
			trans.data_in = fifoif.data_in;
			trans.wr_en = fifoif.wr_en;
			trans.rd_en = fifoif.rd_en;
			trans.data_out = fifoif.data_out;
			trans.full = fifoif.full;
			trans.empty = fifoif.empty;
			trans.almostfull = fifoif.almostfull;
			trans.almostempty = fifoif.almostempty;
			trans.overflow = fifoif.overflow;
			trans.underflow = fifoif.underflow;
			trans.wr_ack = fifoif.wr_ack;

			golden_model_trans.data_out 	= fifoif.g_data_out;
			golden_model_trans.wr_ack 		= fifoif.g_wr_ack;
			golden_model_trans.overflow 	= fifoif.g_overflow;
			golden_model_trans.full 		= fifoif.g_full;
			golden_model_trans.empty 		= fifoif.g_empty;
			golden_model_trans.almostfull 	= fifoif.g_almostfull;
			golden_model_trans.almostempty 	= fifoif.g_almostempty;



			fork
				begin
					cov.sample_data(trans);
				end

				begin
					score.check_data(trans, golden_model_trans);
				end

			join

			if (test_finished) begin
				$display("error_count = %d, correct_count = %d", error_count, correct_count);
				$stop;
			end
		end
	end

endmodule : monitor