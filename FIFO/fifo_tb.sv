import shared_pkg::*;
import FIFO_transaction_pkg::*;
import FIFO_scoreboard_pkg::*;



module fifo_tb(fifo_interface.TB fifoif);

	FIFO_transaction trans_DUT;
	FIFO_transaction golden_model_trans;


	// FIFO_golden_model golden_model(.data_in(fifoif.data_in), 
	// 							   .clk(fifoif.clk),
	// 							   .rst_n(fifoif.rst_n),
	// 							   .wr_en(fifoif.wr_en),
	// 							   .rd_en(fifoif.rd_en),
	// 							   .data_out(fifoif.g_data_out),
	// 							   .wr_ack(fifoif.g_wr_ack),
	// 							   .overflow(fifoif.g_overflow),
	// 							   .full(fifoif.g_full),
	// 							   .empty(fifoif.g_empty),
	// 							   .almostfull(fifoif.g_almostfull),
	// 							   .almostempty(fifoif.g_almostempty),
	// 							   .underflow(fifoif.g_underflow));



	initial begin
		trans_DUT = new();
		golden_model_trans = new();
		assert_reset();
		error_count = 0; correct_count = 0;

		trans_DUT.rst_n.rand_mode(0);		
		trans_DUT.constraint_mode(0);
		trans_DUT.c_wr.constraint_mode(1);
		repeat(500) begin
			assert(trans_DUT.randomize());
			@(posedge fifoif.clk)
			fifoif.rst_n = 1;
			fifoif.data_in = trans_DUT.data_in;
			fifoif.wr_en = trans_DUT.wr_en;
			fifoif.rd_en = trans_DUT.rd_en;
		end


		// assert_reset;

		trans_DUT.constraint_mode(0);
		trans_DUT.c_rd.constraint_mode(1);
		trans_DUT.data_in.rand_mode(0);
		// trans_DUT.rst_n.rand_mode(0);
		repeat(500) begin
			assert(trans_DUT.randomize());
			@(posedge fifoif.clk)
			// fifoif.rst_n = 1;
			fifoif.data_in = trans_DUT.data_in;
			fifoif.wr_en = trans_DUT.wr_en;
			fifoif.rd_en = trans_DUT.rd_en;
		end


		trans_DUT.constraint_mode(1);
		trans_DUT.rand_mode(1);
		trans_DUT.c_wr.constraint_mode(0);
		trans_DUT.c_rd.constraint_mode(0);
		repeat(100000) begin
			assert(trans_DUT.randomize());
			@(posedge fifoif.clk)
			fifoif.rst_n = trans_DUT.rst_n;
			fifoif.data_in = trans_DUT.data_in;
			fifoif.wr_en = trans_DUT.wr_en;
			fifoif.rd_en = trans_DUT.rd_en;
		end




		
			// check_data(ob1);

			// trans_DUT.data_out   	= 	fifoif.data_out;
			// trans_DUT.wr_ack     	= 	fifoif.wr_ack;
			// trans_DUT.overflow   	= 	fifoif.overflow;
			// trans_DUT.full       	= 	fifoif.full;
			// trans_DUT.empty 	 	= 	fifoif.empty;
			// trans_DUT.almostfull 	= 	fifoif.almostfull;
			// trans_DUT.almostempty 	=   fifoif.almostempty;

			// golden_model_trans.data_out 	= fifoif.g_data_out;
			// golden_model_trans.wr_ack 		= fifoif.g_wr_ack;
			// golden_model_trans.overflow 	= fifoif.g_overflow;
			// golden_model_trans.full 		= fifoif.g_full;
			// golden_model_trans.empty 		= fifoif.g_empty;
			// golden_model_trans.almostfull 	= fifoif.g_almostfull;
			// golden_model_trans.almostempty 	= fifoif.g_almostempty;

			// FIFO_scoreboard_pkg::check_data(trans_DUT, golden_model_trans);			
		

		assert_test_finished;




	end


	task assert_reset;
		
		fifoif.rst_n = 0;
		repeat(2) @(negedge fifoif.clk);
		fifoif.rst_n = 1;	
	//	fifoif.rst_n = 1;


	endtask : assert_reset

	task assert_test_finished;
		
		test_finished = 1;

	endtask : assert_test_finished

	


	

endmodule : fifo_tb
