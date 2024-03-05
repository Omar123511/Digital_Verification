interface fifo_interface (input bit clk);

	parameter FIFO_WIDTH = 16;
	parameter FIFO_DEPTH = 8;


	bit [FIFO_WIDTH-1:0] data_in;
	bit rst_n, wr_en, rd_en;
	bit [FIFO_WIDTH-1:0] data_out;
	bit wr_ack, overflow;
	bit full, empty, almostfull, almostempty, underflow;

	// bit [FIFO_WIDTH-1:0] g_data_in;
	// bit g_rst_n, g_wr_en, g_rd_en;
	bit [FIFO_WIDTH-1:0] g_data_out;
	bit g_wr_ack, g_overflow;
	bit g_full, g_empty, g_almostfull, g_almostempty, g_underflow;

	modport DUT (input data_in, clk, rst_n, wr_en, rd_en, output data_out, wr_ack, overflow, full, empty, almostfull, almostempty, underflow);
	modport TB (output data_in, wr_en, rd_en, input clk, rst_n, data_out, wr_ack, overflow, full, empty, almostfull, almostempty, underflow);
	modport MONITOR (input clk, data_in, rst_n, wr_en, rd_en, data_out, wr_ack, overflow, full, empty, almostfull, almostempty, underflow, g_data_out, g_wr_ack, g_overflow, g_full, g_empty, g_almostfull, g_almostempty, g_underflow);
	// modport DUT_REF (input data_in, clk, rst_n, wr_en, rd_en, output data_out, wr_ack, overflow, full, empty, almostfull, almostempty, underflow);
	modport GOLDEN_MODEL (input data_in, clk, rst_n, wr_en, rd_en, output g_data_out, g_wr_ack, g_overflow, g_full, g_empty, g_almostfull, g_almostempty, g_underflow);


endinterface : fifo_interface