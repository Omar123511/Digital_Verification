package FIFO_transaction_pkg;

	class FIFO_transaction;
		parameter FIFO_WIDTH = 16;
		parameter FIFO_DEPTH = 8;
		bit clk;
		rand bit [FIFO_WIDTH-1:0] data_in;
		rand bit rst_n, wr_en, rd_en;
		bit [FIFO_WIDTH-1:0] data_out;
		bit wr_ack, overflow;
	    bit full, empty, almostfull, almostempty, underflow;

		int WR_EN_ON_DIST = 70;
		int RD_EN_ON_DIST = 30;

		constraint c_rst_n {

			rst_n dist {1 := 98, 0 := 2};
			
		}

		constraint c_wr {

			// wr_en dist {1 := WR_EN_ON_DIST, 0 := 100 - WR_EN_ON_DIST};
			wr_en == 1; rd_en == 0;
			// (rd_en == 0) -> wr_en = 1;
			// (rd_en == 1) -> wr_en = 0;
			
			
		}

		constraint c_rd {

			// rd_en dist {1 := RD_EN_ON_DIST, 0 := 100 - RD_EN_ON_DIST};
			rd_en == 1; wr_en == 0;
			// (wr_en == 0) -> rd_en = 1;
			// (wr_en == 1) -> rd_en = 0;
		}

		constraint c_wr_rd {

			rd_en dist {1 := RD_EN_ON_DIST, 0 := 100 - RD_EN_ON_DIST};
			wr_en dist {1 := WR_EN_ON_DIST, 0 := 100 - WR_EN_ON_DIST};
			// (wr_en == 0) -> rd_en = 1;
			// (wr_en == 1) -> rd_en = 0;
		}
			
	endclass : FIFO_transaction
	
endpackage : FIFO_transaction_pkg