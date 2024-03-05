package FIFO_coverage_pkg;

	import FIFO_transaction_pkg::*;

	class FIFO_coverage;

		FIFO_transaction F_cvg_txn; 

		function void sample_data(input FIFO_transaction F_txn);

			// F_txn = F_cvg_txn;
			F_cvg_txn = F_txn;
			cg.sample();
			
		endfunction

		covergroup cg;

			cp_wr : coverpoint F_cvg_txn.wr_en{
				option.weight = 0;
			}

			cp_rd : coverpoint F_cvg_txn.rd_en{
				option.weight = 0;
			}

			cp_full : coverpoint F_cvg_txn.full{
				option.weight = 0;
			}

			cp_empty : coverpoint F_cvg_txn.empty{
				option.weight = 0;
			}

			cp_almostfull : coverpoint F_cvg_txn.almostfull{
				option.weight = 0;
			}

			cp_almostempty : coverpoint F_cvg_txn.almostempty{
				option.weight = 0;
			}

			cp_overflow : coverpoint F_cvg_txn.overflow{
				option.weight = 0;
			}

			cp_underflow : coverpoint F_cvg_txn.underflow{
				option.weight = 0;
			}

			cp_wrack : coverpoint F_cvg_txn.wr_ack{
				option.weight = 0;
			}

			cc_wr_rd_full : cross cp_wr, cp_rd, cp_full;

			cc_wr_rd_empty : cross cp_wr, cp_rd, cp_empty;

			cc_wr_rd_almostfull : cross cp_wr, cp_rd, cp_almostfull;

			cc_wr_rd_almostempty : cross cp_wr, cp_rd, cp_almostempty;

			cc_wr_rd_overflow : cross cp_wr, cp_rd, cp_overflow;

			cc_wr_rd_underflow : cross cp_wr, cp_rd, cp_underflow;

			cc_wr_rd_wrack : cross cp_wr, cp_rd, cp_wrack;


			
		endgroup : cg

		function new();
			cg = new ;
			F_cvg_txn = new;
		endfunction


		
	endclass : FIFO_coverage


	
endpackage : FIFO_coverage_pkg