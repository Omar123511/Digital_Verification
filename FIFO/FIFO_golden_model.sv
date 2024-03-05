////////////////////////////////////////////////////////////////////////////////
// Author: Omar Magdy
// 
//
// Description: FIFO Golden Model Design 
// 
////////////////////////////////////////////////////////////////////////////////


module FIFO_golden_model (fifo_interface.GOLDEN_MODEL fifoif);


	// parameter FIFO_WIDTH = 16;
	// parameter FIFO_DEPTH = 8;
	// input [FIFO_WIDTH-1:0] data_in;
	// input clk, rst_n, wr_en, rd_en;
	// output reg [FIFO_WIDTH-1:0] data_out;
	// output reg wr_ack, overflow;
	// output full, empty, almostfull, almostempty, underflow;


	localparam max_fifo_addr = $clog2(fifoif.FIFO_DEPTH);

	reg [fifoif.FIFO_WIDTH-1:0] mem [fifoif.FIFO_DEPTH-1:0];

	reg [max_fifo_addr-1:0] wr_ptr, rd_ptr;
	reg [max_fifo_addr:0] count;



	always_ff @(posedge fifoif.clk or negedge fifoif.rst_n) begin : write_proc		//Write process logic
		if(~fifoif.rst_n) begin
			 wr_ptr <= 0;
		end else begin
			 if (fifoif.wr_en && count < fifoif.FIFO_DEPTH) begin
			 	mem[wr_ptr] <= fifoif.data_in;
			 	wr_ptr <= wr_ptr + 1;
			 	fifoif.g_wr_ack <= 1'b1;
			 	// fifoif.g_overflow <= 0;

			 end
			 else if (fifoif.wr_en) begin
			 	 fifoif.g_wr_ack <= 1'b0;
				 if(fifoif.g_full) begin
				 	fifoif.g_overflow <= 1;
				 end
				 else begin
				 	fifoif.g_overflow <= 0;
				 end	 
			end
		end
	end


	always_ff @(posedge fifoif.clk or negedge fifoif.rst_n) begin : read_proc		//read process logic
		if(~fifoif.rst_n) begin
			 rd_ptr<= 0;
		end else if (fifoif.rd_en && count > 0) begin
			fifoif.g_data_out <= mem[rd_ptr];
			rd_ptr <= rd_ptr + 1;
			// fifoif.g_underflow <= 0;

		end
		else if (fifoif.rd_en) begin
				if(fifoif.g_empty) begin
					fifoif.g_underflow <= 1;
			 	end
			 	else begin
					fifoif.g_underflow <= 0;
			 	end	 
		end
	end


	always_ff @(posedge fifoif.clk or negedge fifoif.rst_n) begin : count_proc	//count process logic
		if(~fifoif.rst_n) begin
			 count <= 0;
		end else begin
			 if (({fifoif.rd_en, fifoif.wr_en} == 2'b01) && ~fifoif.g_full) begin
			 	count <= count + 1;
			 end
			 if (({fifoif.rd_en, fifoif.wr_en} == 2'b10) && ~fifoif.g_empty) begin
			 	count <= count - 1;
			 end
		end
	end


	assign fifoif.g_full = (count == fifoif.FIFO_DEPTH);
	assign fifoif.g_almostfull = (count == fifoif.FIFO_DEPTH-1);

	assign fifoif.g_empty = (count == 0);
	assign fifoif.g_almostempty = (count == 1);





// bit [FIFO_WIDTH-1:0] g_data_out;
// 	bit g_wr_ack, g_overflow;
// 	bit g_full, g_empty, g_almostfull, g_almostempty, g_underflow;





endmodule : FIFO_golden_model