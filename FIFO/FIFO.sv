////////////////////////////////////////////////////////////////////////////////
// Author: Kareem Waseem
// Course: Digital Verification using SV & UVM
//
// Description: FIFO Design 
// 
////////////////////////////////////////////////////////////////////////////////
// module FIFO(data_in, wr_en, rd_en, clk, rst_n, full, empty, almostfull, almostempty, wr_ack, overflow, underflow, data_out);
// parameter FIFO_WIDTH = 16;
// parameter FIFO_DEPTH = 8;
// input [FIFO_WIDTH-1:0] data_in;
// input clk, rst_n, wr_en, rd_en;
// output reg [FIFO_WIDTH-1:0] data_out;
// output reg wr_ack, overflow;
// output full, empty, almostfull, almostempty, underflow;

module FIFO(fifo_interface.DUT fifoif);

 
localparam max_fifo_addr = $clog2(fifoif.FIFO_DEPTH);

reg [fifoif.FIFO_WIDTH-1:0] mem [fifoif.FIFO_DEPTH-1:0];

reg [max_fifo_addr-1:0] wr_ptr, rd_ptr;
reg [max_fifo_addr:0] count;

always @(posedge fifoif.clk or negedge fifoif.rst_n) begin
	if (!fifoif.rst_n) begin
		wr_ptr <= 0;
	end
	else if (fifoif.wr_en && count < fifoif.FIFO_DEPTH) begin
		mem[wr_ptr] <= fifoif.data_in;
		fifoif.wr_ack <= 1;
		wr_ptr <= wr_ptr + 1;
	end
	else begin 
		fifoif.wr_ack <= 0; 
		if (fifoif.wr_en)
			fifoif.overflow <= 1;
		else
			fifoif.overflow <= 0;
	end
end

always @(posedge fifoif.clk or negedge fifoif.rst_n) begin
	if (!fifoif.rst_n) begin
		rd_ptr <= 0;
	end
	else if (fifoif.rd_en && count != 0) begin
		fifoif.data_out <= mem[rd_ptr];
		rd_ptr <= rd_ptr + 1;
	end
end

always @(posedge fifoif.clk or negedge fifoif.rst_n) begin
	if (!fifoif.rst_n) begin
		count <= 0;
	end
	else begin
		if	( ({fifoif.wr_en, fifoif.rd_en} == 2'b10) && !fifoif.full) 
			count <= count + 1;
		else if ( ({fifoif.wr_en, fifoif.rd_en} == 2'b01) && !fifoif.empty)
			count <= count - 1;
	end
end

assign fifoif.full = (count == fifoif.FIFO_DEPTH)? 1 : 0;
assign fifoif.empty = (count == 0)? 1 : 0;
assign fifoif.underflow = (fifoif.empty && fifoif.rd_en)? 1 : 0; 
assign fifoif.almostfull = (count == fifoif.FIFO_DEPTH-2)? 1 : 0; 
assign fifoif.almostempty = (count == 1)? 1 : 0;



`ifdef SIM
	property p_wr_ack;
		@(posedge fifoif.clk) disable iff(~fifoif.rst_n) (fifoif.wr_en && count < fifoif.FIFO_DEPTH) |=> fifoif.wr_ack;
	endproperty
	a1 : assert property(p_wr_ack);
	c1 : cover property(p_wr_ack);

	property p_overflow;
		@(posedge fifoif.clk) disable iff(~fifoif.rst_n) (fifoif.full && fifoif.wr_en) |=> fifoif.overflow; 
	endproperty
	a2 : assert property(p_overflow);
	c2 : cover property(p_overflow);

	property p_full;
		@(posedge fifoif.clk) disable iff(~fifoif.clk) (count == fifoif.FIFO_DEPTH) |-> fifoif.full;
	endproperty
	a3 : assert property(p_full);
	c3 : cover property(p_full);

	property p_empty;
		@(posedge fifoif.clk) disable iff(~fifoif.rst_n) (count == 0) |-> fifoif.empty;
	endproperty
	a4 : assert property(p_empty);
	c4 : cover property(p_empty);

	property p_almostfull;
		@(posedge fifoif.clk) disable iff(~fifoif.rst_n) (count == fifoif.FIFO_DEPTH-1) |-> fifoif.almostfull;
	endproperty
	a5 : assert property(p_almostfull);
	c5 : cover property(p_almostfull);

	property p_almostempty;
		@(posedge fifoif.clk) disable iff(~fifoif.rst_n) (count == 1) |-> fifoif.almostempty;
	endproperty
	a6 : assert property(p_almostempty);
	c6 : cover property(p_almostempty);

	property p_underflow;
		@(posedge fifoif.clk) disable iff(~fifoif.rst_n) (fifoif.empty && fifoif.rd_en) |=> fifoif.underflow;
	endproperty
	a7 : assert property(p_underflow);
	c7 : cover property(p_underflow);

	property p_count_wr_en;
		@(posedge fifoif.clk) disable iff(~fifoif.rst_n) (({fifoif.wr_en, fifoif.rd_en} == 2'b10) && ~fifoif.full) |=> count == ($past(count) + 1);	//could have syntax error
	endproperty
	a8 : assert property(p_count_wr_en);
	c8 : cover property(p_count_wr_en);

	property p_count_rd_en;
		@(posedge fifoif.clk) disable iff(~fifoif.rst_n) (({fifoif.wr_en, fifoif.rd_en} == 2'b01) && ~fifoif.empty) |=> (count == $past(count) - 1);	//could have syntax error
	endproperty
	a9 : assert property(p_count_rd_en);
	c9 : cover property(p_count_rd_en);
`endif






endmodule