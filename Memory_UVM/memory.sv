module memory (intf.DUT memif);


	// reg [3:0] r_counter;
	logic [31 : 0] l_arr [16];

	always_ff @(posedge memif.i_clk or negedge memif.i_rst_n) begin : proc_o_data_out
		if(~memif.i_rst_n) begin
			memif.o_data_out <= 0;
			memif.o_valid <= 0;
		end else begin
			if (memif.i_EN) begin
				l_arr[memif.i_address] <= memif.i_data_in;
				memif.o_valid <= 0;
			end
			else begin
				memif.o_data_out <= l_arr[memif.i_address];
				memif.o_valid <= 1;

			end
		end
	end


	// assign o_valid = (i_EN)? 1'b0 : 1'b1;

endmodule : memory