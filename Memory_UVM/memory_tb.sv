module memory_tb (intf.TB memif);

	// memory memory_inst0 (.*);

	initial begin
		memif.i_clk = 1;
		forever begin
			#1 memif.i_clk = ~memif.i_clk;
		end
	end


	initial begin
		memif.i_rst_n = 0;
		memif.i_EN = 0;
		memif.i_address = 0;
		memif.i_data_in = 0;	#10

		memif.i_rst_n = 1;
		memif.i_EN = 1;
		memif.i_address = 1;
		memif.i_data_in = 1;	#10

		memif.i_EN = 1;
		memif.i_address = 2;
		memif.i_data_in = 2;	#10

		memif.i_EN = 0;
		memif.i_address = 1;
		memif.i_data_in = 5;	#10

		$stop;



	end






endmodule : memory_tb