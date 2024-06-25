module SVA (counter_if.SVA counterif);

	property load_active_p;
		@(posedge counterif.clk) disable iff (!counterif.rst_n) (!counterif.load_n) |=> (counterif.count_out == $past(counterif.data_load));
	endproperty

	property load_inactive_1;
		@(posedge counterif.clk) disable iff(!counterif.rst_n) (counterif.load_n && !counterif.ce) |=> (counterif.count_out == $past(counterif.count_out));
	endproperty


	property load_inactive_2;
		@(posedge counterif.clk) disable iff (!counterif.rst_n) (counterif.load_n && counterif.ce && counterif.up_down) |=> (counterif.count_out |=> $past(counterif.count_out) + 1); 
	endproperty 

	property load_inactive_3;
		@(posedge counterif.clk) disable iff (!counterif.rst_n) (counterif.load_n && counterif.ce && !counterif.up_down) |=> (counterif.count_out == ($past(counterif.count_out) - 1));
	endproperty

	data_load_assertion: assert property(load_active_p);
	data_load_inactive_1_assertion: assert property(load_inactive_1);
	data_load_inactive_2_assertion: assert property(load_inactive_2);
	data_load_inactive_3_assertion: assert property(load_inactive_3);


	data_load_cover: cover property(load_active_p);
	data_load_inactive_1_cover: cover property(load_inactive_1);
	data_load_inactive_2_cover: cover property(load_inactive_2);
	data_load_inactive_3_cover: cover property(load_inactive_3);

	

	always @(*) begin
		if (!counterif.rst_n) begin
			reset_assertion: assert final(!counterif.rst_n == 0); 
		end

		if (counterif.count_out == 0) begin
			zero_assertion: assert(counterif.zero == 1);
		end

		if (counterif.count_out == {counterif.WIDTH{1'b1}}) begin
			max_count_assertion: assert(counterif.max_count == 1);
		end
	end 




endmodule : SVA