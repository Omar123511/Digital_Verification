module counter_sva (counter_if.DUT c_if);

	always_comb begin 		//This is taken place because the reset in this design is asynchronous
		if (~c_if.rst_n) begin
			assert_reset : assert final (c_if.count_out == 0);
		end

		if (c_if.count_out == 0) begin
			assert_zero : assert (c_if.zero == 1);
		end

		if (c_if.count_out == {c_if.WIDTH{1'b1}}) begin
			assert_max_count : assert (c_if.max_count ==1);
		end
	end



	property load_p;
		@(posedge c_if.clk) disable iff(!c_if.rst_n) (!c_if.load_n) |=> (c_if.count_out == $past(c_if.data_load));
		// @(posedge c_if.clk) (!c_if.rst_n && !c_if.load_n) |=> (c_if.count_out == $past(c_if.data_load));

	endproperty

	property load_n_p;
		@(posedge c_if.clk) disable iff(~c_if.rst_n) (c_if.load_n && ~c_if.ce) |=> (c_if.count_out == $past(c_if.count_out));
	endproperty

	property int_cnt_p;
		@(posedge c_if.clk) disable iff(~c_if.rst_n) (c_if.load_n && c_if.ce && c_if.up_down) |=> (c_if.count_out == ($past(c_if.count_out) + 1)); 
	endproperty

	property dec_cnt_p;
		@(posedge c_if.clk) disable iff(~c_if.rst_n) (c_if.load_n && c_if.ce && ~c_if.up_down) |=> (c_if.count_out == ($past(c_if.count_out) - 1)); 

	endproperty


		assert_load_p : assert property (load_p) begin
			$display("time: %0t : count_out = %d, past_data_load = %d", $time(), c_if.count_out, $past(c_if.data_load));
		end;
		assert_load_n_p : assert property (load_n_p);
		assert_int_cnt_p : assert property (int_cnt_p);
		assert_dec_cnt_p : assert property (dec_cnt_p);


		cover_load_p : cover property (load_p);
		cover_load_n_p : cover property (load_n_p);
		cover_int_cnt_p : cover property (int_cnt_p);
		cover_dec_cnt_p : cover property (dec_cnt_p);



endmodule : counter_sva 