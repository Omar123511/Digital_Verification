import pack::*;
module counter_tb (counter_if.TB counterif);

	parameter TESTS = 100;
	int correct_count, error_count;

	logic [counterif.WIDTH-1:0] count_out_expected;
	logic max_count_expected;
	logic zero_expected;

	counter_c obj;

	initial begin
		error_count = 0;
		correct_count = 0;

		obj = new();

		repeat(TESTS) begin
			assert(obj.randomize());
			counterif.rst_n = obj.rst_n;
			counterif.load_n = obj.load_n;
			counterif.up_down = obj.up_down;
			counterif.ce = obj.ce;
			counterif.data_load = obj.data_load;

			@(negedge counterif.clk);
			obj.count_out = counterif.count_out;
			obj.max_count = obj.max_count;
			obj.zero = obj.zero;
			obj.cg.sample();

			golden_model;
			check_result(count_out_expected, max_count_expected, zero_expected);
		end

		$display("correct_count = %d, error_count = %d", correct_count, error_count);
		$stop;

	end



	task golden_model;
		fork
			begin
				if (~counterif.rst_n) begin
						count_out_expected = 0;
				end

				else begin
					if (~counterif.load_n) begin
							count_out_expected = counterif.data_load;
						end
					else if (counterif.ce) begin
						if (counterif.up_down) begin
							count_out_expected = count_out_expected + 1;
						end
						else begin
							count_out_expected = count_out_expected - 1;
						end
					end
				end
			end

			begin
				max_count_expected = (count_out_expected == {counterif.WIDTH{1'b1}})? 1 : 0;			
			end

			begin
				zero_expected = (count_out_expected == 0)? 1 : 0;

			end
		join
	endtask


	task check_result(logic [counterif.WIDTH - 1 : 0] count_out_expected, logic max_count_expected, zero_expected);
		if ({count_out_expected, max_count_expected, zero_expected} !== {counterif.count_out, counterif.max_count, counterif.zero}) begin
			$display("-------------------------------------------------------");
			$display("Error result");
			$display("count_out_expected = %d, count_out = %d", count_out_expected, counterif.count_out);
			$display("max_count_expected = %d, max_count = %d", max_count_expected, counterif.max_count);
			$display("zero_expected = %d, zero = %d", zero_expected, counterif.zero);
			$display("-------------------------------------------------------");
			error_count = error_count + 1;
				end	

		else begin
			$display("-------------------------------------------------------");
			$display("correct result");
			$display("count_out_expected = %d, count_out = %d", count_out_expected, counterif.count_out);
			$display("max_count_expected = %d, max_count = %d", max_count_expected, counterif.max_count);
			$display("zero_expected = %d, zero = %d", zero_expected, counterif.zero);
			$display("-------------------------------------------------------");
			correct_count = correct_count + 1;
		end	


	endtask



endmodule : counter_tb