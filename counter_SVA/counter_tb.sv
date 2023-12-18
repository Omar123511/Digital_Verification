import mypkg::*;


module counter_tb (counter_if.TEST counterif);
// module counter_tb;

	// localparam WIDTH = 4;

    // bit clk;
    // bit rst_n;
    // bit load_n;
    // bit up_down;
    // bit ce;
    // bit [WIDTH-1:0] data_load;
	// bit [WIDTH-1:0] count_out;
	// bit max_count;
	// bit zero;

	// counter_if c_if(counterif.clk);

	// counter DUT (c_if.DUT);

	// bind counter counter_sva countersva(c_if);

	bit [counterif.WIDTH-1:0] count_out_exp;
	bit max_count_exp;
	bit zero_exp;

	int correct_count, error_count;


	// initial begin
	// 	counterif.clk = 0;
	// 	forever begin
	// 		#1 counterif.clk = ~counterif.clk;
	// 	end
	// end


	counter_c ob1 = new;


	initial begin
		assert_reset;	
		// rst_n = 1; load_n = 1; up_down = 1; ce = 0; data_load = 0; count_out_exp = 0; max_count_exp = 0; zero_exp = 1;
		repeat(500) begin
			@(posedge counterif.clk);
			assert(ob1.randomize);
			counterif.rst_n = ob1.rst_n;
			counterif.load_n = ob1.load_n;
			counterif.up_down = ob1.up_down;
			counterif.ce = ob1.ce;
			counterif.data_load = ob1.data_load;
			// check_result;
			ob1.count_out = counterif.count_out;
			ob1.cg.sample();
		end

		$display("correct_count = %0d, error_count = %0d", correct_count, error_count);

		// #500 $stop;
		$stop;
	end

	task check_result;
		golden_model;
		if (counterif.rst_n) begin
			@(negedge counterif.clk);
			if (counterif.count_out !== count_out_exp || counterif.zero !== zero_exp || counterif.max_count !== max_count_exp) begin
				$display("%0t : fail @ (count_out, count_out_exp) = (%0d, %0d), (zero, zero_exp) = (%0b, %0b), (max_count, max_count_exp) = (%0b, %0b)", $time(), counterif.count_out, count_out_exp, counterif.zero, zero_exp, counterif.max_count, max_count_exp);
				error_count = error_count + 1;
			end

			else begin
				$display("%0t : Pass test: (count_out, count_out_exp) = (%0d, %0d), data_load = %0d, load_n = %0b", $time(), counterif.count_out, count_out_exp, counterif.data_load, counterif.load_n);
				correct_count = correct_count + 1;
			end



		end
		
	endtask : check_result





	task golden_model();

		// @(posedge counterif.clk or negedge counterif.rst_n);
		// if (~rst_n || count_out === {WIDTH{1'b1}} || count_out === 0) begin
		if (~counterif.rst_n) begin
			count_out_exp = 0;
			// if (count_out === {WIDTH{1'b1}}) begin
			//  	max_count_exp <= 1;
			//  end
			//  else if(count_out === 0) begin
			//  	zero_exp <= 1;
			//  end
			//  else begin
			//  	max_count_exp <= 0; zero_exp <= 0;
			//  end 
		end

		else if (~counterif.load_n) begin
			count_out_exp = counterif.data_load;
		end

		// else begin
		else if (counterif.ce) begin
			if (counterif.up_down) begin
				count_out_exp = count_out_exp + 1;
			end
			else begin
				count_out_exp = count_out_exp - 1;
			end
		end
		// end

		max_count_exp = (count_out_exp === {counterif.WIDTH{1'b1}})? 1 : 0;
		zero_exp = (count_out_exp === 0)? 1 : 0;


		
	endtask : golden_model

	task assert_reset;
		counterif.rst_n = 0;
		check_reset;
		counterif.rst_n =1;
		
	endtask : assert_reset

	task check_reset;
		@(negedge counterif.clk);
		if (counterif.count_out === 0 && counterif.max_count === 0 && counterif.zero === 1) begin
			$display("reset check pass");
		    correct_count = correct_count + 1; 
		end
		else begin
			$display("reset failed");
			error_count = error_count + 1;
		end
		
	endtask : check_reset


endmodule : counter_tb