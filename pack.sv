package pack;

	class counter_c;

		parameter WIDTH = 4;
		parameter MAX = {WIDTH{1'b1}};
		parameter ZERO = 0;

		logic clk;
		rand logic rst_n;
		rand logic load_n;
		rand logic up_down;
		rand logic ce;
		rand logic [WIDTH-1:0] data_load;
		logic [WIDTH-1:0] count_out;
		logic max_count;
		logic zero;

		// parameter WIDTH


		constraint zero_constr {
			rst_n dist {0 := 20, 1 := 80};
		}

		constraint load_n_constr {
			load_n dist {0 := 60, 1 := 40};
		} 

		
		constraint up_down_constr {
			up_down dist {1 := 70, 0 := 30}; 
		}

		constraint ce_constr {
			ce dist {0 := 30, 1 := 70};
		}


		covergroup cg;
			data_load_cp : coverpoint data_load iff (~load_n);

			count_out_up_cp : coverpoint count_out iff (rst_n && ce && up_down);

			count_out_up_overflow_cp : coverpoint count_out iff(rst_n && ce && up_down)
			{
				bins overflow_b = (MAX => ZERO);
			}

			count_out_down_cp : coverpoint count_out iff(rst_n && ce && ~up_down);

			count_out_down_underflow_cp : coverpoint count_out iff(rst_n && ce && ~up_down)
			{
				bins underflow_b = (ZERO => MAX);
			}


		endgroup

		function new;
			cg = new();
		endfunction


		



	endclass

	
	
endpackage : pack