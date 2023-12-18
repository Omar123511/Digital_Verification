package mypkg;

	class counter_c;

		parameter WIDTH = 4;

		rand bit clk;
		rand bit rst_n;
		rand bit load_n;
		rand bit up_down;
		rand bit ce;
		rand bit [WIDTH-1:0] data_load;
		// bit [WIDTH-1:0] data_load;
		bit [WIDTH-1:0] count_out;
		bit max_count;
		bit zero;


		constraint c {

			rst_n dist {1 := 98, 0 := 2};
			load_n dist {1 := 30, 0 := 70};
			ce dist {1 := 70, 0 := 30};
		}

		constraint c_up_down {
			up_down dist {1 := 50, 0 := 50};
			// (up_down == 1) -> data_load <= 7;
			// (up_down == 0) -> data_load <= 0;
		}

		constraint c_ce {
			ce dist {1 := 50, 0 := 50};
		}

		constraint c_data_load {
			
			unique {data_load};
		}

		covergroup cg;
			load_data_cp : coverpoint load_n{
				bins active = {1};
				// ignore_bins inactive = {0};
				option.weight = 0;
			}

			data_load_cp : coverpoint data_load{
				option.weight = 0;
			}

			load_cross : cross data_load_cp, load_data_cp{

				ignore_bins ig_load_high = binsof(load_data_cp) intersect {1};

			}


			count_out_cp_1 : coverpoint count_out iff (rst_n && ce && up_down);

			count_out_cp_2 : coverpoint count_out iff (rst_n && ce && up_down){
				bins count_out_trans_zero = ({WIDTH{1'b1}} => 0);				

			}

			count_out_cp_3 : coverpoint count_out iff (rst_n && ce && ~up_down);
			
			count_out_cp_4 : coverpoint count_out iff (rst_n && ce && ~up_down){
				bins count_out_trans_max = (0 => {WIDTH{1'b1}});				

			}





			
		endgroup : cg

		function new();
			cg = new();
		endfunction


	endclass : counter_c
	
endpackage : mypkg
