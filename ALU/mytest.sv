program mytest(intf intf);

	myenv cl_env;

	initial begin
		cl_env = new(intf);

		cl_env.cl_gen.no_packets = 4000;

		cl_env.main();
	end


	final begin
		$display("----------------------------------------------------");
		$display("-[FINAL]-");
		$display("Correct_Count = %d, Error_Count = %d", cl_env.cl_scb.correct_count, cl_env.cl_scb.error_count); 
		$display("no_trans = %0d",cl_env.cl_driv.no_transactions);
		$display("Functional_Coverage = %f", cl_env.cl_cov.cg.get_coverage());	
		$display("----------------------------------------------------");

	end


endprogram : mytest
