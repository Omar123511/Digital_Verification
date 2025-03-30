class myenv;

	mailbox gen2driv, mon2scb, mon2collector;


	mygen cl_gen;
	mydriver cl_driv;
	mymonitor cl_mon;
	myscb cl_scb;
	mycov cl_cov;

	virtual intf vif;


	function new(virtual intf vif);

		this.vif = vif;

		gen2driv = new();
		mon2scb = new();
		mon2collector = new();

		cl_gen = new(gen2driv);
		cl_driv = new(vif, gen2driv);
		cl_mon = new(vif, mon2scb, mon2collector);
		cl_scb = new(mon2scb);
		cl_cov = new(mon2collector);

	endfunction

	task pre_run();
		cl_driv.reset();
	endtask : pre_run

	task run();
		fork
			cl_gen.main();
			cl_driv.main();
			cl_mon.main();
			cl_scb.main();
			cl_cov.main();
		join_none
		
	endtask : run

 	task post_run();
    		wait(cl_gen.no_packets == cl_scb.no_transactions); 			// to ensure no packet is lost when sent to scoreboard
  	endtask 


	task main();
		pre_run();
		run();
		post_run();

		$finish;

	endtask : main
endclass : myenv
