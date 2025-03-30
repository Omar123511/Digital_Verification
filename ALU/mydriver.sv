class mydriver;

	mailbox gen2driv;

	virtual intf vif;

  int no_transactions;



	function new(virtual intf vif, mailbox gen2driv);
		this.vif = vif;
		this.gen2driv = gen2driv;
	endfunction



	task reset();
		wait(!vif.rst_n);
		$display("---------------[DRIVER-RESET-STARTED]---------------");
		vif.ALU_en <= 0;
		vif.a_en <= 0;
		vif.b_en <= 0;
		vif.a_op <= 0;
		vif.b_op <= 0;
		vif.A <= 0;
		vif.B <= 0;
		wait(vif.rst_n);
		$display("---------------[DRIVER-RESET-FINISHED]---------------");
	endtask : reset

	task main();
		forever begin
			mytrans trans;
			gen2driv.get(trans);
			@(posedge vif.clk);
			vif.ALU_en <= 1'b1;
			vif.a_en <= trans.a_en;
			vif.b_en <= trans.b_en;
			vif.a_op <= trans.a_op;
			vif.b_op <= trans.b_op;
			vif.A <= trans.A;
			vif.B <= trans.B;
			@(posedge vif.clk);
			trans.C = vif.C;
			vif.ALU_en <= 1'b0;
			@(posedge vif.clk);
			
			trans.display("DRIVER");
			no_transactions++;	
		end
	endtask : main





	
endclass : mydriver
