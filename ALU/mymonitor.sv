class mymonitor;
	
	mailbox mon2scb, mon2collector;
	virtual intf vif;

	function new(virtual intf vif, mailbox mon2scb, mon2collector);
		this.vif = vif;
		this.mon2scb = mon2scb;
		this.mon2collector = mon2collector;
	endfunction


	task main();
		forever begin
			mytrans trans = new();
			@(posedge vif.clk iff vif.ALU_en);
			
			trans.a_en = vif.a_en;
			trans.b_en = vif.b_en;
			trans.a_op = vif.a_op;
			trans.b_op = vif.b_op;
			trans.A = vif.A;
			trans.B = vif.B;
			@(posedge vif.clk);
			trans.C = vif.C;
			@(posedge vif.clk);
			mon2scb.put(trans);
			mon2collector.put(trans);
			trans.display("MONITOR");
		end
		
	endtask : main

	
endclass : mymonitor
