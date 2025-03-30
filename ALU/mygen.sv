class mygen;

	int no_packets;
	mytrans trans;
	mailbox gen2driv;




	function new(mailbox gen2driv);
		this.gen2driv = gen2driv;
	endfunction



	task main();
		repeat(no_packets) begin
			trans = new();
			if (!trans.randomize()) begin
				$fatal("GENERATOR::Randomization failed");
			end
			trans.display_ips("GENERATOR");
			gen2driv.put(trans);
	end
	endtask : main


	
endclass : mygen
