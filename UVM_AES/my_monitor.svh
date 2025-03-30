class my_monitor extends uvm_monitor;

	`uvm_component_utils(my_monitor)

	virtual intf vif;
	my_sequence_item seq_item_inst0;

	uvm_analysis_port #(my_sequence_item) my_analysis_port;

	function new(string name = "my_monitor", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		$display("my_monitor::build_phase");
		if (!uvm_config_db#(virtual intf)::get(this, "", "vif", vif)) begin
			`uvm_fatal(get_full_name(), "could not get vif")
		end
		seq_item_inst0 = my_sequence_item::type_id::create("seq_item_inst0");
		my_analysis_port = new("my_analysis_port", this);
	endfunction

	virtual task run_phase(uvm_phase phase);
		super.run_phase(phase);
		$display("my_monitor::run_phase");
		forever begin
		// repeat(100) begin
			@(posedge vif.i_clk)
			@(posedge vif.i_clk)
			// @(posedge vif.i_clk)

			seq_item_inst0.in	 			<= vif.in;
			seq_item_inst0.key 				<= vif.key;
			$display("%0t::MONITOR::in = %h, key = %h", $time(), seq_item_inst0.in, seq_item_inst0.key);

			// @(posedge vif.i_clk);	//new

			@(negedge vif.i_clk)
			// @(posedge vif.i_clk)

			// if (!vif.i_EN) begin
				seq_item_inst0.out 				<= vif.out;
				$display("%0t::MONITOR::out = %h", $time(), seq_item_inst0.out);

				// @(negedge vif.i_clk);	//new
			// @(posedge vif.i_clk)

			// end


			#1step my_analysis_port.write(seq_item_inst0);
			// my_analysis_port.write(seq_item_inst0);


		end

		
	endtask : run_phase



endclass : my_monitor