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

			seq_item_inst0.i_rst_n	 			<= vif.i_rst_n;
			seq_item_inst0.i_EN 				<= vif.i_EN;
			seq_item_inst0.i_address 			<= vif.i_address;
			seq_item_inst0.i_data_in 			<= vif.i_data_in;
			// @(posedge vif.i_clk);	//new

			@(negedge vif.i_clk)
			// if (!vif.i_EN) begin
				seq_item_inst0.o_data_out 			<= vif.o_data_out;
				seq_item_inst0.o_valid 				<= vif.o_valid;
				// @(negedge vif.i_clk);	//new

			// end


			#1step my_analysis_port.write(seq_item_inst0);
			// my_analysis_port.write(seq_item_inst0);


			$display("%0t::MONITOR::i_rst_n = %h, i_EN = %h, i_address = %h, i_data_in = %h", $time(), seq_item_inst0.i_rst_n, seq_item_inst0.i_EN, seq_item_inst0.i_address, seq_item_inst0.i_data_in);
			$display("%0t::MONITOR::o_data_out = %h, o_valid = %h", $time(), seq_item_inst0.o_data_out, seq_item_inst0.o_valid);
		end

		
	endtask : run_phase



endclass : my_monitor