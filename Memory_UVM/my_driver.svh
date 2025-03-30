class my_driver extends uvm_driver #(my_sequence_item);

	`uvm_component_utils(my_driver)

	virtual intf vif;
	my_sequence_item seq_item_inst0;

	function new(string name = "my_driver", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		$display("my_driver::build_phase");
		seq_item_inst0 = my_sequence_item::type_id::create("seq_item_inst0");
		if (!uvm_config_db#(virtual intf)::get(this, "", "vif", vif)) begin
			`uvm_fatal(get_full_name(), "could not get vif")
		end
	endfunction

	virtual task run_phase(uvm_phase phase);
		super.run_phase(phase);
		$display("my_driver::run_phase");
		forever begin
		// repeat(100) begin
			// my_sequence_item seq_item_inst0;
			`uvm_info("my_driver", $sformatf("Wait for item from sequencer"), UVM_LOW)
			seq_item_port.get_next_item(seq_item_inst0);
			// @(posedge vif.i_clk)
			drive_item(seq_item_inst0);

			// @(posedge vif.i_clk)
			// seq_item_port.item_done();
			#1step seq_item_port.item_done();
			$display("%0t::DRIVER::i_rst_n = %h, i_EN = %h, i_address = %h, i_data_in = %h", $time(), seq_item_inst0.i_rst_n, seq_item_inst0.i_EN, seq_item_inst0.i_address, seq_item_inst0.i_data_in);


		end
	endtask

	virtual task drive_item(my_sequence_item seq_item_inst0);
		@(posedge vif.i_clk)
		vif.i_rst_n 	<= seq_item_inst0.i_rst_n;
		vif.i_address 	<= seq_item_inst0.i_address;
		vif.i_EN 		<= seq_item_inst0.i_EN;
		// if (seq_item_inst0.i_EN) begin
			vif.i_data_in 	<= seq_item_inst0.i_data_in;
			@(posedge vif.i_clk);
		// end
		// else begin
			// @(posedge vif.i_clk)
			// seq_item_inst0.i_EN <= 1;
			// @(negedge vif.i_clk)
			// seq_item_inst0.o_data_out 	<= vif.o_data_out;
			// seq_item_inst0.o_valid 		<= vif.o_valid;

		// end

	endtask
	
endclass : my_driver