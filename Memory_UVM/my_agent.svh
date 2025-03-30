class my_agent extends uvm_agent;

	`uvm_component_utils(my_agent)

	virtual intf vif;

	my_sequencer 	sequencer_inst0;
	my_driver 		driver_inst0;
	my_monitor		monitor_inst0;

	uvm_analysis_port #(my_sequence_item) my_analysis_port;


	function new(string name = "my_agent", uvm_component parent = null);
		super.new(name, parent);

	endfunction

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		$display("my_agent::build phase started");
		sequencer_inst0 = my_sequencer::type_id::create("sequencer_inst0", this);
		driver_inst0 	= my_driver::type_id::create("driver_inst0", this);
		monitor_inst0 	= my_monitor::type_id::create("monitor_inst0", this);

		my_analysis_port = new("my_analysis_port", this);

		if (!uvm_config_db#(virtual intf)::get(this, "", "vif", vif)) begin
			`uvm_fatal(get_full_name(), "could not get vif")
		end

		uvm_config_db#(virtual intf)::set(this, "driver_inst0", "vif", vif);
		uvm_config_db#(virtual intf)::set(this, "monitor_inst0", "vif", vif);


	endfunction

	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		$display("my_agent::connect phase started");
		driver_inst0.seq_item_port.connect(sequencer_inst0.seq_item_export);
		monitor_inst0.my_analysis_port.connect(this.my_analysis_port);
	endfunction
	
endclass : my_agent