class my_agent extends uvm_agent;

	`uvm_component_utils(my_agent)

	my_sequencer sqr;
	my_driver driv;
	my_monitor mon;

	virtual alu_if intf;

	function new(string name = "my_agent", uvm_component parent = null);
		super.new(name, parent);
	endfunction



	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		sqr = my_sequencer::type_id::create("sqr", this);
		driv = my_driver::type_id::create("driv", this);
		mon = my_monitor::type_id::create("mon", this);

		if (!uvm_config_db#(virtual interface alu_if)::get(this, "", "my_vif", intf)) begin
			`uvm_fatal(get_full_name(), "ERROR FETCHING my_vif")
		end

		uvm_config_db#(virtual interface alu_if)::set(this, "*", "my_vif", intf);


	endfunction

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		driv.seq_item_port.connect(sqr.seq_item_export);
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
	endtask
	
endclass : my_agent