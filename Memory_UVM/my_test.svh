class my_test extends uvm_test;

	`uvm_component_utils(my_test)

	my_env 				env_inst0;
	my_sequence 		seq_inst0;

	virtual intf vif;

	function new(string name = "my_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		$display("my_test::build phase started");
		env_inst0 = my_env::type_id::create("env_inst0", this);
		seq_inst0 = my_sequence::type_id::create("seq_inst0");

		if (!uvm_config_db#(virtual intf)::get(this, "", "vif", vif)) begin
			`uvm_fatal(get_full_name(), "could not get vif");
		end

		uvm_config_db#(virtual intf)::set(this, "env_inst0", "vif", vif);
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
		$display("my_test::run phase started");
		phase.raise_objection(this);
		seq_inst0.start(env_inst0.agent_inst0.sequencer_inst0);

		phase.drop_objection(this);


	endtask : run_phase
	
endclass : my_test