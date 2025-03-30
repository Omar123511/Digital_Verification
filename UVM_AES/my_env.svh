class my_env extends uvm_env;

	`uvm_component_utils(my_env)

	my_scoreboard 	scb_inst0;
	my_subscriber 	sub_inst0;
	my_agent 		agent_inst0;

	virtual intf vif;

	function new(string name = "my_env", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		$display("my_env::build phase started");
		scb_inst0 	= my_scoreboard::type_id::create("scb_inst0", this);
		sub_inst0 	= my_subscriber::type_id::create("sub_inst0", this);
		agent_inst0 = my_agent::type_id::create("agent_inst0", this);

		if (!uvm_config_db#(virtual intf)::get(this, "", "vif", vif)) begin
			`uvm_fatal(get_full_name(), "could not get vif")
		end

		uvm_config_db#(virtual intf)::set(this, "scb_inst0", "vif", vif);
		uvm_config_db#(virtual intf)::set(this, "sub_inst0", "vif", vif);
		uvm_config_db#(virtual intf)::set(this, "agent_inst0", "vif", vif);

	endfunction

	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		$display("my_env::connect phase started");
		agent_inst0.my_analysis_port.connect(scb_inst0.my_analysis_imp);
		agent_inst0.my_analysis_port.connect(sub_inst0.analysis_export);

	endfunction
	
endclass : my_env