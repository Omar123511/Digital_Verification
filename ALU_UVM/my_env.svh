class my_env extends uvm_env;

	`uvm_component_utils(my_env)

	my_agent agt;
	my_scoreboard scb;
	my_coverage_collector cov;

	virtual alu_if intf;

	function new(string name = "my_env", uvm_component parent = null);
		super.new(name, parent);
	endfunction


	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		agt = my_agent::type_id::create("agt", this);
		scb = my_scoreboard::type_id::create("scb", this);
		cov = my_coverage_collector::type_id::create("cov", this);

		if (!uvm_config_db#(virtual interface alu_if)::get(this, "", "my_vif", intf)) begin
			`uvm_fatal(get_full_name(), "ERROR FETCHING my_vif!")
		end
		uvm_config_db#(virtual interface alu_if)::set(this, "agt", "my_vif", intf);



	endfunction

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);


		agt.mon.m_analysis_port.connect(scb.m_analysis_imp);
		agt.mon.m_analysis_port.connect(cov.analysis_export);
	endfunction

	
endclass : my_env