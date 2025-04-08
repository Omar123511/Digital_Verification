class ALU_monitor extends uvm_monitor;

	uvm_analysis_port #(ALU_sequence_item) m_analysis_port;

	virtual alu_if intf;

	ALU_sequence_item req;

	`uvm_component_utils(ALU_monitor)

	function new(string name = "ALU_monitor", uvm_component parent = null);
		super.new(name, parent);
		m_analysis_port = new("m_analysis_port", this);
	endfunction


	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual alu_if)::get(this, "", "my_vif", intf)) begin
			`uvm_fatal(get_full_name(), "ERROR FETCHING my_vif")
		end
	endfunction
	

	virtual task run_phase(uvm_phase phase);
		super.run_phase(phase);
		forever begin
			req = ALU_sequence_item::type_id::create("ALU_sequence_item");
			@(posedge intf.clk iff intf.ALU_en); 					
			req.ALU_en = intf.ALU_en;
			req.a_en = intf.a_en;
			req.b_en = intf.b_en;
			req.a_op = intf.a_op;
			req.b_op = intf.b_op;
			req.A = intf.A;
			req.B = intf.B;

			@(posedge intf.clk); 						
			req.C = intf.C;
			m_analysis_port.write(req);
		end
	endtask : run_phase


endclass : ALU_monitor
