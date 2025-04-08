class ALU_driver extends uvm_driver #(ALU_sequence_item);

	`uvm_component_utils(ALU_driver)

	ALU_sequence_item req_clone;


	function new(string name = "ALU_driver", uvm_component parent = null);
		super.new(name, parent);
	endfunction



	virtual alu_if intf;


	function void build_phase(uvm_phase phase);
		super.build_phase(phase);		
		if (!uvm_config_db#(virtual interface alu_if)::get(this, "", "my_vif", intf))
			`uvm_fatal(get_full_name(), "ERROR FETCHING my_vif")
		req_clone = ALU_sequence_item::type_id::create("req_clone");
	endfunction


	task run_phase(uvm_phase phase);
		super.run_phase(phase);
		forever begin
			seq_item_port.get_next_item(req);
			drive();
			seq_item_port.item_done();		
		end
	endtask


	virtual task drive;
		req_clone = req;
		@(posedge intf.clk); 				
		`uvm_info(get_full_name(), $sformatf("Sample Inputs"), UVM_LOW)
		intf.ALU_en <= 1;
		intf.a_en <= req.a_en;
		intf.b_en <= req.b_en;
		intf.a_op <= req.a_op;
		intf.b_op <= req.b_op;
		intf.A <= req.A;
		intf.B <= req.B;
		
		@(posedge intf.clk); 				
		intf.ALU_en <= 0;
		req.C = intf.C;
		@(posedge intf.clk);

	endtask
	
endclass : ALU_driver