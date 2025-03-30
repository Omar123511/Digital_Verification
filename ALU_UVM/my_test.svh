class my_test extends uvm_test;

	`uvm_component_utils(my_test)

	my_env env;

	my_sequence seq;

	my_cfg cfg;

	virtual alu_if intf;

	function new(string name = "my_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction



	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
        env = my_env::type_id::create("env", this);
        cfg = my_cfg::type_id::create("cfg");
        
        cfg.item_count = 1000;
        cfg.item_count_a_op = 2000;
        cfg.item_count_b_op_1 = 1000;
        cfg.item_count_b_op_2 = 1000;

        cfg.item_count_sum =  cfg.item_count_a_op + cfg.item_count_b_op_1 + cfg.item_count_b_op_2 + cfg.item_count;
       

        if (!uvm_config_db#(virtual interface alu_if)::get(this, "", "my_vif", intf)) begin
        	`uvm_fatal(get_full_name(), "ERROR FETCHING my_vif!")
        end

        uvm_config_db #(virtual interface alu_if)::set(this, "env", "my_vif", intf);
        uvm_config_db #(my_cfg)::set(null, "*", "my_cfg", cfg);

        seq = my_sequence::type_id::create("seq");

	endfunction


	task run_phase(uvm_phase phase);
		super.run_phase(phase);
		phase.raise_objection(this);
		seq.start(env.agt.sqr);
		cfg.count_sum =  cfg.count_a_op + cfg.count_b_op_1 + cfg.count_b_op_2 + cfg.count;
		phase.drop_objection(this);

	endtask

	bit done;
	function void phase_ready_to_end(uvm_phase phase);
		if (phase.is(uvm_run_phase::get)) begin
			if (done != 1) begin 	//replace 4 with config obj
				phase.raise_objection(this, "Test not ready yet");
				fork
				    `uvm_info("PRTESTING", "Phase Ready Testing", UVM_LOW);
					wait_for_ready_to_finish();
					phase.drop_objection(this, "Test ready to end");
				join_none
			end
		end
	endfunction : phase_ready_to_end
 
	task wait_for_ready_to_finish();
	
		`uvm_info(get_full_name(), $sformatf("cfg.cov_items = %0d", cfg.cov_items), UVM_LOW);
		wait(cfg.item_count_sum == cfg.count_sum);
		wait(cfg.item_count_sum == cfg.cov_items);
	
		done = 1;
	
		`uvm_info(get_full_name(), $sformatf("cfg.item_count_sum = %0d", cfg.item_count_sum), UVM_LOW);
		`uvm_info(get_full_name(), $sformatf("cfg.count_sum = %0d", cfg.count_sum), UVM_LOW);

		`uvm_info(get_full_name(), $sformatf("cfg.correct_count = %0d, cfg.error_count = %0d", cfg.correct_count, cfg.error_count), UVM_LOW);

	endtask: wait_for_ready_to_finish


	
endclass : my_test
