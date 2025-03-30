class my_scoreboard extends uvm_scoreboard;

	`uvm_component_utils(my_scoreboard)

	virtual intf vif;
	my_sequence_item seq_item_inst0;

	int error_count, correct_count;

	int 	file_handle;
    string 	line;
    logic [127:0] out_expec;

    int result;


	uvm_analysis_imp #(my_sequence_item, my_scoreboard) my_analysis_imp;

	function new(string name = "my_scoreboard", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		$display("my_scoreboard::build_phase");
		seq_item_inst0 = my_sequence_item::type_id::create("seq_item_inst0");
		my_analysis_imp = new("my_analysis_imp", this);
	endfunction

	virtual function void write(my_sequence_item seq_item_inst0);	
		$display("my_scoreboard::check_result");
		$display("%0t::SCB::in = %h, key = %h", $time(), seq_item_inst0.in, seq_item_inst0.key);
		$display("%0t::SCB::out = %h", $time(), seq_item_inst0.out);

		file_handle = $fopen("input.txt","w");
		$fwrite(file_handle,"%h",seq_item_inst0.in);
		$fwrite(file_handle,"\n%h",seq_item_inst0.key);
		$fclose(file_handle);
	    result = $system("python AES.py input.txt output.txt");
	    if (result != 0) begin
			`uvm_fatal("PYTHON_ERROR", "Failed to run AES.py");
		end

	    file_handle = $fopen("output.txt", "r");

	    if (file_handle) begin
	    	if ($fgets(line, file_handle)) begin
		        $sscanf(line, "%h", out_expec);
				if ({out_expec} !== {seq_item_inst0.out}) begin
					$display("-------------------------------------------------------");
					$display("%0t::ERROR!", $time());
					$display("out_expec = %h, out = %h", out_expec, seq_item_inst0.out);
					$display("-------------------------------------------------------");
					error_count = error_count + 1;
	    		end
	    		else begin
	    			$display("-------------------------------------------------------");
					$display("%0t::PASS!", $time());
					$display("out_expec = %h, out = %h", out_expec, seq_item_inst0.out);
					$display("-------------------------------------------------------");
					correct_count = correct_count + 1;
	    		end
	    	end
		end

		$display("correct_count = %d, error_count = %d",correct_count, error_count);


	endfunction
endclass : my_scoreboard