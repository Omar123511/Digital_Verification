class Register_File_WR_a_Sequence extends uvm_sequence;
	
	`uvm_object_utils(Register_File_WR_a_Sequence)


	function new(string name = "Register_File_WR_a_Sequence");
		super.new(name);
	endfunction

	Register_File_Sequence_Item req;
	virtual task body();
		repeat(5) begin
			req = Register_File_Sequence_Item::type_id::create("req");
			req.print();
			start_item(req);
			assert(req.randomize() with {(req.we_a_i == 1 && req.we_b_i == 0);});
    		finish_item(req);
		end

	endtask
endclass : Register_File_WR_a_Sequence

class Register_File_WR_b_Sequence extends uvm_sequence;
	
	`uvm_object_utils(Register_File_WR_b_Sequence)

	Register_File_Sequence_Item req;

	function new(string name = "Register_File_WR_b_Sequence");
		super.new(name);
	endfunction


	virtual task body();
		repeat(5) begin
			req = Register_File_Sequence_Item::type_id::create("req");
			req.print();
			start_item(req);
			assert(req.randomize() with {(req.we_a_i == 0 && req.we_b_i == 1);});
    		finish_item(req);
		end

	endtask
endclass : Register_File_WR_b_Sequence

class Register_File_WR_a_b_Sequence extends uvm_sequence;
	
	`uvm_object_utils(Register_File_WR_a_b_Sequence)
	Register_File_Sequence_Item req;


	function new(string name = "Register_File_WR_a_b_Sequence");
		super.new(name);
	endfunction


	virtual task body();
		repeat(5) begin
			req = Register_File_Sequence_Item::type_id::create("req");
			req.print();
			start_item(req);
			assert(req.randomize() with {(req.we_a_i == 1 && req.we_b_i == 1);});
    		finish_item(req);
		end

	endtask
endclass : Register_File_WR_a_b_Sequence

class Register_File_Sequence extends uvm_sequence;
	
	`uvm_object_utils(Register_File_Sequence)

	Register_File_WR_a_Sequence seq_a;
	Register_File_WR_b_Sequence seq_b;
	Register_File_WR_a_b_Sequence seq_a_b;


	function new(string name = "Register_File_Sequence");
		super.new(name);
	endfunction

	virtual task body ();
		
		`uvm_do(seq_a)
    	`uvm_do(seq_b)
    	`uvm_do(seq_a_b)
    	
	endtask


endclass : Register_File_Sequence
