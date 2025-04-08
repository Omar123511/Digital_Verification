class ALU_cfg extends uvm_object;

	`uvm_object_utils(ALU_cfg)
	
	int item_count;
	int item_count_a_op;
	int item_count_b_op_1;
	int item_count_b_op_2;

	int item_count_sum = item_count_a_op + item_count_b_op_1 + item_count_b_op_2 + item_count;


	int count;
	int count_a_op;
	int count_b_op_1;
	int count_b_op_2;

	int count_sum;


	bit seq_a_op_on, seq_b_op_1_on, seq_b_op_2_on, seq_all_on; 

	int correct_count, error_count;

	int cov_items;

	function new(string name = "ALU_cfg");
		super.new(name);
		item_count_a_op = 4;
		item_count_b_op_1 = 4;
		item_count_b_op_2 = 4;
		item_count = 4;

		count_a_op = 0;
		count_b_op_1 = 0;
		count_b_op_2 = 0;
		count = 0;

		count_sum = 0;

		seq_a_op_on = 0;
		seq_b_op_1_on = 0;
		seq_b_op_2_on = 0;
		seq_all_on = 0;

		correct_count = 0;
		error_count = 0;

		cov_items = 0;


	endfunction
endclass : ALU_cfg
