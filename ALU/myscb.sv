class myscb;

	mailbox mon2scb;


	bit [5:0] C_expected, C_prev;
	int correct_count, error_count, no_transactions; 


	function new(mailbox mon2scb);
		this.mon2scb = mon2scb;

	endfunction


	
	//env
	task main();
		mytrans trans;
		forever begin
			mon2scb.get(trans);
			golden_logic(trans);
			trans.display("SCB");
			no_transactions++;
		end
		
	endtask : main



	task golden_logic(input mytrans trans);
		
		if (trans.a_en && !trans.b_en) begin
			case (trans.a_op)
				'd0 : C_expected = {trans.A[4], trans.A} + {trans.B[4], trans.B}; 				//ALU_2
				'd1 : C_expected = {trans.A[4], trans.A} - {trans.B[4], trans.B};				//ALU_3
				'd2 : C_expected = trans.A ^ trans.B; 											//ALU_4
				'd3 : C_expected = trans.A & trans.B; 											//ALU_5
				'd4 : C_expected = trans.A & trans.B; 											//ALU_6
				'd5 : C_expected = trans.A | trans.B; 											//ALU_7
				'd6 : C_expected = ~(trans.A ^ trans.B); 										//ALU_8
				default : C_expected = 0;
			endcase
		end

		else if (!trans.a_en && trans.b_en) begin
			case (trans.b_op)
				'd0 : C_expected = ~(trans.A & trans.B); 										//ALU_10
				'd1 : C_expected = {trans.A[4], trans.A} + {trans.B[4], trans.B}; 				//ALU_11
				'd2 : C_expected = {trans.A[4], trans.A} + {trans.B[4], trans.B}; 				//ALU_12
				default : C_expected = 0;
			endcase
		end

		else if (trans.a_en && trans.b_en) begin
			case (trans.b_op)
				'd0 : C_expected = trans.A ^ trans.B; 											//ALU_14
				'd1 : C_expected = ~(trans.A ^ trans.B); 										//ALU_15
				'd2 : C_expected = {trans.A[4], trans.A} - 6'd1; 								//ALU_16
				'd3 : C_expected = {trans.B[4], trans.B} + 6'd2; 								//ALU_17
			endcase
		end
		else begin
			C_expected = C_expected; 															//ALU_18
		end

		check_result(trans);
	endtask : golden_logic


	task check_result(input mytrans trans);
		if (trans.C !== C_expected) begin
			$display("--%0t--",$time);
			$display("SCB::Failed test! Expected Result = %d, Actual Result = %d", $signed(C_expected), $signed(trans.C));
			error_count = error_count + 1;
		end
		else begin
			$display("--%0t--",$time);
			$display("SCB::Successful test! Expected Result = %d, Actual Result = %d", $signed(C_expected), $signed(trans.C));
			correct_count = correct_count + 1;
		end
	endtask : check_result
	
endclass : myscb
