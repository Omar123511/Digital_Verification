/* RAL SCR */
/*###################################################################### 
## Class Name: Scoreboard   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This class checks the functional correctness of the DUT by comparing 
    the expected results with the actual outputs collected by monitors.
######################################################################*/
class Scoreboard extends uvm_scoreboard;
	`uvm_component_utils(Scoreboard)

	//Register_File
	uvm_analysis_export 	#(Register_File_Sequence_Item) Register_File_actual_export;
	uvm_tlm_analysis_fifo 	#(Register_File_Sequence_Item) Register_File_actual_fifo;

	Register_File_Sequence_Item Register_File_from_dut_trans; 	// transaction comes from the dut


	//EX
	uvm_analysis_export 	#(EX_Seq_Item) EX_actual_export;
	uvm_analysis_export 	#(EX_Ref_Seq_Item) EX_refrence_export;
	uvm_tlm_analysis_fifo 	#(EX_Seq_Item) EX_actual_fifo;
	uvm_tlm_analysis_fifo 	#(EX_Ref_Seq_Item) EX_refrence_fifo;

	EX_Ref_Seq_Item EX_from_rf_trans;  // transaction comes from the refrence model
	EX_Seq_Item EX_from_dut_trans; // transaction comes from the dut


	//Data_Memory
	uvm_analysis_export 	#(Data_Memory_Seq_Item) Data_Memory_actual_export;
	uvm_tlm_analysis_fifo 	#(Data_Memory_Seq_Item) Data_Memory_actual_fifo;
    
	// RAL
    Reg_Block           	scr_Reg_Block_inst; 

	Data_Memory_Seq_Item Data_Memory_from_rf_trans; // transaction comes from the refrence model
	Data_Memory_Seq_Item Data_Memory_from_dut_trans; 	// transaction comes from the dut

	
	// Compare the Register File agent transactions
	extern task Compare_RF(
		input Reg_Block blk,
		input Register_File_Sequence_Item  Compare_RF_trans, 
		output bit error, 
		output bit correct);  
	
	// Compare the EX agent transactions
	extern task Compare_EX(
		input EX_Ref_Seq_Item  EX_from_rf_trans, 
		input EX_Seq_Item  EX_from_dut_trans, 
		output bit error, 
		output bit correct);  										 
	
	// Compare the Data Memory agent transactions
	extern task Compare_DM(
	    input  Reg_Block blk,
	    input  Data_Memory_Seq_Item Compare_DM_trans,
	    output bit error,
	    output bit correct);


	// Scoreboard Status
	int Register_File_correct_count = 0;
	int Register_File_error_count   = 0;

	int EX_correct_count = 0;
	int EX_error_count   = 0;

	int Data_Memory_correct_count = 0;
	int Data_Memory_error_count   = 0;
	
	
	// internal signals
	bit Register_File_correct_bit = 0;
	bit Register_File_error_bit   = 0;

	bit EX_correct_bit = 0;
	bit EX_error_bit   = 0;

	bit Data_Memory_correct_bit = 0;
	bit Data_Memory_error_bit 	= 0;

	uvm_status_e 	mem_status;
	bit [31:0] ref_data;

	function new (string name = "Scoreboard", uvm_component parent = null);
		super.new(name, parent);
	endfunction : new
	
	
	function void build_phase (uvm_phase phase);
		super.build_phase(phase);
		//Register_File
		Register_File_actual_export  = new("Register_File_actual_export", this);
		Register_File_actual_fifo    = new("Register_File_actual_fifo", this);

		//EX
		EX_actual_export  			 = new("EX_actual_export", this);
		EX_refrence_export  		 = new("EX_refrence_export", this);
		EX_actual_fifo    			 = new("EX_actual_fifo", this);
		EX_refrence_fifo    		 = new("EX_refrence_fifo", this);

		//Data_Memory
		Data_Memory_actual_export  	 = new("Data_Memory_actual_export", this);
		Data_Memory_actual_fifo    	 = new("Data_Memory_actual_fifo", this);

		// RAL
		if (!uvm_config_db#(Reg_Block)::get(this, "", "Reg_Block_inst", scr_Reg_Block_inst)) 
			begin
			 	`uvm_fatal("SCOREBOARD", "Failed to get ral_reg_block from config DB")
			end
	endfunction : build_phase
	
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		//Register_File
		Register_File_actual_export.connect(Register_File_actual_fifo.analysis_export);

		//EX
		EX_actual_export.connect(EX_actual_fifo.analysis_export);
		EX_refrence_export.connect(EX_refrence_fifo.analysis_export);

		//Data_Memory
		Data_Memory_actual_export.connect(Data_Memory_actual_fifo.analysis_export);

		if (scr_Reg_Block_inst == null) 
			begin
				`uvm_fatal("SCOREBOARD", "scr_Reg_Block_inst is NULL in run_phase")
			end
	endfunction
	
	 
	task run_phase(uvm_phase phase);
		super.run_phase(phase);
		forever 
		begin
			fork
				// Thread to compare the Register_File Agent
				begin 
					Register_File_actual_fifo.get(Register_File_from_dut_trans);

					Compare_RF(scr_Reg_Block_inst, Register_File_from_dut_trans, Register_File_error_bit, Register_File_correct_bit);
					
					if (Register_File_error_bit)
						begin
							Register_File_error_count++;
						end
					else if (Register_File_correct_bit)
						begin
							Register_File_correct_count++;
						end
				end

				// Thread to compare the EX Agent
				begin 
					EX_refrence_fifo.get(EX_from_rf_trans);
					EX_actual_fifo.get(EX_from_dut_trans);

					// Only Compares when the valide is high
					if (EX_from_dut_trans.ex_valid_o)
						begin
							Compare_EX(EX_from_rf_trans, EX_from_dut_trans, EX_error_bit, EX_correct_bit);
							if (EX_error_bit)
								begin
									EX_error_count++;
								end
							else if (EX_correct_bit)
								begin
									EX_correct_count++;
								end
						end
				end

				// Thread to compare the Data_Memory Agent
				begin 
					Data_Memory_actual_fifo.get(Data_Memory_from_dut_trans);
                	
					Compare_DM(scr_Reg_Block_inst, Data_Memory_from_dut_trans, Data_Memory_error_bit, Data_Memory_correct_bit);

					if (Data_Memory_error_bit)
						begin
							Data_Memory_error_count++;
						end
					else if (Data_Memory_correct_bit)
						begin
							Data_Memory_correct_count++;
						end
				end
			join_any

		end

	endtask : run_phase

	
	function void report_phase (uvm_phase phase);
   		super.report_phase(phase);
   		`uvm_info("Scoreboard", $sformatf("Register_File_correct_count = %0d", Register_File_correct_count), UVM_NONE);
   		`uvm_info("Scoreboard", $sformatf("Register_File_error_count   = %0d", Register_File_error_count), UVM_NONE);

   		`uvm_info("Scoreboard", $sformatf("EX_correct_count = %0d", EX_correct_count), UVM_NONE);
   		`uvm_info("Scoreboard", $sformatf("EX_error_count   = %0d", EX_error_count), UVM_NONE);

   		`uvm_info("Scoreboard", $sformatf("Data_Memory_correct_count = %0d", Data_Memory_correct_count), UVM_NONE);
   		`uvm_info("Scoreboard", $sformatf("Data_Memory_error_count   = %0d", Data_Memory_error_count), UVM_NONE);
	endfunction : report_phase
	
endclass




///////////////////////////////////////////////////////// Compare TASKS /////////////////////////////////////////////////
task Scoreboard::Compare_RF(
	input Reg_Block blk,
	input Register_File_Sequence_Item  Compare_RF_trans, 
	output bit error, 
	output bit correct);

	bit [31:0] REF_Read_a_address, REF_Read_b_address, REF_Read_c_address;
	bit [31:0] REF_Read_a_data,    REF_Read_b_data,    REF_Read_c_data;
	bit        addr_a_match, data_a_match;
	bit        addr_b_match, data_b_match;
	bit        addr_c_match, data_c_match;

	REF_Read_a_address = Compare_RF_trans.raddr_a_i;
	REF_Read_b_address = Compare_RF_trans.raddr_b_i;
	REF_Read_c_address = Compare_RF_trans.raddr_c_i;

  	`uvm_info("Scoreboard", $sformatf("Accessing RF_REG[0x%0h], RF_REG[0x%0h], RF_REG[0x%0h]",
    REF_Read_a_address, REF_Read_b_address, REF_Read_c_address), UVM_LOW)

    REF_Read_a_data = blk.RF_REG[REF_Read_a_address].get_mirrored_value(); 
    REF_Read_b_data = blk.RF_REG[REF_Read_b_address].get_mirrored_value(); 
    REF_Read_c_data = blk.RF_REG[REF_Read_c_address].get_mirrored_value();
 

	`uvm_info ("SCB", $sformatf("addr_a=0x%0h data_a=0x%0h addr_b=0x%0h data_b=0x%0h addr_c=0x%0h data_c=0x%0h ", 
	                            REF_Read_a_address, 
	                            REF_Read_a_data, 
	                            REF_Read_b_address,
	                           	REF_Read_b_data, 
	                            REF_Read_c_address,
	                            REF_Read_c_data)
	                            	, UVM_LOW);


	// Port A
	addr_a_match = (Compare_RF_trans.raddr_a_i === REF_Read_a_address);
	data_a_match = (Compare_RF_trans.rdata_a_o === REF_Read_a_data);

	// Read Port B
	addr_b_match = (Compare_RF_trans.raddr_b_i === REF_Read_b_address);
	data_b_match = (Compare_RF_trans.rdata_b_o === REF_Read_b_data);

	// Read Port C
	addr_c_match = (Compare_RF_trans.raddr_c_i === REF_Read_c_address);
	data_c_match = (Compare_RF_trans.rdata_c_o === REF_Read_c_data);


  	error   = ~( (addr_a_match && data_a_match) && (addr_b_match && data_b_match) && (addr_c_match && data_c_match) );
    correct = (addr_a_match && data_a_match) && (addr_b_match && data_b_match) && (addr_c_match && data_c_match);
   
  

    // Print if Port A Address mismatch
    if (!addr_a_match) begin
        `uvm_error("COMPARE_RF", $sformatf("Mismatch Address: DUT_A = %0h, REF_A = %0h",
                                           Compare_RF_trans.raddr_a_i,
                                           REF_Read_a_address));
        error = 1;
    end

    // Print if Port A Data mismatch
    if (!data_a_match) begin
        `uvm_error("COMPARE_RF", $sformatf("Mismatch Data: DUT_A = %0h, REF_A = %0h",
                                           Compare_RF_trans.rdata_a_o,
                                           REF_Read_a_data));
        error = 1;
    end


    // Print if Port B Address mismatch
    if (!addr_b_match) begin
        `uvm_error("COMPARE_RF", $sformatf("Mismatch Address: DUT_B = %0h, REF_B = %0h",
                                           Compare_RF_trans.raddr_b_i,
                                           REF_Read_b_address));
        error = 1;
    end

    // Print if Port B Data mismatch
    if (!data_b_match) begin
        `uvm_error("COMPARE_RF", $sformatf("Mismatch Data: DUT_B = %0h, REF_B = %0h",
                                           Compare_RF_trans.rdata_b_o,
                                           REF_Read_b_data));
        error = 1;
    end


    // Print if Port C Address mismatch
    if (!addr_c_match) begin
        `uvm_error("COMPARE_RF", $sformatf("Mismatch Address: DUT_C = %0h, REF_C = %0h",
                                           Compare_RF_trans.raddr_c_i,
                                           REF_Read_c_address));
        error = 1;
    end

    // Print if Port C Data mismatch
    if (!data_c_match) begin
        `uvm_error("COMPARE_RF", $sformatf("Mismatch Data: DUT_C = %0h, REF_C = %0h",
                                           Compare_RF_trans.rdata_c_o,
                                           REF_Read_c_data));
        error = 1;
    end


		

    // Print Correct Message if all is ok
    if (correct && !error) begin
        `uvm_info("COMPARE_RF", "Comparison PASS", UVM_LOW);
    end
endtask
	
task Scoreboard::Compare_EX(
	input EX_Ref_Seq_Item  EX_from_rf_trans, 
	input EX_Seq_Item  EX_from_dut_trans, 
	output bit error, 
	output bit correct);

    // Port A
    bit ALU_MULT_op 	 = (EX_from_dut_trans.regfile_alu_wdata_fw_o === EX_from_rf_trans.regfile_alu_wdata_fw_o_ref);
    bit Multi_Cycle_Flag = (EX_from_dut_trans.mult_multicycle_o 	 === EX_from_rf_trans.mult_multicycle_o_ref);
    bit Branch_Flag 	 = (EX_from_dut_trans.branch_decision_o 	 === EX_from_rf_trans.branch_decision_o_ref);


    error   = ~(ALU_MULT_op && Multi_Cycle_Flag && Branch_Flag);
    correct = ALU_MULT_op && Multi_Cycle_Flag && Branch_Flag;

    // ALU/MULT Mismatch
    if (!ALU_MULT_op) 
	    begin
	        `uvm_error("COMPARE_EX", $sformatf("EX wdata comparison failed. DUT: %s, REF: 0x%0h", 
	        									EX_from_dut_trans.convert2string(), 
	        									EX_from_rf_trans.regfile_alu_wdata_fw_o_ref));
	        error = 1;
	    end

    // Branch_Flag Mismatch
    if (!Branch_Flag) 
	    begin
	        `uvm_error("COMPARE_EX", $sformatf("EX branch decision comparison failed. DUT: %s, REF: 0x%0h", 
	        									EX_from_dut_trans.convert2string(), 
	        									EX_from_rf_trans.branch_decision_o_ref));
	        error = 1;
	    end


    // Print Correct Message if all is ok
    if (correct && !error) 
	    begin
	        `uvm_info("COMPARE_EX", "Comparison PASS", UVM_LOW);
	    end
endtask

task Scoreboard::Compare_DM(
    input  Reg_Block blk,
    input  Data_Memory_Seq_Item Compare_DM_trans,
    output bit error,
    output bit correct);
	
	bit [31:0] REF_address, REF_data;
	REF_address = Compare_DM_trans.address;
	#10;

	// Read from mirror memory
    blk.Memory.Read(REF_address, REF_data); 

    if (Compare_DM_trans.data !== REF_data) 
		begin
			if (Compare_DM_trans.data_we_o)
				begin // Write
					`uvm_error("COMPARE_DM", $sformatf("Mismatch of Write_ID =%0d at address %0h and Data: DUT = %0h, REF = %0h",
												Compare_DM_trans.Write_ID,
												Compare_DM_trans.address, 
												Compare_DM_trans.data, 
												ref_data));
				end
			else
				begin // Read
					`uvm_error("COMPARE_DM", $sformatf("Mismatch of Read_ID =%0d at address %0h and Data: DUT = %0h, REF = %0h",
												Compare_DM_trans.Read_ID,
												Compare_DM_trans.address, 
												Compare_DM_trans.data, 
												ref_data));
				end
			error 	= 1;
			correct = 0;
		end
	else
		begin
			error 	= 0;
			correct = 1;			
		end

endtask