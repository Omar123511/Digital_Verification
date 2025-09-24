/*######################################################################
## Class Name: Register_File_REF_Model  
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .The reference model generates the expected output and sends it to the scoreboard 
	to be compared with the DUT's that comes from the monitor.
######################################################################*/
class Register_File_REF_Model extends uvm_component;

	`uvm_component_utils(Register_File_REF_Model)

	Register_File_Sequence_Item RF_Actual_Item;
	Register_File_Sequence_Item RF_Expected_Item;

	// virtual Register_File_Interface RF_vif;
	
	uvm_analysis_export #(Register_File_Sequence_Item) RF_Export; 		//actual data from monitor
	uvm_tlm_analysis_fifo #(Register_File_Sequence_Item) RF_FIFO; 		
	uvm_analysis_port #(Register_File_Sequence_Item) REF_Model_ap;
	

	logic [31:0] RF [bit [4:0]];
	//logic [31:0] RF_FP [bit [4:0]];

	
	function new(string name = "Register_File_REF_Model", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		RF_Expected_Item = Register_File_Sequence_Item::type_id::create("RF_Expected_Item");


		RF_Export = new("RF_Export", this);
		RF_FIFO = new("RF_FIFO", this);
		REF_Model_ap = new("REF_Model_ap", this);
		
	endfunction

	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		RF_Export.connect(RF_FIFO.analysis_export);
	endfunction

	virtual task run_phase(uvm_phase phase);
		super.run_phase(phase);
		Reset_RF;
		forever begin
			RF_FIFO.get(RF_Actual_Item);
			// RF_Expected_Item = reference_model(RF_Actual_Item);
			reference_model(RF_Actual_Item);
			REF_Model_ap.write(RF_Expected_Item);
		end

	endtask : run_phase

	virtual task Reset_RF; 					//reset RF
		for (int i = 0; i < 32; i++) begin
			RF[i] = 'h0;
		end
	endtask : Reset_RF

	virtual task reference_model(input Register_File_Sequence_Item Actual_Item);
		// Register_File_Sequence_Item Expected_Item = Register_File_Sequence_Item::type_id::create("Expected_Item");
	
		RF[0] = 'h0;

		RF_Expected_Item.rst_n = Actual_Item.rst_n;

		RF_Expected_Item.we_a_i = Actual_Item.we_a_i;
		RF_Expected_Item.waddr_a_i = Actual_Item.waddr_a_i;
		RF_Expected_Item.wdata_a_i = Actual_Item.wdata_a_i;

		RF_Expected_Item.we_b_i = Actual_Item.we_b_i;
		RF_Expected_Item.waddr_b_i = Actual_Item.waddr_b_i;
		RF_Expected_Item.wdata_b_i = Actual_Item.wdata_b_i;

	
		RF_Expected_Item.raddr_a_i = Actual_Item.raddr_a_i;

		RF_Expected_Item.raddr_b_i = Actual_Item.raddr_b_i;

		RF_Expected_Item.raddr_c_i = Actual_Item.raddr_c_i;



		RF_Expected_Item.rdata_a_o = RF[RF_Expected_Item.raddr_a_i[4:0]];
		RF_Expected_Item.rdata_b_o = RF[RF_Expected_Item.raddr_b_i[4:0]];
		RF_Expected_Item.rdata_c_o = RF[RF_Expected_Item.raddr_c_i[4:0]];



	if (!RF_Expected_Item.rst_n) begin
		for (int i = 1; i < 32; i++)
			RF[i] = 'h0;
	end
	else begin
		if (RF_Expected_Item.we_b_i && (RF_Expected_Item.waddr_b_i != 5'h0)) begin
		    RF[RF_Expected_Item.waddr_b_i[4:0]] = RF_Expected_Item.wdata_b_i;
		end
		if (RF_Expected_Item.we_a_i && (RF_Expected_Item.waddr_a_i != 5'h0)) begin
		    if (!(RF_Expected_Item.we_b_i && 
		        (RF_Expected_Item.waddr_b_i == RF_Expected_Item.waddr_a_i))) begin
		        RF[RF_Expected_Item.waddr_a_i[4:0]] = RF_Expected_Item.wdata_a_i;
		    end
		end
	end

	endtask : reference_model


endclass : Register_File_REF_Model
