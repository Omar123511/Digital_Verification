/*######################################################################
## Class Name: Register_File_Driver  
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .It drives the register file from predefined sequence
######################################################################*/
class Register_File_Driver extends uvm_driver #(Register_File_Sequence_Item);
	
	`uvm_component_utils(Register_File_Driver)

	virtual Register_File_Interface RF_vif;

	function new(string name = "Register_File_Driver", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	virtual task run_phase(uvm_phase phase);
		super.run_phase(phase);
		`uvm_info(get_full_name(), $sformatf("Start of run_phase"), UVM_LOW)
		forever begin
			`uvm_info(get_full_name(), $sformatf("Wait for item from sequencer"), UVM_LOW)
			seq_item_port.get_next_item(req);
			`uvm_info(get_full_name(), $sformatf("Go to drive task"), UVM_LOW)

			drive();

			seq_item_port.item_done();		

		end
	endtask : run_phase


	virtual task drive();
		@(posedge RF_vif.clk);
		RF_vif.rst_n  	<= req.rst_n;

		RF_vif.raddr_a_i 	<= req.raddr_a_i;
		req.rdata_a_o 		= RF_vif.rdata_a_o;

		RF_vif.raddr_b_i 	<= req.raddr_b_i;
		req.rdata_b_o 		= RF_vif.rdata_b_o; 

		RF_vif.raddr_c_i 	<= req.raddr_c_i;
		req.rdata_c_o 		= RF_vif.rdata_c_o;

		RF_vif.we_a_i 		<= req.we_a_i;
		RF_vif.waddr_a_i 	<= req.waddr_a_i;
		RF_vif.wdata_a_i 	<= req.wdata_a_i;

		RF_vif.we_b_i 		<= req.we_b_i;
		RF_vif.waddr_b_i 	<= req.waddr_b_i;
		RF_vif.wdata_b_i 	<= req.wdata_b_i;
		
		req.print();
	endtask : drive
endclass : Register_File_Driver