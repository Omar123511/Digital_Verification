/*######################################################################
## Class Name: Register_File_Monitor  
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .It maps the inputs and outputs of the DUT to sequence item to be then sent to the coverage collector, scoreboard, 
	and reference model to generate expected sequence item. 
######################################################################*/
class Register_File_Monitor extends uvm_monitor;

	`uvm_component_utils(Register_File_Monitor)

	virtual Register_File_Interface RF_vif;

	uvm_analysis_port #(Register_File_Sequence_Item) REF_Monitor_ap;

	Register_File_Sequence_Item RF_seq_item;

	function new(string name = "Register_File_Monitor", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		REF_Monitor_ap = new("REF_Monitor_ap", this);
	endfunction : build_phase


	virtual task run_phase(uvm_phase phase);
		super.run_phase(phase);
		forever begin
			RF_seq_item = Register_File_Sequence_Item::type_id::create("RF_seq_item");
			@(posedge RF_vif.clk);
			

			RF_seq_item.rst_n = RF_vif.rst_n;

			RF_seq_item.raddr_a_i 	= RF_vif.raddr_a_i;
			RF_seq_item.rdata_a_o 	= RF_vif.rdata_a_o;
			

			RF_seq_item.raddr_b_i 	= RF_vif.raddr_b_i;
			RF_seq_item.rdata_b_o 	= RF_vif.rdata_b_o;

			RF_seq_item.raddr_c_i 	= RF_vif.raddr_c_i;
			RF_seq_item.rdata_c_o 	= RF_vif.rdata_c_o;
			

			RF_seq_item.we_a_i 		= RF_vif.we_a_i;
			RF_seq_item.waddr_a_i 	= RF_vif.waddr_a_i;
			RF_seq_item.wdata_a_i 	= RF_vif.wdata_a_i;

			RF_seq_item.we_b_i 		= RF_vif.we_b_i;
			RF_seq_item.waddr_b_i 	= RF_vif.waddr_b_i;
			RF_seq_item.wdata_b_i 	= RF_vif.wdata_b_i;

			RF_seq_item.l_status = 0;

			if (RF_seq_item.we_b_i == 1'b1 && (RF_seq_item.waddr_b_i != 'h0)) 
				begin
					RF_seq_item.l_addr = RF_seq_item.waddr_b_i; // array of reg has 31 regs since reg0 has its own reg
					RF_seq_item.l_data = RF_seq_item.wdata_b_i;
					RF_seq_item.l_status = 1;
				end

			if (RF_seq_item.we_a_i == 1'b1 && (RF_seq_item.waddr_a_i != 'h0)) 
				begin
					if (!RF_seq_item.we_b_i && (RF_seq_item.waddr_b_i == RF_seq_item.waddr_a_i)) 
						begin
							RF_seq_item.l_addr = RF_seq_item.waddr_a_i; // array of reg has 31 regs since reg0 has its own reg
							RF_seq_item.l_data = RF_seq_item.wdata_a_i;
							RF_seq_item.l_status = 1;
					end
			end

			REF_Monitor_ap.write(RF_seq_item);	

		end
	endtask : run_phase

	
endclass : Register_File_Monitor
