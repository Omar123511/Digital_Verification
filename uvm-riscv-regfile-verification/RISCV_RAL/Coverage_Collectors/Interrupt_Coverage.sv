/*###################################################################### 
## Class Name: Interrupt_Coverage   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This class defines the functional coverage model for the interrupt interface. 
    It captures which interrupt lines were asserted, whether acknowledgments 
    occurred, and which interrupt IDs were reported by the DUT. This ensures 
    comprehensive verification of interrupt handling behavior.
######################################################################*/
class Interrupt_Coverage extends uvm_component;
	`uvm_component_utils(Interrupt_Coverage)
	uvm_analysis_export 	#(Interrupt_Seq_Item) cov;
	uvm_tlm_analysis_fifo 	#(Interrupt_Seq_Item) cov_fifo;

	Interrupt_Seq_Item cov_trans; 

	covergroup cg1;
	    rst_cov: coverpoint cov_trans.rst_n
	        {
	            bins rst_1 = {1};
	            bins rst_0 = {0};
	        }

	    interrupt_id: coverpoint cov_trans.interrupt_id 
			{
				bins standard[] 		= {3, 7, 11};// Standard RISC-V interrupts
				ignore_bins custom   	= {[16:31]}; // CV32E40P custom interrupts
				illegal_bins reserved 	= default;   // Ensure reserved IDs are never used
			}

		ack: coverpoint cov_trans.acknowledged 
			{
		    	bins yes = {1}; 
		  	}

		mode: coverpoint cov_trans.Mode 
			{
				bins direct_mode   = {0};  
				bins vectored_mode = {1};
			}

		Enable: coverpoint cov_trans.Enable 
			{
				bins on = {1};
			}

        // --------------------------------------------
        //              CROSS COVERAGE
        // --------------------------------------------

		inter: cross Enable, mode, ack
			{
				bins inter_occured = binsof(Enable.on) && binsof(mode.vectored_mode) && binsof(ack.yes);
			}
	endgroup : cg1

	function new (string name = "Interrupt_Coverage", uvm_component parent = null);
		super.new(name, parent);
		cg1 = new();
	endfunction : new
	
	
	function void build_phase (uvm_phase phase);
		super.build_phase(phase);
		cov  		= new("cov", this);
		cov_fifo 	= new("cov_fifo", this);
	endfunction : build_phase
	
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		cov.connect(cov_fifo.analysis_export);
	endfunction
	
	
	function void report_phase(uvm_phase phase);
		super.report_phase(phase);
		`uvm_info("Interrupt_Coverage", $sformatf("Interrupt_Coverage: %0.2f%%",cg1.get_inst_coverage()), UVM_LOW)
    endfunction : report_phase


	task run_phase(uvm_phase phase);
		super.run_phase(phase);
		
		forever 
		begin
			cov_fifo.get(cov_trans);				
			cg1.sample();
		end

	endtask : run_phase
endclass
