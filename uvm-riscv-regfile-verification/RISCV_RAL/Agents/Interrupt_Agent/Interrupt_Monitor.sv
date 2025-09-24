/*###################################################################### 
## Class Name: Interrupt_Monitor   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This class monitors the DUT’s interrupt output signals (irq_ack_o, irq_id_o) 
    and captures them as transactions for analysis and coverage.
######################################################################*/
class Interrupt_Monitor extends uvm_monitor;
	`uvm_component_utils(Interrupt_Monitor)
	uvm_analysis_port #(Interrupt_Seq_Item) mon_ap;

	virtual Interrupt_IF m_if;
	Interrupt_Seq_Item mon_monans;
	Interrupt_Seq_Item mon;
	
	function new (string name = "Interrupt_Monitor", uvm_component parent = null);
		super.new(name, parent);
	endfunction : new
	
	function void build_phase (uvm_phase phase);
		super.build_phase(phase);
		mon_ap = new("mon_ap", this);
	endfunction : build_phase


	task run_phase(uvm_phase phase);
		super.run_phase(phase);
		
		forever 
		begin
			@(posedge m_if.clk);
			mon = Interrupt_Seq_Item::type_id::create("mon");

			// Capture acknowledgment
			if (m_if.irq_ack_o) 
				begin
					mon.acknowledged   	= m_if.irq_ack_o;
					mon.id 		       	= m_if.irq_id_o;
					mon.Mode 			= m_if.Mode; 
					mon.Enable 			= m_if.Enable; 
					mon_ap.write(mon); 
				end

		end
	endtask
endclass