/*###################################################################### 
## Class Name: Interrupt_Agent   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This agent generates and drives interrupt signals to the DUT through 
    the interrupt interface and monitors DUT responses and sends them to the coverage.
######################################################################*/
class Interrupt_Agent extends uvm_agent;
	`uvm_component_utils(Interrupt_Agent)
	uvm_analysis_port #(Interrupt_Seq_Item) agt_ap;

	Interrupt_Config 		cfg;
	Interrupt_Driver 	drv; 
	Interrupt_Sequencer sqr; 
	Interrupt_Monitor 	mon; 

	function new (string name = "Interrupt_Agent", uvm_component parent = null);
		super.new(name, parent);
	endfunction : new

	function void build_phase (uvm_phase phase);
		//super.build_phase(phase);
		if (!uvm_config_db#(Interrupt_Config)::get(this, "", "Interrupt_Agent_Config", cfg))
			`uvm_fatal("Interrupt_Agent", "Can't get Instruction_cfg from the config db");

		mon 		= Interrupt_Monitor::type_id::create("mon", this);
		agt_ap 		= new("agt_ap", this);
		
		mon.m_if = cfg.Interrupt_vif;

		if (cfg.Interrupt_is_active == UVM_ACTIVE)
			begin
				drv = Interrupt_Driver 		::type_id::create("drv", this);
				sqr = Interrupt_Sequencer 	::type_id::create("sqr", this);
				
				drv.d_if = cfg.Interrupt_vif;
			end

	endfunction : build_phase

	function void connect_phase(uvm_phase phase);
		//super.connect_phase(phase);
		mon.mon_ap.connect(agt_ap);

		if (cfg.Interrupt_is_active == UVM_ACTIVE)
			begin
				drv.seq_item_port.connect(sqr.seq_item_export);
			end
	endfunction : connect_phase

endclass