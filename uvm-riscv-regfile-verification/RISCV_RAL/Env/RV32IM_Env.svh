/*######################################################################
## Class Name : RV32IM_Env
## Engineer   : Abdelrhman Tamer
## Date       : May 2025
## Description: 
   This UVM environment class encapsulates the overall verification 
   components required for the RV32IM processor. It instantiates and 
   configures the agents (Instruction, Configuration, Data_Memory, RF, Interrupt, EX_Stage),
   coverage collectors, and provides connectivity between the 
   analysis ports and subscribers.
######################################################################*/
class RV32IM_Env extends uvm_env;
	`uvm_component_utils(RV32IM_Env)
	
   // Declrations 
   RAL_Env                    RAL_Env_inst;
   RV32IM_Env_Config          env_cfg;
   Scoreboard                 scr;
   Virtual_Sequencer          v_sqr;

   Instruction_Agent 		   Instruction_agt;
	Configuration_Agent 	      Configuration_agt;
	Data_Memory_Agent 		   Data_Memory_agt;
   Debug_Agent                debug_agt;
   EX_Agent 				      EX_agt;
   Interrupt_Agent            interrupt_agt;
	Register_File_Agent        RF_agt;
   
   Instruction_Coverage 	   Instruction_cvr;
   Configuration_Coverage     Configuration_cvr;
   Data_Memory_Coverage	      Data_Memory_cvr;
   Interrupt_Coverage         interrupt_cvr;
	EX_Coverage	               EX_cvr;
	Register_File_Coverage     RF_cvr;

	
	function new (string name = "RV32IM_Env", uvm_component parent = null);
		super.new(name, parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      v_sqr          = Virtual_Sequencer::type_id::create("v_sqr",this);
      RAL_Env_inst   = RAL_Env::type_id::create ("RAL_Env_inst", this);
      uvm_reg::include_coverage ("*", UVM_CVR_ALL);

      if(!uvm_config_db#(RV32IM_Env_Config)::get(this,"","RV32IM_Env_Config",env_cfg))
            `uvm_fatal("RV32IM_Env","Can't get RV32IM_Env_Config from the config db ")


		if(env_cfg.env_has_instruction_agent==UVM_ACTIVE)
         begin
            Instruction_agt = Instruction_Agent::type_id::create("Instruction_agt", this);
            uvm_config_db#(Instruction_Agent_Config)::set(this,"Instruction_agt","Instruction_Agent_Config",env_cfg.instr_cfg);
         end


		if(env_cfg.env_has_configuration_agent==UVM_ACTIVE)
         begin
            Configuration_agt 	= Configuration_Agent::type_id::create("Configuration_agt", this);
            uvm_config_db#(Configuration_cfg)::set(this,"Configuration_agt","cfg",env_cfg.configuration_cfg_inst);
         end


      if(env_cfg.env_has_RF_agent==1'b1)
         begin
            RF_agt 	= Register_File_Agent ::type_id::create("RF_agt", this);
            uvm_config_db#(Register_File_CFG)::set(this,"RF_agt","RF_cfg",env_cfg.RF_cfg_inst); 
         end


		if(env_cfg.env_has_ex_agent==1'b1)
         begin
            EX_agt 	= EX_Agent ::type_id::create("EX_agt", this);
            uvm_config_db#(EX_Config)::set(this,"EX_agt","EX_CFG",env_cfg.EX_cfg_inst); 
         end


      if(env_cfg.env_has_data_memory_agent==UVM_ACTIVE)
         begin
            Data_Memory_agt = Data_Memory_Agent ::type_id::create("Data_Memory_agt", this);
            uvm_config_db#(Data_Memory_Config)::set(this,"Data_Memory_agt","Agt_Data_Memory_IF",env_cfg.Data_Memory_cfg_inst); 
         end


      if(env_cfg.env_has_debug_agent==1'b1)
         begin
            debug_agt=Debug_Agent::type_id::create("debug_agt",this);
            uvm_config_db#(Debug_Config)::set(this,"debug_agt","Debug_Config",env_cfg.debug_cfg_inst); 
         end


      if(env_cfg.env_has_interrupt_agent==1'b1)
         begin
            interrupt_agt=Interrupt_Agent::type_id::create("interrupt_agt",this);
            uvm_config_db#(Interrupt_Config)::set(this,"interrupt_agt","Interrupt_Agent_Config",env_cfg.interrupt_cfg_inst); 
         end

      if (env_cfg.env_has_scoreboard == 1'b1) begin
         scr = Scoreboard::type_id::create("scr", this);
      end
        

      if(env_cfg.env_has_instruction_coverage_collector==1'b1)
         begin
            Instruction_cvr 	= Instruction_Coverage ::type_id::create("Instruction_cvr", this); 
         end


      if(env_cfg.env_has_configuration_coverage_collector==1'b1)
         begin
            Configuration_cvr = Configuration_Coverage::type_id::create("Configuration_cvr", this);
         end


      if(env_cfg.env_has_data_memory_coverage_collector==1'b1)
         begin
            Data_Memory_cvr = Data_Memory_Coverage::type_id::create("Data_Memory_cvr", this);
         end


      if(env_cfg.env_has_interrupt_coverage_collector==1'b1)
         begin
           interrupt_cvr 	= Interrupt_Coverage ::type_id::create("interrupt_cvr", this); 
         end


      if(env_cfg.env_has_ex_coverage_collector==1'b1)
         begin
            EX_cvr = EX_Coverage ::type_id::create("EX_cvr", this);
         end
		
      if(env_cfg.env_has_RF_coverage_collector==1'b1)
         begin
            RF_cvr = Register_File_Coverage ::type_id::create("RF_cvr", this);
         end
	endfunction : build_phase
	

	function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      if(env_cfg.env_has_instruction_agent==1'b1 && env_cfg.env_has_instruction_coverage_collector==1'b1)
         begin
            Instruction_agt.agent_ap.connect(Instruction_cvr.imp_instruction_cov);	// connect monitor to Coverage collector
         end


      if(env_cfg.env_has_configuration_agent==1'b1 && env_cfg.env_has_configuration_coverage_collector==1'b1)
         begin
            Configuration_agt.agt_ap.connect(Configuration_cvr.cov);                // connect monitor to Coverage collector
         end


      if(env_cfg.env_has_interrupt_agent==1'b1&&env_cfg.env_has_interrupt_coverage_collector==1'b1)
         begin
            interrupt_agt.agt_ap.connect(interrupt_cvr.cov);                        // connect monitor to Coverage collector
         end


      if(env_cfg.env_has_RF_agent==1'b1 && env_cfg.env_has_RF_coverage_collector==1'b1)
         begin
            RF_agt.RF_agt_Actual_ap.connect(RF_cvr.analysis_export);	               // connect monitor to Coverage collector
         end


      if(env_cfg.env_has_RF_agent==1'b1 && env_cfg.env_has_scoreboard==1'b1)
         begin
            RF_agt.RF_agt_Actual_ap.connect(scr.Register_File_actual_export);       // connect DUT to scoreboard 
         end


      if(env_cfg.env_has_ex_agent==1'b1 && env_cfg.env_has_ex_coverage_collector==1'b1)
         begin
            EX_agt.agt_ap.connect(EX_cvr.cov_export);                               // connect monitor to Coverage collector
         end


      if(env_cfg.env_has_ex_agent==1'b1 && env_cfg.env_has_scoreboard==1'b1)
         begin
            EX_agt.agt_ap.connect(scr.EX_actual_export);                            // connect monitor to scoreboard
            EX_agt.ref_agt_ap.connect(scr.EX_refrence_export);                      // connect refrence model to scoreboard
         end


      if(env_cfg.env_has_data_memory_agent==1'b1 && env_cfg.env_has_data_memory_coverage_collector==1'b1)
         begin
            Data_Memory_agt.agt_dut_ap.connect(Data_Memory_cvr.imp_sub);	         // connect monitor to Coverage collector
         end


		  if(env_cfg.env_has_data_memory_agent==1'b1 && env_cfg.env_has_data_memory_coverage_collector==1'b1)begin
            Data_Memory_agt.agt_dut_ap.connect(Data_Memory_cvr.imp_sub);	   // connect monitor to Coverage collector
        end


		  if(env_cfg.env_has_data_memory_agent==1'b1 && env_cfg.env_has_scoreboard==1'b1)begin
            Data_Memory_agt.agt_dut_ap.connect(scr.Data_Memory_actual_export);      // connect DUT to scoreboard

        end
        

      // Connect RAL
      RAL_Env_inst.DM_agent = Data_Memory_agt;
      RAL_Env_inst.Reg_Block_inst.default_map.set_sequencer(Data_Memory_agt.sqr, RAL_Env_inst.DM_Adapter_inst);
      Data_Memory_agt.monitor.mon_ap.connect(RAL_Env_inst.DM_Predictor.bus_in);

      RAL_Env_inst.RF_agent = RF_agt;

      RF_agt.RF_mon.REF_Monitor_ap.connect(RAL_Env_inst.RF_Predictor.bus_in);

      RF_agt.RF_mon.REF_Monitor_ap.connect(RAL_Env_inst.RF_Read_a_Predictor.bus_in);
      RF_agt.RF_mon.REF_Monitor_ap.connect(RAL_Env_inst.RF_Read_b_Predictor.bus_in);
      RF_agt.RF_mon.REF_Monitor_ap.connect(RAL_Env_inst.RF_Read_c_Predictor.bus_in);
      

      // Connect Vitrual Sequencer
      v_sqr.config_sqr      = Configuration_agt.sqr;
      v_sqr.instr_sqr       = Instruction_agt.sqr;
      v_sqr.data_memory_sqr = Data_Memory_agt.sqr;
      v_sqr.debug_sqr       = debug_agt.sqr;
      v_sqr.interrupt_sqr   = interrupt_agt.sqr;
	endfunction : connect_phase
	
endclass