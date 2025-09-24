/*######################################################################
## Class Name: Base_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This base test instantiates env , configure env , sets the config object for the env and its agents.
    .It gets Virtual interfaces handle and set them to the  corresponding agent configurations.
    .It starts the required initializtion virtual sequence on virtual sequencer.
######################################################################*/
class Base_Test extends uvm_test;
  `uvm_component_utils(Base_Test)
    
      RV32IM_Env env;
      RV32IM_Env_Config env_cfg;
      Virtual_Base_Seq v_seq;
      
  function new(string name="Base_Test",uvm_component parent=null);
      super.new(name,parent);
  endfunction
  virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env =RV32IM_Env::type_id::create("env",this);
        env_cfg=new("env_cfg");
        configure_env(env_cfg);
      if(!uvm_config_db#(virtual Instruction_Interface)::get(this,"","instruction_vif",env_cfg.instr_cfg.vif))
          `uvm_fatal("Base_Test","Can't get Instruction_vif from the config db")

        if(!uvm_config_db#(virtual Data_Memory_IF)::get(this,"","Data_Memory_vif",env_cfg.Data_Memory_cfg_inst.Data_Memory_vif))
          `uvm_fatal("Base_Test","Can't get Data_Memory_IF from the config db")

      if(!uvm_config_db#(virtual Configuration_IF)::get(this,"","configuration_vif",env_cfg.configuration_cfg_inst.configuration_vif))
          `uvm_fatal("Base_Test","Can't get Configuration_IF from the config db")

        if(!uvm_config_db#(virtual Debug_Interface)::get(this,"","debug_vif",env_cfg.debug_cfg_inst.Debug_vif))
          `uvm_fatal("Base_Test","Can't get Debug_Interface from the config db")

        if(!uvm_config_db#(virtual EX_Interface)::get(this,"","ex_vif",env_cfg.EX_cfg_inst.EX_vif))
          `uvm_fatal("Base_Test","Can't get EX_Interface from the config db")

        if(!uvm_config_db#(virtual Interrupt_IF)::get(this,"","interrupt_vif",env_cfg.interrupt_cfg_inst.Interrupt_vif))
          `uvm_fatal("Base_Test","Can't get Interrupt_IF from the config db")

        if(!uvm_config_db#(virtual Register_File_Interface)::get(this,"","RF_vif",env_cfg.RF_cfg_inst.RF_vif))
          `uvm_fatal("Base_Test","Can't get Interrupt_IF from the config db")

        
      uvm_config_db#(RV32IM_Env_Config)::set(this,"env","RV32IM_Env_Config",env_cfg);
  endfunction
  virtual function void configure_env(ref RV32IM_Env_Config cfg);
        //Instruction agent configurations
        cfg.env_has_instruction_agent=1'b1;
        cfg.instr_cfg.agent_is_active=UVM_ACTIVE;
        cfg.env_has_instruction_coverage_collector=1'b1;
        
        //configuration agent cfg
        cfg.env_has_configuration_agent=1'b1;
        cfg.configuration_cfg_inst.configuration_is_active=UVM_ACTIVE;
        cfg.env_has_configuration_coverage_collector=1'b1;
        
        // debug agent configurations
        cfg.env_has_debug_agent=1'b1;
        cfg.debug_cfg_inst.Debug_is_active=UVM_ACTIVE;

        // interrupt agent configurations
        cfg.env_has_interrupt_agent=1'b1;
        cfg.interrupt_cfg_inst.Interrupt_is_active=UVM_ACTIVE;
        
        // RF agent configurations
        cfg.env_has_RF_agent=1'b1;
        cfg.RF_cfg_inst.RF_Is_Active=UVM_PASSIVE;
        cfg.env_has_RF_coverage_collector=1'b1;

        //execute agent configurations
        cfg.env_has_ex_agent=1'b1;
        cfg.EX_cfg_inst.EX_is_active=UVM_PASSIVE;
        cfg.env_has_ex_coverage_collector=1'b1;

        //data memory configurations
        cfg.env_has_data_memory_agent=1'b1;
        cfg.env_has_data_memory_coverage_collector=1'b1;
        cfg.Data_Memory_cfg_inst.Data_Memory_is_active=UVM_ACTIVE;

        cfg.env_has_scoreboard=1'b1;
  endfunction
virtual task main_phase(uvm_phase phase);
        phase.raise_objection(this);
            `uvm_info("Base_Test","main phase is started",UVM_MEDIUM)
                 v_seq=Virtual_Base_Seq::type_id::create("v_seq");
                 v_seq.start(env.v_sqr);
                 #200;

            `uvm_info("Base_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
endtask
endclass
