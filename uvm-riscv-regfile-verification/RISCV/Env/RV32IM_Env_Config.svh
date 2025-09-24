/*###################################################################### 
## Class Name: RV32IM_Env_Config   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This configuration class is used to share environment-level parameters and 
    component configuration handles across the UVM testbench. 
    This class is typically set in the UVM config DB and retrieved by each component 
    during the build phase.
######################################################################*/

class RV32IM_Env_Config extends uvm_object;
	`uvm_object_utils(RV32IM_Env_Config)

	Instruction_Agent_Config 	instr_cfg;
	Data_Memory_Config 			Data_Memory_cfg_inst;
	Configuration_cfg 			configuration_cfg_inst;
	Debug_Config  				debug_cfg_inst;
	EX_Config					EX_cfg_inst;
	Interrupt_Config  			interrupt_cfg_inst;
	Register_File_CFG		 	RF_cfg_inst;
	

	bit env_has_instruction_agent;
	bit env_has_instruction_coverage_collector;

	bit env_has_configuration_agent;
	bit env_has_configuration_coverage_collector;

	bit env_has_debug_agent;

	bit env_has_interrupt_agent;
	bit env_has_interrupt_coverage_collector;

	bit env_has_RF_agent;
	bit env_has_RF_coverage_collector;


	bit env_has_ex_agent;
	bit env_has_ex_coverage_collector;

	bit env_has_data_memory_agent;
	bit env_has_data_memory_coverage_collector;
	
	bit env_has_scoreboard;

	function new(string name = "RV32IM_Env_Config");
		super.new(name);
		instr_cfg 				=new("instr_cfg");
		Data_Memory_cfg_inst 	=new("Data_Memory_cfg_inst");
		configuration_cfg_inst	=new("configuration_cfg_inst");
		debug_cfg_inst			=new("debug_cfg_inst");
		EX_cfg_inst				=new("EX_cfg_inst");
		interrupt_cfg_inst		=new("interrupt_cfg_inst");
		RF_cfg_inst				=new("RF_cfg_inst");
	endfunction : new
endclass