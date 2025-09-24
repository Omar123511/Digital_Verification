/*######################################################################
## Class Name: Instruction_Agent_Config  
## Engineer : Omnia Mohamed
## Date: April 2025
## Description:
    .This class contains the configurations of instruction agent.
    .It is used to determine whether the agent is active or passive.
    .It is used to pass the virtual interface handle to both the instruction driver and monior.
    
######################################################################*/
class Instruction_Agent_Config extends uvm_object;
    `uvm_object_utils(Instruction_Agent_Config)

    uvm_active_passive_enum agent_is_active ;
    virtual Instruction_Interface vif;

    function new(string name="Instruction_Agent_Config");
        super.new(name);
    endfunction
endclass