/*######################################################################
## Class Name: Virtual_Sequencer  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequencer is used to run all virtual sequences.
######################################################################*/
class Virtual_Sequencer extends uvm_sequencer#(uvm_sequence_item);
    `uvm_component_utils(Virtual_Sequencer)
    
    // all sequencers handles 
    Configuration_Sequencer config_sqr;
    Instruction_Sequencer   instr_sqr;
    Data_Memory_Sequencer   data_memory_sqr;
    Debug_Sequencer         debug_sqr;
    Interrupt_Sequencer     interrupt_sqr;

    function new(string name="Virtual_Sequencer",uvm_component parent=null);
        super.new(name,parent);

    endfunction
endclass