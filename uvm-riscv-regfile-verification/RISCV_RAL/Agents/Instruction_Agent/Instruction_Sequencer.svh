/*######################################################################
## Class Name: Instruction_Sequencer  
## Engineer : Omnia Mohamed
## Date: May 2025
######################################################################*/
class Instruction_Sequencer extends uvm_sequencer#(Instruction_Seq_Item);
    `uvm_component_utils(Instruction_Sequencer)
    
    function new(string name="Instruction_Sequencer",uvm_component parent=null);
        super.new(name,parent);

    endfunction
endclass