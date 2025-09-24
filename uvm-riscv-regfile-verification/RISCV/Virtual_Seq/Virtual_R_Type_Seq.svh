/*######################################################################
## Class Name: Virtual_R_Type_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence generates R-Type instructions.
    .It also generates additional Addi instructions alongside the R-Type sequence.
######################################################################*/
class Virtual_R_Type_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_R_Type_Seq)

    Instruction_R_Type_Sequence rtype_seq;
    
    function new(string name="Virtual_R_Type_Seq");
        super.new(name);
    endfunction
    virtual task body();
        rtype_seq=Instruction_R_Type_Sequence::type_id::create("rtype_seq");
        rtype_seq.num_transactions=64; 
        fork

            rtype_seq.start(p_sequencer.instr_sqr);
            
        join

    endtask
    endclass
