/*######################################################################
## Class Name: Virtual_B_Type_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to start B-Type instruction sequence.
######################################################################*/
class Virtual_B_Type_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_B_Type_Seq)

    Instruction_B_Type_Sequence btype_seq;
    
    function new(string name="Virtual_B_Type_Seq");
        super.new(name);
    endfunction
    virtual task body();
        btype_seq=Instruction_B_Type_Sequence::type_id::create("btype_seq");
        btype_seq.num_transactions=33;
        fork
            btype_seq.start(p_sequencer.instr_sqr);
            
        join_none
        #2000;
        disable fork;

    endtask
endclass
