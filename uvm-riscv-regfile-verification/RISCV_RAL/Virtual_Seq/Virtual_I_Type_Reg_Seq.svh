/*######################################################################
## Class Name: Virtual_I_Type_Reg_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to start I-Type register sequences.
######################################################################*/
class Virtual_I_Type_Reg_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_I_Type_Reg_Seq)

    Instruction_I_Type_Register_Sequence itype_reg_seq;
    
    function new(string name="Virtual_I_Type_Reg_Seq");
        super.new(name);
    endfunction
    virtual task body();
        itype_reg_seq=Instruction_I_Type_Register_Sequence::type_id::create("itype_reg_seq");
        itype_reg_seq.num_transactions=31; 
        fork
            itype_reg_seq.start(p_sequencer.instr_sqr);
            #200;
        join

    endtask
    endclass
