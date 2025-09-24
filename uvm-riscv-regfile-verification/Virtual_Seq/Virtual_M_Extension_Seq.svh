/*######################################################################
## Class Name: Virtual_M_Extension_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence generates M-Extension instructions.
######################################################################*/
class Virtual_M_Extension_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_M_Extension_Seq)

    Instruction_M_Extension_Sequence m_seq;

    function new(string name="Virtual_M_Extension_Seq");
        super.new(name);
    endfunction
    virtual task body();
        m_seq=Instruction_M_Extension_Sequence::type_id::create("m_seq");
        m_seq.num_transactions=31; 
        fork
            m_seq.start(p_sequencer.instr_sqr);
            #200;
        join

    endtask
endclass
