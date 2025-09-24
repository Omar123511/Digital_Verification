/*######################################################################
## Class Name: Virtual_Signed_Min_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to start signed min seq  to generate the min signed values in all registers.
######################################################################*/
class Virtual_Signed_Min_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Signed_Min_Seq)

    Instruction_signed_min_sequence min_seq;
    
    function new(string name="Virtual_Signed_Min_Seq");
        super.new(name);
    endfunction
    virtual task body();
        min_seq=Instruction_signed_min_sequence::type_id::create("min_seq");
        min_seq.num_transactions=31;
       
        min_seq.start(p_sequencer.instr_sqr);
            

    endtask
    endclass
