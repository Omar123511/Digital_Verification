/*######################################################################
## Class Name: Virtual_Signed_Max_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to start signed min seq and then signed max seq to generate the max signed values in all registers.
######################################################################*/
class Virtual_Signed_Max_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Signed_Max_Seq)

    Instruction_xori_max_sequence max_seq;
    Instruction_signed_min_sequence min_seq;
    
    function new(string name="Virtual_Signed_Max_Seq");
        super.new(name);
    endfunction
    virtual task body();
        max_seq=Instruction_xori_max_sequence::type_id::create("max_seq");
        max_seq.num_transactions=31;
        min_seq=Instruction_signed_min_sequence::type_id::create("min_seq");
        min_seq.num_transactions=31;
        p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);// change the arbitration to take the priority of starting seq into consideration.
        fork
             begin 
                min_seq.start(p_sequencer.instr_sqr,null,200);
                max_seq.start(p_sequencer.instr_sqr,null,50);
                #200;
             end
        join

    endtask
    endclass
