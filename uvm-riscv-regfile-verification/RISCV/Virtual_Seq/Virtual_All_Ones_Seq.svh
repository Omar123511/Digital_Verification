/*######################################################################
## Class Name: Virtual_All_Ones_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    This virtual sequence runs multiple instruction sequences, including 
    all-ones addi sequences, random instructions, data memory operations, 
    and M-extension instructions.
######################################################################*/
class Virtual_All_Ones_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_All_Ones_Seq)

    Instruction_all_ones_addi_sequence ones_seq, ones_seq2;
    Instruction_rand_sequence rand_seq;
    Data_Memory_Sequence data_seq;
    Instruction_M_Extension_Sequence m_seq;
    
    function new(string name="Virtual_All_Ones_Seq");
        super.new(name);
    endfunction
    virtual task body();
        ones_seq=Instruction_all_ones_addi_sequence::type_id::create("ones_seq");
        ones_seq.num_transactions=31; 
        ones_seq2=Instruction_all_ones_addi_sequence::type_id::create("ones_seq2");
        ones_seq2.num_transactions=31; 
        rand_seq=Instruction_rand_sequence::type_id::create("rand_seq");
        rand_seq.num_transactions=64;
        data_seq=Data_Memory_Sequence::type_id::create("data_seq");
        m_seq=Instruction_M_Extension_Sequence::type_id::create("m_seq");
        m_seq.num_transactions=31; 
        p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);// change the arbitration to take the priority of starting seq into consideration.
        fork
            begin
                data_seq.start(p_sequencer.data_memory_sqr);
            end
            begin 
		ones_seq.start(p_sequencer.instr_sqr,null,200);
                rand_seq.start(p_sequencer.instr_sqr,null,100);
                
            end
        join_none
        #5000;
        disable fork;
        ones_seq2.start(p_sequencer.instr_sqr);
        #300;
        m_seq.start(p_sequencer.instr_sqr);
        #100;

    endtask
    endclass

