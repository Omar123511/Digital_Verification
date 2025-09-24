/*######################################################################
## Class Name: Virtual_Max_Min_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to start max and min imm values sequence and then instruction rand seq.
######################################################################*/
class Virtual_Max_Min_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Max_Min_Seq)

    Instruction_max_min_addi_sequence max_min_seq,max_min_seq2;
    Instruction_rand_sequence rand_seq;
    Data_Memory_Sequence data_seq;
    Instruction_M_Extension_Sequence m_seq;
    function new(string name="Virtual_Max_Min_Seq");
        super.new(name);
    endfunction
    virtual task body();
        max_min_seq=Instruction_max_min_addi_sequence::type_id::create("max_min_seq");
        max_min_seq.num_transactions=31; 
        max_min_seq2=Instruction_max_min_addi_sequence::type_id::create("max_min_seq2");
        max_min_seq2.num_transactions=31; 
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
		            max_min_seq.start(p_sequencer.instr_sqr,null,200);
                rand_seq.start(p_sequencer.instr_sqr,null,100);
                
            end
        join_none
        #5000;
        disable fork;
        max_min_seq2.start(p_sequencer.instr_sqr);
        #300;
        m_seq.start(p_sequencer.instr_sqr);
        #100;
        

    endtask
    endclass

