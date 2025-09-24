/*######################################################################
## Class Name: Virtual_Zeros_Ones_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to start Instruction zeros and ones sequence.
######################################################################*/
class Virtual_Zeros_Ones_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Zeros_Ones_Seq)

    Instruction_zeros_ones_addi_sequence zeros_ones_seq;
    Instruction_rand_sequence rand_seq;
    Data_Memory_Sequence data_seq;
    
    function new(string name="Virtual_Zeros_Ones_Seq");
        super.new(name);
    endfunction
    virtual task body();
        zeros_ones_seq=Instruction_zeros_ones_addi_sequence::type_id::create("zeros_ones_seq");
        zeros_ones_seq.num_transactions=31; 
        rand_seq=Instruction_rand_sequence::type_id::create("rand_seq");
        rand_seq.num_transactions=64;
        data_seq=Data_Memory_Sequence::type_id::create("data_seq");
        p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);// change the arbitration to take the priority of starting seq into consideration.
        fork
            begin
                data_seq.start(p_sequencer.data_memory_sqr);
            end
            begin 
		zeros_ones_seq.start(p_sequencer.instr_sqr,null,200);
                rand_seq.start(p_sequencer.instr_sqr,null,100);
                
            end
        join_none
        #5000;
        disable fork;

    endtask
    endclass

