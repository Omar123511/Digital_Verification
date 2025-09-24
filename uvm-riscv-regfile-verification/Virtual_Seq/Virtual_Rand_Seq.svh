/*######################################################################
## Class Name: Virtual_Rand_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to start Instruction rand sequence and data memory seq.
######################################################################*/
class Virtual_Rand_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Rand_Seq)

    Instruction_addi_Sequence addi_seq;
    Data_Memory_Sequence data_seq;
    Instruction_rand_sequence rand_seq;
    Instruction_rst_Sequence rst_seq;
    
    function new(string name="Virtual_Rand_Seq");
        super.new(name);
    endfunction
    virtual task body();
        rand_seq=Instruction_rand_sequence::type_id::create("rand_seq");
        rand_seq.num_transactions=2500; 
        addi_seq=Instruction_addi_Sequence::type_id::create("addi_seq");
        addi_seq.num_transactions=31; 
        data_seq=Data_Memory_Sequence::type_id::create("data_seq");
	rst_seq=Instruction_rst_Sequence::type_id::create("rst_seq");
	rst_seq.num_transactions=31; 
        p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);// change the arbitration to take the priority of starting seq into consideration.
        fork
            begin
                data_seq.start(p_sequencer.data_memory_sqr);
            end
             begin 
                addi_seq.start(p_sequencer.instr_sqr,null,200);
                rand_seq.start(p_sequencer.instr_sqr,null,100);
             end
        join_none
        #35000;
        disable fork;
	rst_seq.start(p_sequencer.instr_sqr);

    endtask
    endclass

