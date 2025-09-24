/*######################################################################
## Class Name: Virtual_Store_Load_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence generates store and load operations.
    .It also starts a  Data_Memory_Sequence to simulate data memory transactions
    .It modifies the instruction sequencer arbitration mode to SEQ_ARB_STRICT_FIFO to control sequence execution priority.
######################################################################*/
class Virtual_Store_Load_Seq extends  Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Store_Load_Seq)

    Instruction_Load_Sequence itype_load_seq,itype_load_seq2;
    Instruction_S_Type_Sequence stype_seq,stype_seq2;
    Instruction_addi_Sequence addi_seq;
    
    Data_Memory_Sequence data_seq,data_seq2;

    function new(string name="Virtual_Store_Load_Seq");
        super.new(name);
    endfunction
    virtual task body();
        itype_load_seq=Instruction_Load_Sequence::type_id::create("itype_load_seq");
        itype_load_seq.num_transactions=31; 
        data_seq=Data_Memory_Sequence::type_id::create("data_seq");
        stype_seq=Instruction_S_Type_Sequence::type_id::create("stype_seq");
        stype_seq.num_transactions=31; 
	      itype_load_seq2=Instruction_Load_Sequence::type_id::create("itype_load_seq2");
        itype_load_seq2.num_transactions=31; 
        data_seq2=Data_Memory_Sequence::type_id::create("data_seq2");
        stype_seq2=Instruction_S_Type_Sequence::type_id::create("stype_seq2");
        stype_seq2.num_transactions=31; 

        addi_seq=Instruction_addi_Sequence::type_id::create("addi_seq");
        addi_seq.num_transactions=31; 
        p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);// change the arbitration to take the priority of starting seq into consideration.
        fork
            begin
             data_seq.start(p_sequencer.data_memory_sqr);
            end
             begin 
                stype_seq.start(p_sequencer.instr_sqr,null,300);
                
                itype_load_seq.start(p_sequencer.instr_sqr,null,50);
               #300;
             end
        join_none
        #4000;
        disable fork;
	    fork
            begin
             data_seq2.start(p_sequencer.data_memory_sqr);
            end
             begin 
		            addi_seq.start(p_sequencer.instr_sqr,null,200);
                stype_seq2.start(p_sequencer.instr_sqr,null,300);
                
                itype_load_seq2.start(p_sequencer.instr_sqr,null,50);
               #300;
             end
        join_none
        #4000;
        disable fork;

    endtask
    endclass
