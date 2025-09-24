/*######################################################################
## Class Name: Virtual_S_Type_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence generates store operations.
    .It also starts a  Data_Memory_Sequence to simulate data memory transactions
    .It modifies the instruction sequencer arbitration mode to SEQ_ARB_STRICT_FIFO to control sequence execution priority.
######################################################################*/
class Virtual_S_Type_Seq extends  Virtual_Base_Seq;
    `uvm_object_utils(Virtual_S_Type_Seq)

    Instruction_S_Type_Sequence stype_seq;
    Instruction_addi_Sequence addi_seq;
    Data_Memory_Sequence data_seq;

    function new(string name="Virtual_S_Type_Seq");
        super.new(name);
    endfunction
    virtual task body();
        stype_seq=Instruction_S_Type_Sequence::type_id::create("stype_seq");
        stype_seq.num_transactions=31; 
        data_seq=Data_Memory_Sequence::type_id::create("data_seq");
        addi_seq=Instruction_addi_Sequence::type_id::create("addi_seq");
        addi_seq.num_transactions=31; 
        p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);// change the arbitration to take the priority of starting seq into consideration.
        
        fork
            begin
                data_seq.start(p_sequencer.data_memory_sqr);
            end
             begin 
                addi_seq.start(p_sequencer.instr_sqr,null,200);
                stype_seq.start(p_sequencer.instr_sqr,null,100);
             end
            join_none
            #3000;
            disable fork;

    endtask
    endclass
