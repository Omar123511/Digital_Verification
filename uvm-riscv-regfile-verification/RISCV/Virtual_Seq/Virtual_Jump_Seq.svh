/*######################################################################
## Class Name: Virtual_Jump_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence generates Jump instructions like jal and jalr.
######################################################################*/
class Virtual_Jump_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Jump_Seq)

    Instruction_Jump_Sequence jump_seq;
    Instruction_addi_Sequence addi_seq;
    function new(string name="Virtual_Jump_Seq");
        super.new(name);
    endfunction
    virtual task body();
        jump_seq=Instruction_Jump_Sequence::type_id::create("jump_seq");
        jump_seq.num_transactions=31; 
        addi_seq=Instruction_addi_Sequence::type_id::create("addi_seq");
        addi_seq.num_transactions=31; 
         p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);// change the arbitration to take the priority of starting seq into consideration.
        fork
            addi_seq.start(p_sequencer.instr_sqr,null,200);
            jump_seq.start(p_sequencer.instr_sqr,null,100);
        join_none
	#4000;
	disable fork;

    endtask
    endclass
