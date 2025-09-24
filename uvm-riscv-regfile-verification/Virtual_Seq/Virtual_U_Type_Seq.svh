/*######################################################################
## Class Name: Virtual_U_Type_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is responsible for generating U-Type instructions (LUI, AUIPC) using Instruction_U_Type_Sequence,
    .it also executes some ADDI instruction to test instruction mix scenarios.
    . It modifies the instruction sequencer arbitration mode to SEQ_ARB_STRICT_FIFO to control sequence execution priority.
######################################################################*/
class Virtual_U_Type_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_U_Type_Seq)

    Instruction_U_Type_Sequence utype_seq;
    Instruction_addi_Sequence addi_seq;
    function new(string name="Virtual_U_Type_Seq");
        super.new(name);
    endfunction
    virtual task body();
        utype_seq=Instruction_U_Type_Sequence::type_id::create("utype_seq");
        utype_seq.num_transactions=31; 
        addi_seq=Instruction_addi_Sequence::type_id::create("addi_seq");
        addi_seq.num_transactions=31; 
         p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);// change the arbitration to take the priority of starting seq into consideration.
        fork
            addi_seq.start(p_sequencer.instr_sqr,null,200);
            utype_seq.start(p_sequencer.instr_sqr,null,100);
        join

    endtask
    endclass
