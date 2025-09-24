/*######################################################################
## Class Name: Virtual_addi_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to generate addi instructions to fill the registers with random values.
######################################################################*/
class Virtual_addi_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_addi_Seq)

    Instruction_addi_Sequence addi_seq;
    
    function new(string name="Virtual_addi_Seq");
        super.new(name);

    endfunction
    virtual task body();
        addi_seq=Instruction_addi_Sequence::type_id::create("addi_seq");
        addi_seq.num_transactions=31; 
        fork
            addi_seq.start(p_sequencer.instr_sqr);
           
        join

    endtask
endclass
