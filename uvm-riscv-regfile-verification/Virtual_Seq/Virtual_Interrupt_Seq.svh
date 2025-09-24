/*######################################################################
## Class Name: Virtual_Interrupt_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to start interrupt sequences.
    
######################################################################*/
class Virtual_Interrupt_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Interrupt_Seq)

    Interrupt_Sequence interrupt_seq;
    
    function new(string name="Virtual_Interrupt_Seq");
        super.new(name);
    endfunction
    virtual task body();
        interrupt_seq=Interrupt_Sequence::type_id::create("interrupt_seq");
        fork
            interrupt_seq.start(p_sequencer.interrupt_sqr);
            #200;
        join

    endtask
    endclass