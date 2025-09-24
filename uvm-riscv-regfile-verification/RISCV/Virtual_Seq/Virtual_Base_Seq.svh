/*######################################################################
## Class Name: Virtual_Base_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to start all Initialization sequences,
    including configuration, debug seq(normal operation), base instruction sequence(initialize all registers), and no interrupt seq.
######################################################################*/
class Virtual_Base_Seq extends uvm_sequence #(uvm_sequence_item);
    `uvm_object_utils(Virtual_Base_Seq)
    `uvm_declare_p_sequencer(Virtual_Sequencer)

    Configuration_Sequencer config_sqr;
    Instruction_Sequencer instr_sqr;
    Data_Memory_Sequencer data_memory_sqr;
    Debug_Sequencer debug_sqr;

    Instruction_base_Sequence base_seq;
    Configuration_Sequence init_seq;
    Debug_Sequence debug_seq;
    No_Interrupt_Sequence no_interrupt_seq;
    
    function new(string name="Virtual_Base_Seq");
        super.new(name);
    endfunction
    virtual task body();
        base_seq=Instruction_base_Sequence::type_id::create("base_seq");
        base_seq.num_transactions=31; 
        init_seq=Configuration_Sequence::type_id::create("init_seq");
        debug_seq=Debug_Sequence::type_id::create("debug_seq");
        no_interrupt_seq=No_Interrupt_Sequence::type_id::create("no_interrupt_seq");
        fork
            init_seq.start(p_sequencer.config_sqr);
            debug_seq.start(p_sequencer.debug_sqr);
            base_seq.start(p_sequencer.instr_sqr);
            no_interrupt_seq.start(p_sequencer.interrupt_sqr);
        join

    endtask
    endclass
