/*######################################################################
## Class Name: Instruction_rand_sequence  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description: 
    This sequence is random to generate different format types to be used in rand test.
######################################################################*/
class  Instruction_rand_sequence extends Instruction_base_Sequence;
    `uvm_object_utils( Instruction_rand_sequence)
    int num_transactions=31;
    Instruction_Seq_Item item;
    function new(string name=" Instruction_rand_sequence");
        super.new(name);
    endfunction
    virtual task body();
        super.body();
    endtask
    virtual task randomize_item();
        repeat(num_transactions)begin
            item=Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            `uvm_info(" Instruction_rand_sequence","seq is starting now",UVM_MEDIUM)
            
            assert(item.randomize() with {})
            else `uvm_fatal(" Instruction_rand_sequence","Randomization Failed")
            `uvm_info(" Instruction_rand_sequence","seq is randomized",UVM_MEDIUM)
            `uvm_info(" Instruction_rand_sequence", item.sprint(),UVM_HIGH)
            `uvm_info(" Instruction_rand_sequence","seq is finishing",UVM_MEDIUM)
            
            finish_item(item);
        end
    endtask
endclass
