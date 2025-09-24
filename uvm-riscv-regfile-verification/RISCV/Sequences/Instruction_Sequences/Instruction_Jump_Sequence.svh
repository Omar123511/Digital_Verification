/*######################################################################
## Class Name: Instruction_Jump_Sequence  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description: 
    .This sequence is used to generate various jump instructions(jal,jalr). 
######################################################################*/
class Instruction_Jump_Sequence extends Instruction_base_Sequence;
    `uvm_object_utils(Instruction_Jump_Sequence)
    int num_transactions=31;
    Instruction_Seq_Item item;
    function new(string name="Instruction_Jump_Sequence");
        super.new(name);
    endfunction
    virtual task body();
        super.body();
    endtask
    virtual task randomize_item();
        repeat(num_transactions)begin
            item=Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            `uvm_info("Instruction_Jump_Sequence","seq is starting now",UVM_MEDIUM)
            
            assert(item.randomize() with{ instruction_type==j_type || instruction_type==i_type_jump;
                                         })
            else `uvm_fatal("Instruction_Jump_Sequence","Randomization Failed")
            `uvm_info("Instruction_Jump_Sequence","seq is randomized",UVM_MEDIUM)
            `uvm_info("Instruction_Jump_Sequence", item.sprint(),UVM_HIGH)
            `uvm_info("Instruction_Jump_Sequence","seq is finishing",UVM_MEDIUM)
            
            finish_item(item);
            
        end
    endtask
endclass
