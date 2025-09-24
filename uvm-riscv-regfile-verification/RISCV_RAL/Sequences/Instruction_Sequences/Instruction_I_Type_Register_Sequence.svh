/*######################################################################
## Class Name: Instruction_I_Type_Register_Sequence  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description: 
    .This sequence is used to generate various I-Type register instructions. 
######################################################################*/
class Instruction_I_Type_Register_Sequence extends Instruction_base_Sequence;
    `uvm_object_utils( Instruction_I_Type_Register_Sequence)
    int num_transactions=31;
    Instruction_Seq_Item item;
    function new(string name="Instruction_I_Type_Register_Sequence");
        super.new(name);
    endfunction
    virtual task body();
        super.body();
    endtask
    virtual task randomize_item();
        int count=0;
        repeat(num_transactions)begin
             count=count+1;
            item=Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            `uvm_info(" Instruction_I_Type_Register_Sequence","seq is starting now",UVM_MEDIUM)
            
            assert(item.randomize() with{instruction_type==i_type_reg;
                                         rd==count;rs1==count;})
            else `uvm_fatal(" Instruction_I_Type_Register_Sequence","Randomization Failed")
            `uvm_info(" Instruction_I_Type_Register_Sequence","seq is randomized",UVM_MEDIUM)
            `uvm_info(" Instruction_I_Type_Register_Sequence", item.sprint(),UVM_HIGH)
            `uvm_info(" Instruction_I_Type_Register_Sequence","seq is finishing",UVM_MEDIUM)
            if(count==31)
                count=0;
            finish_item(item);
           
        end
    endtask
endclass