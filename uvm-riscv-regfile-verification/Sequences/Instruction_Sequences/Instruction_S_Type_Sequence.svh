/*######################################################################
## Class Name: Instruction_S_Type_Sequence  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description: 
    .This sequence is used to generate various S-Type instructions. 
######################################################################*/
class Instruction_S_Type_Sequence extends Instruction_base_Sequence;
    `uvm_object_utils(Instruction_S_Type_Sequence)
    int num_transactions=31;
    Instruction_Seq_Item item;
    int count=0;
    int i=0;
    function new(string name="Instruction_S_Type_Sequence");
        super.new(name);
    endfunction
    virtual task body();
        super.body();
    endtask
    virtual task randomize_item();
        repeat(num_transactions)begin
            count=count+1;
            i=i+4;
            item=Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            `uvm_info("Instruction_S_Type_Sequence","seq is starting now",UVM_MEDIUM)
            
            assert(item.randomize() with{instruction_type==s_type;
                                        rs2==count;//rs1==0;
                                         imm==i;
                                        })
            else `uvm_fatal("Instruction_S_Type_Sequence","Randomization Failed")
            `uvm_info("Instruction_S_Type_Sequence","seq is randomized",UVM_MEDIUM)
            `uvm_info("Instruction_S_Type_Sequence", item.sprint(),UVM_HIGH)
            `uvm_info("Instruction_S_Type_Sequence","seq is finishing",UVM_MEDIUM)
            if(count==31)
                count=0;
            finish_item(item);
        end
    endtask
endclass