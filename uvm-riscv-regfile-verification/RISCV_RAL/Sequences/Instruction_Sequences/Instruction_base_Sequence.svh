/*######################################################################
## Class Name: Instruction_base_Sequence  
## Engineer : Omnia Mohamed
## Date: April 2025
## Description: 
    This sequence is used to initialize all registers with all zeros value using addi instruction.
######################################################################*/
class Instruction_base_Sequence extends uvm_sequence#(Instruction_Seq_Item);
    `uvm_object_utils(Instruction_base_Sequence)
    int num_transactions=31;
    Instruction_Seq_Item item;
    int count1=0;
    function new(string name="Instruction_base_Sequence");
        super.new(name);
    endfunction
    virtual task body();
        randomize_item();
    endtask
    virtual task randomize_item();
        
        repeat(num_transactions)begin
            count1=count1+1;
            item=Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            `uvm_info("Instruction_base_Sequence","seq is starting now",UVM_MEDIUM)
            
            assert(item.randomize() with{instruction_type==i_type_reg;
                                        itype_reg==addi;imm==12'h000; rd==count1;rs1==0;
			})
            else `uvm_fatal("Instruction_base_Sequence","Randomization Failed")
            `uvm_info("Instruction_base_Sequence","seq is randomized",UVM_MEDIUM)
            `uvm_info("Instruction_base_Sequence", item.sprint(),UVM_HIGH)
            `uvm_info("Instruction_base_Sequence","seq is finishing",UVM_MEDIUM)
            if(count1==31)
                count1=0;
            finish_item(item);
            
        end
    endtask
endclass
