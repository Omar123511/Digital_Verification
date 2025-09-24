/*######################################################################
## Class Name: Instruction_zeros_ones_addi_sequence  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description: 
    This sequence is used to put different patterns of zeros and ones in registers using addi instruction.
######################################################################*/
class  Instruction_zeros_ones_addi_sequence extends Instruction_base_Sequence;
    `uvm_object_utils( Instruction_zeros_ones_addi_sequence)
    int num_transactions=31;
    Instruction_Seq_Item item;
    int count=0;
    int increment=0;
    function new(string name=" Instruction_zeros_ones_addi_sequence");
        super.new(name);
    endfunction
    virtual task body();
        super.body();
    endtask
    virtual task randomize_item();
        repeat(num_transactions)begin
            count=count+1;
            increment=increment+1;
            item=Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            `uvm_info(" Instruction_zeros_ones_addi_sequence","seq is starting now",UVM_MEDIUM)
            
            assert(item.randomize() with{instruction_type==i_type_reg;
                                        itype_reg==addi;$countones(imm)==count ; rd==increment;rs1==0;})
            else `uvm_fatal(" Instruction_zeros_ones_addi_sequence","Randomization Failed")
            `uvm_info(" Instruction_zeros_ones_addi_sequence","seq is randomized",UVM_MEDIUM)
            `uvm_info(" Instruction_zeros_ones_addi_sequence", item.sprint(),UVM_HIGH)
            `uvm_info(" Instruction_zeros_ones_addi_sequence","seq is finishing",UVM_MEDIUM)
            
            finish_item(item);
            if(increment==31)
                increment=0;
            if(count ==31)
                count=0;
        end
    endtask
endclass
