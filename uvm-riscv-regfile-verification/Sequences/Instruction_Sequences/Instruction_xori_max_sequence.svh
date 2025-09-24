/*######################################################################
## Class Name: Instruction_xori_max_sequence  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description: 
    This sequence is used to generate xori instructions with 0xFFF immediate, used within a virtual 
	sequence to  produce the maximum signed 32-bit value (0x7FFFFFFF).
######################################################################*/
class  Instruction_xori_max_sequence extends Instruction_base_Sequence;
    `uvm_object_utils( Instruction_xori_max_sequence)
    int num_transactions=31;
    Instruction_Seq_Item item;
    int count=0;
    function new(string name=" Instruction_xori_max_sequence");
        super.new(name);
    endfunction
    virtual task body();
        super.body();
    endtask
    virtual task randomize_item();
        
        repeat(num_transactions)begin
            
            item=Instruction_Seq_Item::type_id::create("item");
            count=count+1;
            start_item(item);
            `uvm_info(" Instruction_xori_max_sequence","seq is starting now",UVM_MEDIUM)
            assert(item.randomize() with{instruction_type==i_type_reg;
                                        itype_reg==xori;imm ==12'hfff; rd==count;rs1==count;})
            
            
            else `uvm_fatal(" Instruction_xori_max_sequence","Randomization Failed")
            `uvm_info(" Instruction_xori_max_sequence","seq is randomized",UVM_MEDIUM)
            `uvm_info(" Instruction_xori_max_sequence", item.sprint(),UVM_HIGH)
            `uvm_info(" Instruction_xori_max_sequence","seq is finishing",UVM_MEDIUM)
            
            if(count==31)
                count=0;
            finish_item(item);
            
            
        end
    endtask
endclass
