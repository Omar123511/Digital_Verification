/*######################################################################
## Class Name: Instruction_corner_Cases_r_seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description: 
    This sequence is used to generate R-type instructions with controlled register patterns. 
    It will be Used by a virtual sequence to apply corner-case operand values.
######################################################################*/
class  Instruction_corner_Cases_r_seq extends Instruction_base_Sequence;
    `uvm_object_utils( Instruction_corner_Cases_r_seq)
    int num_transactions=31;
    Instruction_Seq_Item item;
    int count=15;
    int i=0;
    function new(string name=" Instruction_corner_Cases_r_seq");
        super.new(name);
    endfunction
    virtual task body();
        super.body();
    endtask
    virtual task randomize_item();
        
        repeat(num_transactions)begin
            count=count+1;
            i=i+1;
            item=Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            `uvm_info("Instruction_corner_Cases_r_seq","seq is starting now",UVM_MEDIUM)
            
            assert(item.randomize() with{instruction_type==r_type;
					  rtype inside {sub,and_op,or_op,sltu,slt};
                                         rd==count;rs1==i;rs2==15-i;})
            else `uvm_fatal("Instruction_corner_Cases_r_seq","Randomization Failed")
            `uvm_info("Instruction_corner_Cases_r_seq","seq is randomized",UVM_MEDIUM)
            `uvm_info("Instruction_corner_Cases_r_seq", item.sprint(),UVM_HIGH)
            `uvm_info("Instruction_corner_Cases_r_seq","seq is finishing",UVM_MEDIUM)
            if(count==31)
                count=15;
            if(i==7)
              i=0;
            finish_item(item);
	end
	
    endtask
endclass
