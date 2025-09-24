//------------------------------------------------------------------------------------
// Nourhan Mohammed
// UVM Test Sequences for RISC-V Processor Hazard Detection
// 
// This file contains test sequences designed to verify the processor's handling of
// various pipeline hazards including RAW, WAR, WAW, and load-use dependencies.
// Each sequence targets a specific hazard scenario to validate the processor's
// hazard detection and stall mechanisms.
//------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------
class instruction_seq_RAW_ALU_dependency extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_RAW_ALU_dependency)
    Instruction_addi_Sequence addi_seq1;
    Instruction_addi_Sequence addi_seq2;
    Instruction_R_Type_Sequence add_seq;
    
    function new(string name="instruction_seq_WAR_no_stall");
        super.new(name);
    endfunction
    
    virtual task body();
        addi_seq1 = Instruction_addi_Sequence::type_id::create("addi_seq1");
        addi_seq2 = Instruction_addi_Sequence::type_id::create("addi_seq2");
        add_seq = Instruction_R_Type_Sequence::type_id::create("add_seq");
        
        addi_seq1.num_transactions = 1;
        addi_seq2.num_transactions = 1;
        add_seq.num_transactions = 1;
        
        // Remove the randomization constraints from the sequences
        // and set the values directly
        addi_seq1.item = Instruction_Seq_Item::type_id::create("item");
        addi_seq1.item.instruction_type = i_type_reg;
        addi_seq1.item.itype_reg = addi;
        addi_seq1.item.rd = 1;
        addi_seq1.item.rs1 = 0;
        addi_seq1.item.imm = 5;
        
        addi_seq2.item = Instruction_Seq_Item::type_id::create("item");
        addi_seq2.item.instruction_type = i_type_reg;
        addi_seq2.item.itype_reg = addi;
        addi_seq2.item.rd = 2;
        addi_seq2.item.rs1 = 1;
        addi_seq2.item.imm = 10;
        
        add_seq.item = Instruction_Seq_Item::type_id::create("item");
        add_seq.item.instruction_type = r_type;
        add_seq.item.rtype = add;
        add_seq.item.rd = 3;
        add_seq.item.rs1 = 1;
        add_seq.item.rs2 = 2;
        
        fork
            addi_seq1.start(p_sequencer.instr_sqr);
            #200;
            addi_seq2.start(p_sequencer.instr_sqr);
            #200;
            add_seq.start(p_sequencer.instr_sqr);
            #200;
        join
 	
    endtask
endclass

class instruction_seq_WAR_no_stall extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_WAR_no_stall)

    Instruction_addi_Sequence addi_seq1;
    Instruction_addi_Sequence addi_seq2;
    Instruction_addi_Sequence addi_seq3;
    
    function new(string name="instruction_seq_WAR_no_stall");
        super.new(name);
    endfunction
    
    virtual task body();
        addi_seq1 = Instruction_addi_Sequence::type_id::create("addi_seq1");
        addi_seq2 = Instruction_addi_Sequence::type_id::create("addi_seq2");
        addi_seq3 = Instruction_addi_Sequence::type_id::create("addi_seq3");
        
        addi_seq1.num_transactions = 1;
        addi_seq2.num_transactions = 1;
        addi_seq3.num_transactions = 1;
        
        // Set values directly instead of using randomization
        addi_seq1.item = Instruction_Seq_Item::type_id::create("item");
        addi_seq1.item.instruction_type = i_type_reg;
        addi_seq1.item.itype_reg = addi;
        addi_seq1.item.rd = 1;
        addi_seq1.item.rs1 = 0;
        addi_seq1.item.imm = 5;
        
        addi_seq2.item = Instruction_Seq_Item::type_id::create("item");
        addi_seq2.item.instruction_type = i_type_reg;
        addi_seq2.item.itype_reg = addi;
        addi_seq2.item.rd = 2;
        addi_seq2.item.rs1 = 1;
        addi_seq2.item.imm = 10;
        
        addi_seq3.item = Instruction_Seq_Item::type_id::create("item");
        addi_seq3.item.instruction_type = i_type_reg;
        addi_seq3.item.itype_reg = addi;
        addi_seq3.item.rd = 1;
        addi_seq3.item.rs1 = 2;
        addi_seq3.item.imm = 15;
        
        fork
            addi_seq1.start(p_sequencer.instr_sqr);
            #200;
            addi_seq2.start(p_sequencer.instr_sqr);
            #200;
            addi_seq3.start(p_sequencer.instr_sqr);
            #200;
        join
    endtask
endclass

class instruction_seq_WAW_register_clobber extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_WAW_register_clobber)

    Instruction_M_Extension_Sequence mul_seq;
    Instruction_addi_Sequence addi_seq;
    
    function new(string name="instruction_seq_WAW_register_clobber");
        super.new(name);
    endfunction
    
    virtual task body();
        mul_seq = Instruction_M_Extension_Sequence::type_id::create("mul_seq");
        addi_seq = Instruction_addi_Sequence::type_id::create("addi_seq");
        
        mul_seq.num_transactions = 1;
        addi_seq.num_transactions = 1;
        
        // Set values directly
        mul_seq.item = Instruction_Seq_Item::type_id::create("item");
        mul_seq.item.instruction_type = r_type;
        mul_seq.item.m_instr = mul;
        mul_seq.item.rd = 1;
        mul_seq.item.rs1 = 2;
        mul_seq.item.rs2 = 3;
        
        addi_seq.item = Instruction_Seq_Item::type_id::create("item");
        addi_seq.item.instruction_type = i_type_reg;
        addi_seq.item.itype_reg = addi;
        addi_seq.item.rd = 1;
        addi_seq.item.rs1 = 4;
        addi_seq.item.imm = 10;
        
        fork
            mul_seq.start(p_sequencer.instr_sqr);
            #300;
            addi_seq.start(p_sequencer.instr_sqr);
            #200;
        join
    endtask
endclass

class instruction_seq_LoadUse_stall extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_LoadUse_stall)

    Instruction_Load_Sequence load_seq;
    Instruction_R_Type_Sequence add_seq;
    Data_Memory_Sequence seq;
    
    function new(string name="instruction_seq_LoadUse_stall");
        super.new(name);
    endfunction
    
    virtual task body();
        load_seq = Instruction_Load_Sequence::type_id::create("load_seq");
        add_seq = Instruction_R_Type_Sequence::type_id::create("add_seq");
	seq=Data_Memory_Sequence::type_id::create("seq");
        p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);
        
        load_seq.num_transactions = 1;
        add_seq.num_transactions = 1;
        
        // Set values directly
        load_seq.item = Instruction_Seq_Item::type_id::create("item");
        load_seq.item.instruction_type = i_type_load;
        // Set appropriate load instruction type (lw, lh, lb, etc.)
        load_seq.item.itype_load = lw; 
        load_seq.item.rd = 1;
        load_seq.item.rs1 = 2;
        load_seq.item.imm = 0;
        
        add_seq.item = Instruction_Seq_Item::type_id::create("item");
        add_seq.item.instruction_type = r_type;
        add_seq.item.rtype = add;
        add_seq.item.rd = 3;
        add_seq.item.rs1 = 1;
        add_seq.item.rs2 = 4;
        
        fork
	  begin 
		seq.start(p_sequencer.data_memory_sqr);
	  end
          begin
            load_seq.start(p_sequencer.instr_sqr);
            #500;
            add_seq.start(p_sequencer.instr_sqr);
            #100;
           end
        join_none
        #4000;
	disable fork;
    endtask
endclass
//------------------------------------------------------------------------------------
// Sequence: instruction_seq_StoreAfterLoad (Deterministic)
// Description: Tests store-after-load with specific registers and values
//------------------------------------------------------------------------------------
class instruction_seq_StoreAfterLoad extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_StoreAfterLoad)
    Instruction_Load_Sequence load_seq;
    Instruction_S_Type_Sequence store_seq;

    function new(string name="instruction_seq_StoreAfterLoad");
        super.new(name);
    endfunction

    virtual task body();
        // Set strict FIFO arbitration
        p_sequencer.instr_sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);
        
        // Create and configure load sequence
        load_seq = Instruction_Load_Sequence::type_id::create("load_seq");
        load_seq.num_transactions = 1;
        load_seq.item = Instruction_Seq_Item::type_id::create("item");
        load_seq.item.instruction_type = i_type_load;
        load_seq.item.itype_load = lw;  // Assuming lw is defined
        load_seq.item.rd = 5;           // x5 will receive loaded value
        load_seq.item.rs1 = 3;          // Base address in x3
        load_seq.item.imm = 0;
        

        // Create and configure store sequence
        store_seq = Instruction_S_Type_Sequence::type_id::create("store_seq");
        store_seq.num_transactions = 1;
        store_seq.item = Instruction_Seq_Item::type_id::create("item");
        store_seq.item.instruction_type = s_type;
        store_seq.item.stype = sw;      // Assuming sw is defined
        store_seq.item.rs1 = 4;         // Different base address
        store_seq.item.rs2 = 5;         // Store the value we just loaded (x5)
        store_seq.item.imm = 0;
       
	fork
            load_seq.start(p_sequencer.instr_sqr);
            #300;
            store_seq.start(p_sequencer.instr_sqr);
            #200;
        join_none
        #4000;
	disable fork;
    endtask
endclass

//------------------------------------------------------------------------------------
// Sequence: instruction_seq_RAW_MUL_to_ADD (Deterministic)
// Description: Tests RAW hazard between multi-cycle MUL and ADD with specific regs
//------------------------------------------------------------------------------------
class instruction_seq_RAW_MUL_to_ADD extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_RAW_MUL_to_ADD)
    Instruction_M_Extension_Sequence mul_seq;
    Instruction_R_Type_Sequence add_seq;

    function new(string name="instruction_seq_RAW_MUL_to_ADD");
        super.new(name);
    endfunction

    virtual task body();
        // Create and configure MUL sequence
        mul_seq = Instruction_M_Extension_Sequence::type_id::create("mul_seq");
        mul_seq.num_transactions = 1;
        mul_seq.item = Instruction_Seq_Item::type_id::create("item");
        mul_seq.item.instruction_type = r_type;
        mul_seq.item.m_instr = mul;
        mul_seq.item.rd = 6;            // Result will be in x6
        mul_seq.item.rs1 = 2;           // x2 * x3
        mul_seq.item.rs2 = 3;
        

        // Create and configure ADD sequence
        add_seq = Instruction_R_Type_Sequence::type_id::create("add_seq");
        add_seq.num_transactions = 1;
        add_seq.item = Instruction_Seq_Item::type_id::create("item");
        add_seq.item.instruction_type = r_type;
        add_seq.item.rtype = add;
        add_seq.item.rd = 7;            // Result in x7
        add_seq.item.rs1 = 6;            // RAW dependency on MUL result (x6)
        add_seq.item.rs2 = 4;
        fork
            mul_seq.start(p_sequencer.instr_sqr);
            #300;
            add_seq.start(p_sequencer.instr_sqr);
            #200;
        join
    endtask
endclass

//------------------------------------------------------------------------------------
// Sequence: instruction_seq_Forwarding (Deterministic)
// Description: Tests ALU result forwarding with specific registers and values
//------------------------------------------------------------------------------------
class instruction_seq_Forwarding extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_Forwarding)
    Instruction_addi_Sequence addi_seq;
    Instruction_R_Type_Sequence add_seq;

    function new(string name="instruction_seq_Forwarding");
        super.new(name);
    endfunction

    virtual task body();
        // Create and configure ADDI sequence
        addi_seq = Instruction_addi_Sequence::type_id::create("addi_seq");
        addi_seq.num_transactions = 1;
        addi_seq.item = Instruction_Seq_Item::type_id::create("item");
        addi_seq.item.instruction_type = i_type_reg;
        addi_seq.item.itype_reg = addi;
        addi_seq.item.rd = 8;           // Result in x8
        addi_seq.item.rs1 = 0;          // x0 (hardwired zero)
        addi_seq.item.imm = 42;         // x8 = 0 + 42
       

        // Create and configure ADD sequence
        add_seq = Instruction_R_Type_Sequence::type_id::create("add_seq");
        add_seq.num_transactions = 1;
        add_seq.item = Instruction_Seq_Item::type_id::create("item");
        add_seq.item.instruction_type = r_type;
        add_seq.item.rtype = add;
        add_seq.item.rd = 9;            // Result in x9
        add_seq.item.rs1 = 8;           // Forwarding test (uses x8 just computed)
        add_seq.item.rs2 = 1;
       
        fork
            addi_seq.start(p_sequencer.instr_sqr);
            #300;
            add_seq.start(p_sequencer.instr_sqr);
            #200;
        join
    endtask
endclass
