
//------------------------------------------------------------------------------------
// Nourhan Mohammed
// UVM Test Sequences for RISC-V Processor Hazard Detection
// 
// This file contains comprehensive test sequences designed to verify:
// - Pipeline hazard detection (RAW, WAR, WAW)
// - Forwarding paths
// - Load-use stalls
// - Memory disambiguation
// - Multi-cycle operation handling
// Each sequence includes precise timing controls and detailed comments about
// the expected processor behavior and verification objectives.
//------------------------------------------------------------------------------------

// Base sequence class with dependency handling
class Instruction_base_Seq extends uvm_sequence#(Instruction_Seq_Item);
    `uvm_object_utils(Instruction_base_Seq)
    
    // Configuration parameters
    int num_transactions = 1;        // Number of transactions to generate
    Instruction_Seq_Item item;       // Sequence item handle
    
    // Dependency control fields
    logic [4:0] dep_reg1 = 0;       // First dependency register
    logic [4:0] dep_reg2 = 0;       // Second dependency register
    bit use_dependencies = 0;        // Flag to enable dependency constraints
    
    function new(string name="Instruction_base_Seq");
        super.new(name);
    endfunction
    
    virtual task body();
        randomize_item();
    endtask
    
    // Virtual method to be overridden by child classes
    virtual task randomize_item();
        // Base class implementation empty
    endtask
endclass

//------------------------------------------------------
// ADDI Instruction Sequence
// Purpose: Generates ADDI instructions with optional register dependencies
//------------------------------------------------------
class Instruction_addi_Seq extends Instruction_base_Seq;
    `uvm_object_utils(Instruction_addi_Seq)
    
    function new(string name="Instruction_addi_Seq");
        super.new(name);
        dep_reg1 = 0;  // Initialize dependency registers
        dep_reg2 = 0;
    endfunction
    
    virtual task randomize_item();
        repeat(num_transactions) begin
            item = Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            
            if (!use_dependencies) begin
                // Random ADDI without dependencies
                assert(item.randomize() with {
                    instruction_type == i_type_reg;
                    itype_reg == addi;
                }) else `uvm_fatal("RAND_FAIL", "ADDI randomization failed");
            end
            else begin
                // ADDI with register dependency constraints
                assert(item.randomize() with {
                    instruction_type == i_type_reg;
                    itype_reg == addi;
                    rs1 == local::dep_reg1;    // Use specified source register
                    rd != local::dep_reg1;      // Destination different from source
                    rd inside {[1:31]};         // Valid destination register
                    imm inside {[1:100]};      // Reasonable immediate value
                }) else `uvm_fatal("RAND_FAIL", "ADDI dependency randomization failed");
            end
            
            finish_item(item);
        end
    endtask
endclass

//------------------------------------------------------
// R-Type Instruction Sequence
// Purpose: Generates R-type ALU instructions with optional dependencies
//------------------------------------------------------
class Instruction_R_Type_Seq extends Instruction_base_Seq;
    `uvm_object_utils(Instruction_R_Type_Seq)
    
    function new(string name="Instruction_R_Type_Seq");
        super.new(name);
        dep_reg1 = 0;
        dep_reg2 = 0;
    endfunction
    
    virtual task randomize_item();
        repeat(num_transactions) begin
            item = Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            
            if (!use_dependencies) begin
                // Random R-type instruction
                assert(item.randomize() with {
                    instruction_type == r_type;
                }) else `uvm_fatal("RAND_FAIL", "R-Type randomization failed");
            end
            else begin
                // R-type with register dependencies
                assert(item.randomize() with {
                    instruction_type == r_type;
                    rs1 == local::dep_reg1;    // First source operand
                    rs2 == local::dep_reg2;    // Second source operand
                    rd != local::dep_reg1;      // Destination different from sources
                    rd != local::dep_reg2;
                    rd inside {[1:31]};         // Valid destination
                    funct3 == add;              // Use ADD operation
                }) else `uvm_fatal("RAND_FAIL", "R-Type dependency randomization failed");
            end
            
            finish_item(item);
        end
    endtask
endclass

//------------------------------------------------------
// B-Type Instruction Sequence
// Purpose: Generates branch instructions with optional dependencies
//------------------------------------------------------
class Instruction_B_Type_Seq extends Instruction_base_Seq;
    `uvm_object_utils(Instruction_B_Type_Seq)
    
    function new(string name="Instruction_B_Type_Seq");
        super.new(name);
        dep_reg1 = 0;
        dep_reg2 = 0;
    endfunction
    
    virtual task randomize_item();
        repeat(num_transactions) begin
            item = Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            
            if (!use_dependencies) begin
                // Random branch instruction
                assert(item.randomize() with {
                    instruction_type == b_type;
                }) else `uvm_fatal("RAND_FAIL", "B-Type randomization failed");
            end
            else begin
                // Branch with register dependencies
                assert(item.randomize() with {
                    instruction_type == b_type;
                    rs1 == local::dep_reg1;      // First compare operand
                    rs2 == local::dep_reg2;      // Second compare operand
                    btype == beq;                // Use BEQ for consistency
                    imm inside {[-100:100]};     // Reasonable branch offset
                }) else `uvm_fatal("RAND_FAIL", "B-Type dependency randomization failed");
            end
            
            finish_item(item);
        end
    endtask
endclass

//------------------------------------------------------
// Load Instruction Sequence
// Purpose: Generates load instructions with optional dependencies
//------------------------------------------------------
class Instruction_Load_Seq extends Instruction_base_Seq;
    `uvm_object_utils(Instruction_Load_Seq)
    
    function new(string name="Instruction_Load_Seq");
        super.new(name);
        dep_reg1 = 0;
        dep_reg2 = 0;
    endfunction
    
    virtual task randomize_item();
        repeat(num_transactions) begin
            item = Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            
            if (!use_dependencies) begin
                // Random load instruction
                assert(item.randomize() with {
                    instruction_type == i_type_load;
                }) else `uvm_fatal("RAND_FAIL", "Load randomization failed");
            end
            else begin
                // Load with register dependency
                assert(item.randomize() with {
                    instruction_type == i_type_load;
                    itype_load == lw;           // Use LW for consistency
                    rs1 == local::dep_reg1;     // Base address register
                    rd != local::dep_reg1;      // Destination different from base
                    rd inside {[1:31]};         // Valid destination
                    imm == 0;                   // Simple offset for testing
                }) else `uvm_fatal("RAND_FAIL", "Load dependency randomization failed");
            end
            
            finish_item(item);
        end
    endtask
endclass

//------------------------------------------------------
// Store Instruction Sequence
// Purpose: Generates store instructions with optional dependencies
//------------------------------------------------------
class Instruction_S_Type_Seq extends Instruction_base_Seq;
    `uvm_object_utils(Instruction_S_Type_Seq)
    
    function new(string name="Instruction_S_Type_Seq");
        super.new(name);
        dep_reg1 = 0;
        dep_reg2 = 0;
    endfunction
    
    virtual task randomize_item();
        repeat(num_transactions) begin
            item = Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            
            if (!use_dependencies) begin
                // Random store instruction
                assert(item.randomize() with {
                    instruction_type == s_type;
                }) else `uvm_fatal("RAND_FAIL", "Store randomization failed");
            end
            else begin
                // Store with register dependencies
                assert(item.randomize() with {
                    instruction_type == s_type;
                    stype == sw;                // Use SW for consistency
                    rs1 == local::dep_reg1;     // Base address register
                    rs2 == local::dep_reg2;     // Value to store
                    imm == 0;                  // Simple offset for testing
                }) else `uvm_fatal("RAND_FAIL", "Store dependency randomization failed");
            end
            
            finish_item(item);
        end
    endtask
endclass

//------------------------------------------------------
// M-Extension Instruction Sequence
// Purpose: Generates multiply/divide instructions with optional dependencies
//------------------------------------------------------
class Instruction_M_Extension_Seq extends Instruction_base_Seq;
    `uvm_object_utils(Instruction_M_Extension_Seq)
    
    function new(string name="Instruction_M_Extension_Seq");
        super.new(name);
        dep_reg1 = 0;
        dep_reg2 = 0;
    endfunction
    
    virtual task randomize_item();
        repeat(num_transactions) begin
            item = Instruction_Seq_Item::type_id::create("item");
            start_item(item);
            
            if (!use_dependencies) begin
                // Random M-extension instruction
                assert(item.randomize() with {
                    instruction_type == m_extension;
                }) else `uvm_fatal("RAND_FAIL", "M-Extension randomization failed");
            end
            else begin
                // M-extension with register dependencies
                assert(item.randomize() with {
                    instruction_type == m_extension;
                    m_instr == mul;             // Use MUL for consistency
                    rs1 == local::dep_reg1;     // First operand
                    rs2 == local::dep_reg2;     // Second operand
                    rd inside {[1:31]};         // Valid destination
                    rd != local::dep_reg1;      // Destination different from sources
                    rd != local::dep_reg2;
                }) else `uvm_fatal("RAND_FAIL", "M-Extension dependency randomization failed");
            end
            
            finish_item(item);
        end
    endtask
endclass

//------------------------------------------------------
// RAW ALU Dependency Sequence
// Purpose: Creates a Read-After-Write hazard between ALU instructions
// Description: 
//   1. First ADDI writes to a register
//   2. Second ADDI reads that register
//   3. ADD reads both ADDI results
// Tests: Forwarding paths for ALU operations
//------------------------------------------------------
class instruction_seq_RAW_ALU_dependency extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_RAW_ALU_dependency)
    Instruction_addi_Seq addi_seq1, addi_seq2;
    Instruction_R_Type_Seq add_seq;
    
    function new(string name="instruction_seq_RAW_ALU_dependency");
        super.new(name);
    endfunction
    
    virtual task body();
        addi_seq1 = Instruction_addi_Seq::type_id::create("addi_seq1");
        addi_seq2 = Instruction_addi_Seq::type_id::create("addi_seq2");
        add_seq = Instruction_R_Type_Seq::type_id::create("add_seq");
        
        fork
            begin // First ADDI - producer
                addi_seq1.use_dependencies = 1;
                addi_seq1.dep_reg1 = 0; // x0 as source
                addi_seq1.start(p_sequencer.instr_sqr);
            end
            
            begin // Second ADDI - first consumer
                #100; // Small delay to ensure ordering
                addi_seq2.use_dependencies = 1;
                addi_seq2.dep_reg1 = addi_seq1.item.rd; // Read after first ADDI
                addi_seq2.start(p_sequencer.instr_sqr);
            end
            
            begin // ADD - second consumer
                #200; // Additional delay
                add_seq.use_dependencies = 1;
                add_seq.dep_reg1 = addi_seq1.item.rd; // First ADDI result
                add_seq.dep_reg2 = addi_seq2.item.rd; // Second ADDI result
                add_seq.start(p_sequencer.instr_sqr);
            end
        join
    endtask
endclass

//------------------------------------------------------
// WAR No Stall Sequence
// Purpose: Creates a Write-After-Read hazard that shouldn't stall
// Description:
//   1. First ADDI writes to register R1
//   2. SUB reads R1 while another instruction writes to it
//   3. Second ADDI writes to R1 (WAR hazard)
// Tests: Pipeline handling of WAR hazards (shouldn't stall)
//------------------------------------------------------
class instruction_seq_WAR_no_stall extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_WAR_no_stall)
    Instruction_addi_Seq addi_seq1, addi_seq2;
    Instruction_R_Type_Seq sub_seq;
    
    function new(string name="instruction_seq_WAR_no_stall");
        super.new(name);
    endfunction

    virtual task body();
        addi_seq1 = Instruction_addi_Seq::type_id::create("addi_seq1");
        sub_seq = Instruction_R_Type_Seq::type_id::create("sub_seq");
        addi_seq2 = Instruction_addi_Seq::type_id::create("addi_seq2");

        fork
            begin // First ADDI - initial writer
                addi_seq1.use_dependencies = 1;
                addi_seq1.dep_reg1 = 0; // x0 as source
                addi_seq1.start(p_sequencer.instr_sqr);
            end
            
            begin // SUB - reads while second ADDI writes
                #50; // Small delay
                sub_seq.use_dependencies = 1;
                sub_seq.dep_reg1 = addi_seq1.item.rd; // Read first ADDI result
                sub_seq.dep_reg2 = 1; // Some other register
                sub_seq.start(p_sequencer.instr_sqr);
            end
            
            begin // Second ADDI - WAR hazard
                #100; // Additional delay
                addi_seq2.use_dependencies = 1;
                addi_seq2.dep_reg1 = sub_seq.item.rd; // Write to register SUB reads
                addi_seq2.start(p_sequencer.instr_sqr);
            end
        join
    endtask
endclass

//------------------------------------------------------
// WAW Register Clobber Sequence
// Purpose: Creates a Write-After-Write hazard
// Description:
//   1. Two ADDI instructions write to the same register
//   2. Second write happens shortly after first
// Tests: Pipeline handling of WAW hazards and register file bypass
//------------------------------------------------------
class instruction_seq_WAW_register_clobber extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_WAW_register_clobber)
    Instruction_addi_Seq addi_seq1, addi_seq2;
    
    function new(string name="instruction_seq_WAW_register_clobber");
        super.new(name);
    endfunction

    virtual task body();
        addi_seq1 = Instruction_addi_Seq::type_id::create("addi_seq1");
        addi_seq2 = Instruction_addi_Seq::type_id::create("addi_seq2");

        // Randomize target register (same for both)
        assert(std::randomize(addi_seq1.dep_reg1) with { addi_seq1.dep_reg1 inside {[1:31]}; });
        addi_seq2.dep_reg1 = addi_seq1.dep_reg1; // Same target register

        fork
            begin // First ADDI - first write
                addi_seq1.use_dependencies = 1;
                addi_seq1.start(p_sequencer.instr_sqr);
            end
            
            begin // Second ADDI - WAW hazard
                #50; // Small delay
                addi_seq2.use_dependencies = 1;
                addi_seq2.start(p_sequencer.instr_sqr);
            end
        join
    endtask
endclass

//------------------------------------------------------
// Load-Use Stall Sequence
// Purpose: Creates a load-use hazard that requires stalling
// Description:
//   1. Load instruction reads from memory
//   2. ADD instruction immediately uses loaded value
// Tests: Pipeline stalling for load-use hazards
//------------------------------------------------------
class instruction_seq_LoadUse_stall extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_LoadUse_stall)
    Instruction_Load_Seq load_seq;
    Instruction_R_Type_Seq add_seq;
    
    function new(string name="instruction_seq_LoadUse_stall");
        super.new(name);
    endfunction

    virtual task body();
        load_seq = Instruction_Load_Seq::type_id::create("load_seq");
        add_seq = Instruction_R_Type_Seq::type_id::create("add_seq");

        fork
            begin // Load - producer
                load_seq.use_dependencies = 1;
                load_seq.dep_reg1 = 1; // Use x1 as base
                load_seq.start(p_sequencer.instr_sqr);
            end
            
            begin // ADD - consumer (should stall)
                #100; // Should cause stall
                add_seq.use_dependencies = 1;
                add_seq.dep_reg1 = load_seq.item.rd; // Use loaded value
                add_seq.start(p_sequencer.instr_sqr);
            end
         join_none
        
        #4000; // Long timeout to ensure completion
        disable fork;
    endtask
endclass

//------------------------------------------------------
// Store After Load Sequence
// Purpose: Creates a load-store dependency
// Description:
//   1. Load instruction reads from memory
//   2. Store instruction uses loaded value
// Tests: Memory dependency handling
//------------------------------------------------------
class instruction_seq_StoreAfterLoad extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_StoreAfterLoad)
    Instruction_Load_Seq load_seq;
    Instruction_S_Type_Seq store_seq;
    
    function new(string name="instruction_seq_StoreAfterLoad");
        super.new(name);
    endfunction

    virtual task body();
        load_seq = Instruction_Load_Seq::type_id::create("load_seq");
        store_seq = Instruction_S_Type_Seq::type_id::create("store_seq");

        fork
            begin // Load - producer
                load_seq.use_dependencies = 1;
                load_seq.dep_reg1 = 1; // Use x1 as base
                load_seq.start(p_sequencer.instr_sqr);
            end
            
            begin // Store - consumer
                #100; // Small delay
                store_seq.use_dependencies = 1;
                store_seq.dep_reg1 = 2; // Different base
                store_seq.dep_reg2 = load_seq.item.rd; // Store loaded value
                store_seq.start(p_sequencer.instr_sqr);
            end
         join_none
        
        #4000; // Long timeout to ensure completion
        disable fork;
    endtask
endclass

//------------------------------------------------------
// RAW MUL to ADD Sequence
// Purpose: Creates dependency between multi-cycle MUL and ADD
// Description:
//   1. MUL instruction takes multiple cycles
//   2. ADD instruction depends on MUL result
// Tests: Multi-cycle operation hazard handling
//------------------------------------------------------
class instruction_seq_RAW_MUL_to_ADD extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_RAW_MUL_to_ADD)
    Instruction_M_Extension_Seq mul_seq;
    Instruction_R_Type_Seq add_seq;
    
    function new(string name="instruction_seq_RAW_MUL_to_ADD");
        super.new(name);
    endfunction

    virtual task body();
        mul_seq = Instruction_M_Extension_Seq::type_id::create("mul_seq");
        add_seq = Instruction_R_Type_Seq::type_id::create("add_seq");

        fork
            begin // MUL (multi-cycle producer)
                mul_seq.use_dependencies = 1;
                mul_seq.dep_reg1 = 1; // First operand
                mul_seq.dep_reg2 = 2; // Second operand
                mul_seq.start(p_sequencer.instr_sqr);
            end
            
            begin // ADD (consumer during MUL execution)
                #100; // Start during MUL execution
                add_seq.use_dependencies = 1;
                add_seq.dep_reg1 = mul_seq.item.rd; // MUL result
                add_seq.start(p_sequencer.instr_sqr);
            end
         join_none
        
        #4000; // Long timeout to ensure completion
        disable fork;
    endtask
endclass

//------------------------------------------------------
// Forwarding Path Verification Sequence
// Purpose: Tests all forwarding paths in the pipeline
// Description:
//   1. First ADDI produces a value
//   2. Second ADDI immediately consumes it
//   3. ADD consumes both ADDI results
// Tests: ALU-to-ALU forwarding paths
//------------------------------------------------------
class instruction_seq_Forwarding extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_Forwarding)
    Instruction_addi_Seq addi_seq1, addi_seq2;
    Instruction_R_Type_Seq add_seq;
    
    function new(string name="instruction_seq_Forwarding");
        super.new(name);
    endfunction

    virtual task body();
        addi_seq1 = Instruction_addi_Seq::type_id::create("addi_seq1");
        addi_seq2 = Instruction_addi_Seq::type_id::create("addi_seq2");
        add_seq = Instruction_R_Type_Seq::type_id::create("add_seq");

        fork
            begin // First ADDI - producer
                addi_seq1.use_dependencies = 1;
                addi_seq1.dep_reg1 = 0; // x0 as source
                addi_seq1.start(p_sequencer.instr_sqr);
            end
            
            begin // Second ADDI - first consumer (tests EX->EX forwarding)
                #10; // Very small delay
                addi_seq2.use_dependencies = 1;
                addi_seq2.dep_reg1 = addi_seq1.item.rd; // Consume first ADDI
                addi_seq2.start(p_sequencer.instr_sqr);
            end
            
            begin // ADD - second consumer (tests all forwarding paths)
                #20; // Small delay
                add_seq.use_dependencies = 1;
                add_seq.dep_reg1 = addi_seq1.item.rd; // First ADDI result
                add_seq.dep_reg2 = addi_seq2.item.rd; // Second ADDI result
                add_seq.start(p_sequencer.instr_sqr);
            end
         join_none
        
        #1000; // Long timeout to ensure completion
        disable fork;
    endtask
endclass

//------------------------------------------------------
// Mixed Hazard Scenarios Sequence
// Purpose: Tests combination of different hazard types
// Description:
//   1. ADDI produces initial value
//   2. Load uses that value
//   3. Second ADDI creates WAR hazard with load
//   4. Store uses both loaded and ADDI values
//   5. Final ADD tests all forwarding paths
// Tests: Complex pipeline hazard handling
//------------------------------------------------------
class instruction_seq_MixedHazards extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_MixedHazards)
    Instruction_addi_Seq addi_seq1, addi_seq2;
    Instruction_Load_Seq load_seq;
    Instruction_S_Type_Seq store_seq;
    Instruction_R_Type_Seq add_seq;
    
    function new(string name="instruction_seq_MixedHazards");
        super.new(name);
    endfunction

    virtual task body();
        addi_seq1 = Instruction_addi_Seq::type_id::create("addi_seq1");
        addi_seq2 = Instruction_addi_Seq::type_id::create("addi_seq2");
        load_seq = Instruction_Load_Seq::type_id::create("load_seq");
        store_seq = Instruction_S_Type_Seq::type_id::create("store_seq");
        add_seq = Instruction_R_Type_Seq::type_id::create("add_seq");

        fork
            begin // First ADDI - initial producer
                addi_seq1.use_dependencies = 1;
                addi_seq1.dep_reg1 = 0; // x0 as source
                addi_seq1.start(p_sequencer.instr_sqr);
            end
            
            begin // Load - memory consumer
                #10; // Small delay
                load_seq.use_dependencies = 1;
                load_seq.dep_reg1 = addi_seq1.item.rd; // Use ADDI result
                load_seq.start(p_sequencer.instr_sqr);
            end
            
            begin // Second ADDI - WAR hazard with load
                #20; // Additional delay
                addi_seq2.use_dependencies = 1;
                addi_seq2.dep_reg1 = load_seq.item.rd; // Write to register load reads
                addi_seq2.start(p_sequencer.instr_sqr);
            end
            
            begin // Store - memory producer
                #30; // Additional delay
                store_seq.use_dependencies = 1;
                store_seq.dep_reg1 = addi_seq1.item.rd; // Same as load base
                store_seq.dep_reg2 = addi_seq2.item.rd; // Value from second ADDI
                store_seq.start(p_sequencer.instr_sqr);
            end
            
            begin // Final ADD - complex consumer
                #40; // Additional delay
                add_seq.use_dependencies = 1;
                add_seq.dep_reg1 = load_seq.item.rd; // Loaded value
                add_seq.dep_reg2 = store_seq.item.rd; // Store address
                add_seq.start(p_sequencer.instr_sqr);
            end
          join_none
        
        #2000; // Long timeout to ensure completion
        disable fork;
    endtask
endclass

//------------------------------------------------------
// Load-Load Hazard Sequence
// Purpose: Tests back-to-back loads to same address
// Description:
//   1. First load reads from memory
//   2. Second load reads same address immediately after
//   3. ADD uses both loaded values
// Tests: Memory system hazard handling
//------------------------------------------------------
class instruction_seq_LoadLoad_hazard extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_LoadLoad_hazard)
    Instruction_Load_Seq load_seq1, load_seq2;
    Instruction_R_Type_Seq add_seq;
    
    function new(string name="instruction_seq_LoadLoad_hazard");
        super.new(name);
    endfunction

    virtual task body();
        load_seq1 = Instruction_Load_Seq::type_id::create("load_seq1");
        load_seq2 = Instruction_Load_Seq::type_id::create("load_seq2");
        add_seq = Instruction_R_Type_Seq::type_id::create("add_seq");

        fork
            begin // First load
                load_seq1.use_dependencies = 1;
                load_seq1.dep_reg1 = 1; // x1 as base
                load_seq1.start(p_sequencer.instr_sqr);
            end
            
            begin // Second load (same address)
                #10; // Very small delay
                load_seq2.use_dependencies = 1;
                load_seq2.dep_reg1 = 1; // Same base as first load
                load_seq2.start(p_sequencer.instr_sqr);
            end
            
            begin // ADD that uses both loads
                #20; // Small delay
                add_seq.use_dependencies = 1;
                add_seq.dep_reg1 = load_seq1.item.rd; // First load
                add_seq.dep_reg2 = load_seq2.item.rd; // Second load
                add_seq.start(p_sequencer.instr_sqr);
            end
         join_none
        
        #4000; // Long timeout to ensure completion
        disable fork;
    endtask
endclass

//------------------------------------------------------
// Branch Hazard Sequence
// Purpose: Tests branch prediction and recovery
// Description:
//   1. Two ADDIs produce values
//   2. Branch compares them
//   3. ADD in branch shadow
// Tests: Branch prediction and pipeline flush
//------------------------------------------------------
class instruction_seq_Branch_hazard extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_Branch_hazard)
    Instruction_addi_Seq addi_seq1, addi_seq2;
    Instruction_B_Type_Seq branch_seq;
    Instruction_R_Type_Seq add_seq;
    
    function new(string name="instruction_seq_Branch_hazard");
        super.new(name);
    endfunction

    virtual task body();
        addi_seq1 = Instruction_addi_Seq::type_id::create("addi_seq1");
        addi_seq2 = Instruction_addi_Seq::type_id::create("addi_seq2");
        branch_seq = Instruction_B_Type_Seq::type_id::create("branch_seq");
        add_seq = Instruction_R_Type_Seq::type_id::create("add_seq");

        fork
            begin // First ADDI - first compare operand
                addi_seq1.use_dependencies = 1;
                addi_seq1.dep_reg1 = 0; // x0 as source
                addi_seq1.start(p_sequencer.instr_sqr);
            end
            
            begin // Second ADDI - second compare operand
                #10; // Small delay
                addi_seq2.use_dependencies = 1;
                addi_seq2.dep_reg1 = 0; // x0 as source
                addi_seq2.start(p_sequencer.instr_sqr);
            end
            
            begin // Branch instruction
                #20; // Additional delay
                branch_seq.use_dependencies = 1;
                branch_seq.dep_reg1 = addi_seq1.item.rd; // First ADDI
                branch_seq.dep_reg2 = addi_seq2.item.rd; // Second ADDI
                branch_seq.start(p_sequencer.instr_sqr);
            end
            
            begin // ADD in branch shadow
                #30; // Additional delay
                add_seq.use_dependencies = 1;
                add_seq.dep_reg1 = addi_seq1.item.rd; // First ADDI
                add_seq.dep_reg2 = addi_seq2.item.rd; // Second ADDI
                add_seq.start(p_sequencer.instr_sqr);
            end
         join_none
        
        #500; // Long timeout to ensure completion
        disable fork;
    endtask
endclass

//------------------------------------------------------
// Multi-Port Hazard Sequence
// Purpose: Tests register file port contention
// Description:
//   1. Three ADDIs write to different registers
//   2. Two ADDs read combinations of those registers
// Tests: Register file read/write port contention
//------------------------------------------------------
class instruction_seq_MultiPort_hazard extends Virtual_Base_Seq;
    `uvm_object_utils(instruction_seq_MultiPort_hazard)
    Instruction_addi_Seq addi_seq1, addi_seq2, addi_seq3;
    Instruction_R_Type_Seq add_seq1, add_seq2;
    
    function new(string name="instruction_seq_MultiPort_hazard");
        super.new(name);
    endfunction

    virtual task body();
        addi_seq1 = Instruction_addi_Seq::type_id::create("addi_seq1");
        addi_seq2 = Instruction_addi_Seq::type_id::create("addi_seq2");
        addi_seq3 = Instruction_addi_Seq::type_id::create("addi_seq3");
        add_seq1 = Instruction_R_Type_Seq::type_id::create("add_seq1");
        add_seq2 = Instruction_R_Type_Seq::type_id::create("add_seq2");

        fork
            begin // First ADDI - first writer
                addi_seq1.use_dependencies = 1;
                addi_seq1.dep_reg1 = 0; // x0 as source
                addi_seq1.start(p_sequencer.instr_sqr);
            end
            
            begin // Second ADDI - second writer
                addi_seq2.use_dependencies = 1;
                addi_seq2.dep_reg1 = 0; // x0 as source
                addi_seq2.start(p_sequencer.instr_sqr);
            end
            
            begin // Third ADDI - third writer
                addi_seq3.use_dependencies = 1;
                addi_seq3.dep_reg1 = 0; // x0 as source
                addi_seq3.start(p_sequencer.instr_sqr);
            end
            
            begin // First ADD - reads first two ADDIs
                #10; // Small delay
                add_seq1.use_dependencies = 1;
                add_seq1.dep_reg1 = addi_seq1.item.rd; // First ADDI
                add_seq1.dep_reg2 = addi_seq2.item.rd; // Second ADDI
                add_seq1.start(p_sequencer.instr_sqr);
            end
            
            begin // Second ADD - reads second and third ADDIs
                #10; // Same cycle as first ADD
                add_seq2.use_dependencies = 1;
                add_seq2.dep_reg1 = addi_seq2.item.rd; // Second ADDI
                add_seq2.dep_reg2 = addi_seq3.item.rd; // Third ADDI
                add_seq2.start(p_sequencer.instr_sqr);
           end
         join_none
        
        #3000; // Long timeout to ensure completion
        disable fork;
    endtask
endclass
