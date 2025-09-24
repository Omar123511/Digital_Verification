
//------------------------------------------------------------------------------------
// Nourhan Mohammed
// Complete Hazard Test Class
//
// This class executes a comprehensive suite of hazard test sequences to verify:
// - Pipeline hazard detection (RAW, WAR, WAW)
// - Forwarding paths and bypass networks
// - Load-use stalls and memory dependencies
// - Multi-cycle operation handling
// - Complex hazard combinations
//
// Each test sequence includes appropriate delays between tests to ensure clean
// separation of test cases and accurate timing verification.
//------------------------------------------------------------------------------------

class Hazard_Test extends Base_Test;
  `uvm_component_utils(Hazard_Test)
  
  // Sequence instances for all hazard types
  instruction_seq_RAW_ALU_dependency raw_seq;          // Basic ALU RAW dependency
  instruction_seq_WAR_no_stall war_seq;               // Write-After-Read hazard
  instruction_seq_WAW_register_clobber waw_seq;       // Write-After-Write hazard  
  instruction_seq_LoadUse_stall loaduse_seq;          // Load-Use hazard with stalls
  instruction_seq_StoreAfterLoad storeload_seq;       // Memory disambiguation
  instruction_seq_RAW_MUL_to_ADD raw_mul_seq;         // Multi-cycle RAW dependency
  instruction_seq_Forwarding forwarding_seq;          // Forwarding path verification
  instruction_seq_MixedHazards mixed_seq;             // Combined hazard scenarios
  instruction_seq_LoadLoad_hazard loadload_seq;       // Back-to-back load hazard
  instruction_seq_Branch_hazard branch_seq;           // Branch prediction hazard
  instruction_seq_MultiPort_hazard multiport_seq;     // Register file port contention

  function new(string name="Hazard_Test", uvm_component parent=null);
      super.new(name,parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // No additional configuration needed in build phase
  endfunction
  
  function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // No special connections needed
  endfunction
  
  virtual task main_phase(uvm_phase phase);
      super.main_phase(phase);
      phase.raise_objection(this);
      
      `uvm_info("HAZARD_TEST", "Starting comprehensive hazard test suite", UVM_MEDIUM)
      
      //----------------------------------------------------------------------------
      // 1. Basic RAW ALU Dependency Test
      // Verifies: Forwarding paths between ALU operations
      // Expected: No stalls with correct forwarding
      //----------------------------------------------------------------------------
      raw_seq = instruction_seq_RAW_ALU_dependency::type_id::create("raw_seq");
      raw_seq.start(env.v_sqr);
      `uvm_info("RAW_TEST", "Completed RAW ALU dependency test", UVM_MEDIUM)
      #100; // Allow pipeline to clear
      
      //----------------------------------------------------------------------------
      // 2. WAR No Stall Test 
      // Verifies: Write-After-Read hazard handling
      // Expected: No stalls since WAR hazards are allowed
      //----------------------------------------------------------------------------
      war_seq = instruction_seq_WAR_no_stall::type_id::create("war_seq");
      war_seq.start(env.v_sqr);
      `uvm_info("WAR_TEST", "Completed WAR no stall test", UVM_MEDIUM)
      #200; // Additional delay for writeback completion
      
      //----------------------------------------------------------------------------
      // 3. WAW Register Clobber Test
      // Verifies: Write-After-Write hazard detection
      // Expected: Pipeline stall or correct write ordering
      //----------------------------------------------------------------------------
      waw_seq = instruction_seq_WAW_register_clobber::type_id::create("waw_seq");
      waw_seq.start(env.v_sqr);
      `uvm_info("WAW_TEST", "Completed WAW register clobber test", UVM_MEDIUM)
      #200; // Allow multi-cycle operation to complete
      
      //----------------------------------------------------------------------------
      // 4. Load-Use Stall Test
      // Verifies: Pipeline stalling when load data needed
      // Expected: Correct stall insertion and forwarding from MEM stage
      //----------------------------------------------------------------------------
      loaduse_seq = instruction_seq_LoadUse_stall::type_id::create("loaduse_seq");
      loaduse_seq.start(env.v_sqr);
      `uvm_info("LOADUSE_TEST", "Completed Load-Use stall test", UVM_MEDIUM)
      #300; // Longer delay for memory operations
      
      //----------------------------------------------------------------------------
      // 5. Store After Load Test
      // Verifies: Memory disambiguation logic
      // Expected: Correct store buffer behavior or forwarding
      //----------------------------------------------------------------------------
      storeload_seq = instruction_seq_StoreAfterLoad::type_id::create("storeload_seq");
      storeload_seq.start(env.v_sqr);
      `uvm_info("STORELOAD_TEST", "Completed Store after Load test", UVM_MEDIUM)
      #200; // Allow store buffer to drain
      
      //----------------------------------------------------------------------------
      // 6. RAW MUL to ADD Test
      // Verifies: Multi-cycle operation hazard handling
      // Expected: Correct stalling until MUL result available
      //----------------------------------------------------------------------------
      raw_mul_seq = instruction_seq_RAW_MUL_to_ADD::type_id::create("raw_mul_seq");
      raw_mul_seq.start(env.v_sqr);
      `uvm_info("RAWMUL_TEST", "Completed RAW MUL to ADD test", UVM_MEDIUM)
      #500; // Extended delay for multi-cycle MUL
      
      //----------------------------------------------------------------------------
      // 7. Forwarding Test
      // Verifies: All forwarding paths with minimal delays
      // Expected: No stalls with correct forwarding
      //----------------------------------------------------------------------------
      forwarding_seq = instruction_seq_Forwarding::type_id::create("forwarding_seq");
      forwarding_seq.start(env.v_sqr);
      `uvm_info("FORWARDING_TEST", "Completed Forwarding test", UVM_MEDIUM)
     
      
      //----------------------------------------------------------------------------
      // 8. Mixed Hazards Test
      // Verifies: Combined RAW/WAR/WAW scenarios
      // Expected: Correct handling of complex dependencies
      //----------------------------------------------------------------------------
      mixed_seq = instruction_seq_MixedHazards::type_id::create("mixed_seq");
      mixed_seq.start(env.v_sqr);
      `uvm_info("MIXED_TEST", "Completed Mixed hazards test", UVM_MEDIUM)
     
      
      //----------------------------------------------------------------------------
      // 9. Load-Load Hazard Test (NEW)
      // Verifies: Back-to-back loads to same register
      // Expected: No data corruption between dependent loads
      //----------------------------------------------------------------------------
      loadload_seq = instruction_seq_LoadLoad_hazard::type_id::create("loadload_seq");
      loadload_seq.start(env.v_sqr);
      `uvm_info("LOADLOAD_TEST", "Completed Load-Load hazard test", UVM_MEDIUM)
      #200; // Memory operation delay
      
      //----------------------------------------------------------------------------
      // 10. Branch Hazard Test (NEW)
      // Verifies: Branch dependent on ALU result
      // Expected: Correct stall and flush behavior
      //----------------------------------------------------------------------------
      branch_seq = instruction_seq_Branch_hazard::type_id::create("branch_seq");
      branch_seq.start(env.v_sqr);
      `uvm_info("BRANCH_TEST", "Completed Branch hazard test", UVM_MEDIUM)
      #100; // Branch resolution delay
      
      //----------------------------------------------------------------------------
      // 11. Multi-Port Hazard Test (NEW)
      // Verifies: Register file port contention
      // Expected: Correct simultaneous read/write behavior
      //----------------------------------------------------------------------------
      multiport_seq = instruction_seq_MultiPort_hazard::type_id::create("multiport_seq");
      multiport_seq.start(env.v_sqr);
      `uvm_info("MULTIPORT_TEST", "Completed Multi-Port hazard test", UVM_MEDIUM)
      #100; // Register file access delay
      
      //----------------------------------------------------------------------------
      // Test Completion
      `uvm_info("HAZARD_TEST", "All hazard tests completed successfully", UVM_HIGH)
      
      phase.drop_objection(this);
  endtask
endclass


