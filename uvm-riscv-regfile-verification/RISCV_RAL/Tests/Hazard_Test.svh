//------------------------------------------------------------------------------------
// Nourhan Mohammed
// Complete Hazard Test Class
// This class executes all hazard test sequences to verify full processor behavior
//------------------------------------------------------------------------------------

class Hazard_Test extends Base_Test;
  `uvm_component_utils(Hazard_Test)
  
  // Sequence instances for all hazard types
  instruction_seq_RAW_ALU_dependency raw_seq;          // RAW ALU dependency test
  instruction_seq_WAR_no_stall war_seq;               // WAR hazard test
  instruction_seq_WAW_register_clobber waw_seq;       // WAW hazard test
  instruction_seq_LoadUse_stall loaduse_seq;          // Load-Use hazard test
  
  
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
      
      `uvm_info("HAZARD_TEST", "Starting all hazard test sequences", UVM_MEDIUM)
      
      // 1. RAW ALU Dependency Test
      raw_seq = instruction_seq_RAW_ALU_dependency::type_id::create("raw_seq");
      raw_seq.start(env.v_sqr);
      `uvm_info("RAW_TEST", "Completed RAW ALU dependency test", UVM_MEDIUM)
      #100;
      
      // 2. WAR No Stall Test
      war_seq = instruction_seq_WAR_no_stall::type_id::create("war_seq");
      war_seq.start(env.v_sqr);
      `uvm_info("WAR_TEST", "Completed WAR no stall test", UVM_MEDIUM)
      #200;
      
      // 3. WAW Register Clobber Test
      waw_seq = instruction_seq_WAW_register_clobber::type_id::create("waw_seq");
      waw_seq.start(env.v_sqr);
      `uvm_info("WAW_TEST", "Completed WAW register clobber test", UVM_MEDIUM)
      #200;
      
      // 4. Load-Use Stall Test
      loaduse_seq = instruction_seq_LoadUse_stall::type_id::create("loaduse_seq");
      loaduse_seq.start(env.v_sqr);
      `uvm_info("LOADUSE_TEST", "Completed Load-Use stall test", UVM_MEDIUM)
      #300;  // Longer delay for memory operations
      
     

      `uvm_info("HAZARD_TEST", "All hazard tests completed successfully", UVM_HIGH)
      
      phase.drop_objection(this);
  endtask
endclass

