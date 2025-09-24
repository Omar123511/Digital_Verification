/*######################################################################
## Class Name: Jump_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test starts the Virtual_Jump_Seq to verify jump instructions such as jal and jalr.
######################################################################*/
class Jump_Test extends  Base_Test;
  `uvm_component_utils(Jump_Test)
      
      Virtual_Jump_Seq v_jump_seq;
      
  function new(string name="Jump_Test",uvm_component parent=null);
      super.new(name,parent);
  endfunction
  virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
  endfunction
function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
endfunction
  virtual task main_phase(uvm_phase phase);
        super.main_phase(phase);
        phase.raise_objection(this);
            `uvm_info("Jump_Test","main phase is started",UVM_MEDIUM)
            
            v_jump_seq=Virtual_Jump_Seq::type_id::create("v_jump_seq");
            v_jump_seq.start(env.v_sqr);
            
           
           
           
            `uvm_info("Jump_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass