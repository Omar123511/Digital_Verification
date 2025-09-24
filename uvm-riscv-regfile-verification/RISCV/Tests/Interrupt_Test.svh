/*###################################################################### 
## Class Name: Interrupt_Test   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This UVM test class verifies the interrupt functionality of the RV32IM processor. 
    It builds and configures the environment, initializes sequences for 
    interrupt generation.
######################################################################*/
class Interrupt_Test extends  Base_Test;
  `uvm_component_utils(Interrupt_Test)
      
      Virtual_Interrupt_Seq v_interrupt_seq;

  function new(string name="Interrupt_Test",uvm_component parent=null);
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
            `uvm_info("Interrupt_Test","main phase is started",UVM_MEDIUM)
            
            v_interrupt_seq=Virtual_Interrupt_Seq::type_id::create("v_interrupt_seq");
            v_interrupt_seq.start(env.v_sqr);
            #200;
            `uvm_info("Interrupt_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass