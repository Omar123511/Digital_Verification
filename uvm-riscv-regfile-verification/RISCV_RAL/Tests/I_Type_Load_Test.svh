/*######################################################################
## Class Name: I_Type_Load_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test verifies the functionality of I-type load instructions.
    .It runs a virtual sequence on the virtual sequencer to ensure proper data loading behavior from memory using load operations.
######################################################################*/
class I_Type_Load_Test extends  Base_Test;
  `uvm_component_utils(I_Type_Load_Test)
      
      Virtual_I_Type_Load_Seq v_itype_load_seq;
      
  function new(string name="I_Type_Load_Test",uvm_component parent=null);
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
            `uvm_info("I_Type_Load_Test","main phase is started",UVM_MEDIUM)
            
            v_itype_load_seq=Virtual_I_Type_Load_Seq::type_id::create("v_itype_load_seq");
            v_itype_load_seq.start(env.v_sqr);
            #2000;
           
           
           
            `uvm_info("I_Type_Load_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass