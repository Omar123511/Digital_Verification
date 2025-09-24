/*######################################################################
## Class Name: Store_Load_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test starts the Virtual_Store_Load_Seq to verify correct functionality of memory store and load operations, 
    ensuring proper data handling between the core and data memory agent.
######################################################################*/
class Store_Load_Test extends  Base_Test;
  `uvm_component_utils(Store_Load_Test)
      
      Virtual_Store_Load_Seq v_store_load_seq;
      
  function new(string name="Store_Load_Test",uvm_component parent=null);
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
            `uvm_info("Store_Load_Test","main phase is started",UVM_MEDIUM)
            
            v_store_load_seq=Virtual_Store_Load_Seq::type_id::create("v_store_load_seq");
            v_store_load_seq.start(env.v_sqr);
            #2000;
           
           
           
            `uvm_info("Store_Load_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass