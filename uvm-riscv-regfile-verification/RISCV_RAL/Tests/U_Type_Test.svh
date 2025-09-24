/*######################################################################
## Class Name: U_Type_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test starts the Virtual_U_Type_Seq to generate and verify U-Type instructions such as LUI and AUIPC.
######################################################################*/
class U_Type_Test extends  Base_Test;
  `uvm_component_utils(U_Type_Test)
      
      Virtual_U_Type_Seq v_utype_seq;
      
  function new(string name="U_Type_Test",uvm_component parent=null);
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
            `uvm_info("U_Type_Test","main phase is started",UVM_MEDIUM)
            
            v_utype_seq=Virtual_U_Type_Seq::type_id::create("v_utype_seq");
            v_utype_seq.start(env.v_sqr);
            #2000;
           
           
           
            `uvm_info("U_Type_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass