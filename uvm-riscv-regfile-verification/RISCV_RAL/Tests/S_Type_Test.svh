/*######################################################################
## Class Name: S_Type_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test starts the Virtual_S_Type_Seq to verify the correct behavior of S-type store instructions such as (sb, sh, sw).
######################################################################*/
class S_Type_Test extends  Base_Test;
  `uvm_component_utils(S_Type_Test)
      

      Virtual_S_Type_Seq v_stype_seq;

  function new(string name="S_Type_Test",uvm_component parent=null);
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
            `uvm_info("S_Type_Test","main phase is started",UVM_MEDIUM)
             v_stype_seq=Virtual_S_Type_Seq::type_id::create("v_stype_seq");
             v_stype_seq.start(env.v_sqr);
            #2000;
            `uvm_info("S_Type_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass