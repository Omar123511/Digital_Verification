/*######################################################################
## Class Name: B_Type_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test runs a virtual sequence to verify the functionality of B-type (branch) instructions using the virtual sequencer.
######################################################################*/
class B_Type_Test extends  Base_Test;
  `uvm_component_utils(B_Type_Test)

      Virtual_B_Type_Seq v_btype_seq;
      Virtual_addi_Seq v_addi;

  function new(string name="B_Type_Test",uvm_component parent=null);
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
            `uvm_info("B_Type_Test","main phase is started",UVM_MEDIUM)
            v_btype_seq=Virtual_B_Type_Seq::type_id::create("v_btype_seq");
            v_addi=Virtual_addi_Seq::type_id::create("v_addi");
            v_addi.start(env.v_sqr);
            #500;
            v_btype_seq.start(env.v_sqr);
            #200;
            `uvm_info("B_Type_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass