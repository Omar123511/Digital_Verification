/*######################################################################
## Class Name: All_Ones_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test runs a virtual sequence to verify the functionality of adding all ones in all registers and then apply all different instructions.
######################################################################*/
class All_Ones_Test extends  Base_Test;
  `uvm_component_utils(All_Ones_Test)

      Virtual_All_Ones_Seq v_ones_seq;

  function new(string name="All_Ones_Test",uvm_component parent=null);
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
            `uvm_info("All_Ones_Test","main phase is started",UVM_MEDIUM)
            v_ones_seq=Virtual_All_Ones_Seq::type_id::create("v_ones_seq");
            v_ones_seq.start(env.v_sqr);
            #200;
            `uvm_info("All_Ones_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass
