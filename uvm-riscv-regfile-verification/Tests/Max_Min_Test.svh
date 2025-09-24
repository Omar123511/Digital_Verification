/*######################################################################
## Class Name: Max_Min_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test runs a virtual sequence to verify the functionality of adding max and min values in all registers,
     then runs all different instructions to check how the design handles edge cases.
  
######################################################################*/
class Max_Min_Test extends  Base_Test;
  `uvm_component_utils(Max_Min_Test)

      Virtual_Max_Min_Seq v_max_min_seq;

  function new(string name="Max_Min_Test",uvm_component parent=null);
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
            `uvm_info("Max_Min_Test","main phase is started",UVM_MEDIUM)
            v_max_min_seq=Virtual_Max_Min_Seq::type_id::create("v_max_min_seq");
            v_max_min_seq.start(env.v_sqr);
            #200;
            `uvm_info("Max_Min_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass
