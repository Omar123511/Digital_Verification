/*######################################################################
## Class Name: Rand_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test runs a virtual sequence to verify the functionality of random instructions using the virtual sequencer.
    .It starts two random instruction sequences on the virtual sequencer to exercise different instruction combinations and corner cases.
######################################################################*/
class Rand_Test extends  Base_Test;
  `uvm_component_utils(Rand_Test)

      Virtual_Rand_Seq v_rand_seq,v_rand_seq2;

  function new(string name="Rand_Test",uvm_component parent=null);
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
            `uvm_info("Rand_Test","main phase is started",UVM_MEDIUM)
            v_rand_seq=Virtual_Rand_Seq::type_id::create("v_rand_seq");
            v_rand_seq2=Virtual_Rand_Seq::type_id::create("v_rand_seq2");
            v_rand_seq.start(env.v_sqr);
            #200;
            v_rand_seq2.start(env.v_sqr);
            #200;
            `uvm_info("Rand_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass
