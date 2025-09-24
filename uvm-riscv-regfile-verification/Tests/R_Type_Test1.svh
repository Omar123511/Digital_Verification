/*######################################################################
## Class Name: R_Type_Test1  
## Author : Omnia Mohamed
## Date: May 2025
 Description:
    -This test starts the Virtual_R_Type_Seq to verify R-type instructions.
    -It verifies R-type instruction functionality.
    -It begins by initializing registers using an ADDI sequence,
    -executes the main R-type sequence, and runs additional corner case sequences that target edge conditions in both R- and B-type  instructions.
######################################################################*/
class R_Type_Test1 extends  Base_Test;
  `uvm_component_utils(R_Type_Test1)

      Virtual_R_Type_Seq v_rtype_seq;
      Virtual_addi_Seq v_addi;
      Virtual_Corner_Cases_R_B_Seq v_cor_seq;


  function new(string name="R_Type_Test1",uvm_component parent=null);
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
            `uvm_info("R_Type_Test1","main phase is started",UVM_MEDIUM)
            v_rtype_seq=Virtual_R_Type_Seq::type_id::create("v_rtype_seq");
            v_addi=Virtual_addi_Seq::type_id::create("v_addi");
	    v_cor_seq=Virtual_Corner_Cases_R_B_Seq::type_id::create("v_cor_seq");

            v_addi.start(env.v_sqr);
            #500;
            v_rtype_seq.start(env.v_sqr);
            #200;
	    repeat(11) begin
            	v_cor_seq.start(env.v_sqr);
	    end
	    
            `uvm_info("R_Type_Test1","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass
