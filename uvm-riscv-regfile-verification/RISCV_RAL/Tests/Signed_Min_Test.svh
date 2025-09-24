/*######################################################################
## Class Name: Signed_Min_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test runs virtual sequences to verify functionality with signed 
      minimum values in all registers, then applies various instruction 
      sequences (R-type, M-extension, B-type) to cover different corner cases. 
######################################################################*/
class Signed_Min_Test extends  Base_Test;
  `uvm_component_utils(Signed_Min_Test)

      Virtual_Signed_Min_Seq v_min_seq1,v_min_seq2,v_min_seq3;
      Virtual_R_Type_Seq v_rtype_seq;

      Virtual_M_Extension_Seq v_m_seq;
      Virtual_B_Type_Seq v_btype_seq;

  function new(string name="Signed_Min_Test",uvm_component parent=null);
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
            `uvm_info("Signed_Min_Test","main phase is started",UVM_MEDIUM)
                v_min_seq1=Virtual_Signed_Min_Seq::type_id::create("v_min_seq1");
                v_min_seq2=Virtual_Signed_Min_Seq::type_id::create("v_min_seq2");
                v_min_seq3=Virtual_Signed_Min_Seq::type_id::create("v_min_seq3");
                v_rtype_seq=Virtual_R_Type_Seq::type_id::create("v_rtype_seq");
                v_m_seq=Virtual_M_Extension_Seq::type_id::create("v_m_seq");
                v_btype_seq=Virtual_B_Type_Seq::type_id::create("v_btype_seq");
            
                v_min_seq1.start(env.v_sqr);
                #500;
                v_rtype_seq.start(env.v_sqr);
                #1000;
                v_min_seq2.start(env.v_sqr);
                #500;
                v_m_seq.start(env.v_sqr);
                #1000;
                v_min_seq3.start(env.v_sqr);
                #500;
                fork 
			v_btype_seq.start(env.v_sqr);
		join_none
		#2000;
		disable fork;
            
                
            `uvm_info("Signed_Min_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass
