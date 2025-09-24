/*######################################################################
## Class Name: M_Extension_Test  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test starts the Virtual_M_Extension_Seq to verify M-extension (multiplication and division) instructions.
    .This includes tests with corner case values such as max, min, unsigned, signed, positive, and negative operands combined with M-extension operations 
     to ensure full functional coverage.
######################################################################*/
class M_Extension_Test extends  Base_Test;
  `uvm_component_utils(M_Extension_Test)

      Virtual_M_Extension_Seq v_m_seq,v_m_seq2;
      Virtual_addi_Seq v_addi;
      
      Virtual_Corner_Cases_M_Seq v_m_cor_seq;


  function new(string name="M_Extension_Test",uvm_component parent=null);
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
            `uvm_info("M_Extension_Test","main phase is started",UVM_MEDIUM)
            v_m_seq=Virtual_M_Extension_Seq::type_id::create("v_m_seq");
            v_m_seq2=Virtual_M_Extension_Seq::type_id::create("v_m_seq2");
            v_addi=Virtual_addi_Seq::type_id::create("v_addi");
            
            v_m_cor_seq=Virtual_Corner_Cases_M_Seq::type_id::create("v_m_cor_seq");
            
            v_m_seq.start(env.v_sqr);
            #200;
            v_addi.start(env.v_sqr);
            #500;
            v_m_seq2.start(env.v_sqr);
            #200;
	repeat(4) begin
            v_m_cor_seq.start(env.v_sqr);
	end
            
            `uvm_info("M_Extension_Test","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass
