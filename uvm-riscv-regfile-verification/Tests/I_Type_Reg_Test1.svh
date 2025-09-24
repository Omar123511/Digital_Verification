/*######################################################################
## Class Name: I_Type_Reg_Test1  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This test runs a virtual sequence to verify I-type register instructions.
     It starts with an ADDI sequence to initialize register values, 
     followed by execution of the main I-Type register sequence. 
######################################################################*/
class I_Type_Reg_Test1 extends  Base_Test;
  `uvm_component_utils(I_Type_Reg_Test1)
      
      Virtual_I_Type_Reg_Seq v_itype_reg_seq;
      Virtual_addi_Seq v_addi;

  function new(string name="I_Type_Reg_Test1",uvm_component parent=null);
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
            `uvm_info("I_Type_Reg_Test1","main phase is started",UVM_MEDIUM)
            
            v_itype_reg_seq=Virtual_I_Type_Reg_Seq::type_id::create("v_itype_reg_seq");
            v_addi=Virtual_addi_Seq::type_id::create("v_addi");

            v_addi.start(env.v_sqr);
            #500;
            v_itype_reg_seq.start(env.v_sqr);
            #200;
            
            `uvm_info("I_Type_Reg_Test1","main phase is finished",UVM_MEDIUM)
        phase.drop_objection(this);
  endtask
endclass