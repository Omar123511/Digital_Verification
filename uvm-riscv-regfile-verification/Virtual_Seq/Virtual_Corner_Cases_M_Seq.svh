
/*######################################################################
## Class Name: Virtual_Corner_Cases_M_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence starts various instruction sequences
    targeting corner cases for M-extension instructions and related 
    operations. It generates sequences to test maximum and minimum 
    signed and unsigned values, all-ones, all-zeroes, multiplication 
    instructions, and other corner scenarios to help achieve 100% functional coverage.
######################################################################*/
class Virtual_Corner_Cases_M_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Corner_Cases_M_Seq)

    Instruction_xori_max_sequence max_seq,max_seq2;//to generate max signed value
    Instruction_signed_min_sequence min_seq,min_seq1,min_seq2;//to generate min signed value
    
    Instruction_all_ones_addi_sequence ones_seq; //to generate all ones value 
    Instruction_base_Sequence base_seq; // to generate all zeros value
    Instruction_max_min_addi_sequence max_min_seq;//to generate max & min unsigned values

    Instruction_addi_Sequence addi_seq;
    
    Instruction_M_Extension_Sequence m_seq;
    Instruction_mul_op_seq mul_seq,mul_seq2;

    
    function new(string name="Virtual_Corner_Cases_M_Seq");
        super.new(name);
    endfunction
    virtual task body();
        max_seq=Instruction_xori_max_sequence::type_id::create("max_seq");
        max_seq.num_transactions=15;
        min_seq=Instruction_signed_min_sequence::type_id::create("min_seq");
        min_seq.num_transactions=15;
        
         max_seq2=Instruction_xori_max_sequence::type_id::create("max_seq2");
        max_seq2.num_transactions=7;
        min_seq1=Instruction_signed_min_sequence::type_id::create("min_seq1");
        min_seq1.num_transactions=7;
        
        base_seq=Instruction_base_Sequence::type_id::create("base_seq");
        base_seq.num_transactions=7; 
        
        min_seq2=Instruction_signed_min_sequence::type_id::create("min_seq2");
        min_seq2.num_transactions=15;
        
        ones_seq=Instruction_all_ones_addi_sequence::type_id::create("ones_seq");
        ones_seq.num_transactions=7;
        
        max_min_seq=Instruction_max_min_addi_sequence::type_id::create("max_min_seq");
        max_min_seq.num_transactions=7;
        
        m_seq=Instruction_M_Extension_Sequence::type_id::create("m_seq");
        m_seq.num_transactions=31;
        
        mul_seq=Instruction_mul_op_seq::type_id::create("mul_seq");
        mul_seq.num_transactions=15;
        mul_seq2=Instruction_mul_op_seq::type_id::create("mul_seq2");
        mul_seq2.num_transactions=15;

	      addi_seq=Instruction_addi_Sequence::type_id::create("addi_seq");
        addi_seq.num_transactions=7;
        
        
        fork
             begin 
                min_seq.start(p_sequencer.instr_sqr);
                #10;
                max_seq.start(p_sequencer.instr_sqr);
                #10;
                base_seq.start(p_sequencer.instr_sqr);
                
             end
        join
        mul_seq.start(p_sequencer.instr_sqr);
        m_seq.start(p_sequencer.instr_sqr);
        fork
             begin 
                base_seq.start(p_sequencer.instr_sqr);
                #10;
                min_seq.start(p_sequencer.instr_sqr);
                #10;
                max_seq.start(p_sequencer.instr_sqr);
                #10;
               
                
             end
        join
        mul_seq.start(p_sequencer.instr_sqr);
	      m_seq.start(p_sequencer.instr_sqr);
        fork
             begin 
               min_seq.start(p_sequencer.instr_sqr);
                #10;
                base_seq.start(p_sequencer.instr_sqr);
                #10;
                
               
                
             end
        join
        mul_seq.start(p_sequencer.instr_sqr);
	      m_seq.start(p_sequencer.instr_sqr);
        
        fork
             begin 
               min_seq2.start(p_sequencer.instr_sqr);
                #10;
                min_seq1.start(p_sequencer.instr_sqr);
                #10;
                max_seq2.start(p_sequencer.instr_sqr);
                #10;
               //base_seq.start(p_sequencer.instr_sqr);
                
             end
        join
        mul_seq2.start(p_sequencer.instr_sqr);
	      m_seq.start(p_sequencer.instr_sqr);
	    fork
             begin 
               min_seq.start(p_sequencer.instr_sqr);
                #10;
                ones_seq.start(p_sequencer.instr_sqr);
                #10;
             end
     join
        mul_seq.start(p_sequencer.instr_sqr);
	      m_seq.start(p_sequencer.instr_sqr);
	    fork
             begin 
               min_seq.start(p_sequencer.instr_sqr);
                #10;
		            max_seq.start(p_sequencer.instr_sqr);
                #10;
                ones_seq.start(p_sequencer.instr_sqr);
                #10;
             end
     join
        mul_seq.start(p_sequencer.instr_sqr);
	      m_seq.start(p_sequencer.instr_sqr);

	    fork
             begin 
               min_seq.start(p_sequencer.instr_sqr);
                #10;
                addi_seq.start(p_sequencer.instr_sqr);
                #10;
             end
     join
        mul_seq.start(p_sequencer.instr_sqr);
	      m_seq.start(p_sequencer.instr_sqr);
      fork
             begin 
               min_seq.start(p_sequencer.instr_sqr);
                #10;
                max_min_seq.start(p_sequencer.instr_sqr);
                #10;
             end
      join
        mul_seq.start(p_sequencer.instr_sqr);
	      m_seq.start(p_sequencer.instr_sqr);
	    fork
             begin 
               min_seq.start(p_sequencer.instr_sqr);
                #10;
		            max_seq.start(p_sequencer.instr_sqr);
                #10;
                max_min_seq.start(p_sequencer.instr_sqr);
                #10;
             end
     join
        mul_seq.start(p_sequencer.instr_sqr);
	      m_seq.start(p_sequencer.instr_sqr);

    endtask
    endclass
