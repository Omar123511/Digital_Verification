
/*######################################################################
## Class Name: Virtual_Corner_Cases_R_B_Seq  
## Engineer : Omnia Mohamed
## Date: May 2025
## Description:
    .This virtual sequence is used to run a set of corner case sequences 
    for R-type and B-type instructions. It includes combinations of 
    maximum and minimum signed values, all-ones, all-zeros, and 
    edge cases for branching and R-type instructions to help achieve 100% functional coverage.
######################################################################*/
class Virtual_Corner_Cases_R_B_Seq extends Virtual_Base_Seq;
    `uvm_object_utils(Virtual_Corner_Cases_R_B_Seq)

    Instruction_xori_max_sequence max_seq,max_seq2;//to generate max signed value
    Instruction_signed_min_sequence min_seq,min_seq1,min_seq2;//to generate min signed value
    
    Instruction_all_ones_addi_sequence ones_seq; //to generate all ones value 
    Instruction_base_Sequence base_seq; // to generate all zeros value
    Instruction_max_min_addi_sequence max_min_seq;//to generate max & min unsigned values

    Instruction_addi_Sequence addi_seq;
    
     
    Instruction_R_Type_Sequence rtype_seq;
    Instruction_corner_Cases_r_seq rb_seq;
    Instruction_B_Type_Sequence b_seq,b_seq2;
 
	

    
    function new(string name="Virtual_Corner_Cases_R_B_Seq");
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
        min_seq1.num_transactions=15;
        
        base_seq=Instruction_base_Sequence::type_id::create("base_seq");
        base_seq.num_transactions=7; 
        
        min_seq2=Instruction_signed_min_sequence::type_id::create("min_seq2");
        min_seq2.num_transactions=7;
        
        ones_seq=Instruction_all_ones_addi_sequence::type_id::create("ones_seq");
        ones_seq.num_transactions=15;
        
        max_min_seq=Instruction_max_min_addi_sequence::type_id::create("max_min_seq");
        max_min_seq.num_transactions=15;
        
	      addi_seq=Instruction_addi_Sequence::type_id::create("addi_seq");
        addi_seq.num_transactions=7;

	      rtype_seq=Instruction_R_Type_Sequence::type_id::create("rtype_seq");
        rtype_seq.num_transactions=31;
        rb_seq=Instruction_corner_Cases_r_seq::type_id::create("rb_seq");
        rb_seq.num_transactions=15;
	      b_seq=Instruction_B_Type_Sequence::type_id::create("b_seq");
        b_seq.num_transactions=10;
	      b_seq2=Instruction_B_Type_Sequence::type_id::create("b_seq2");
	      b_seq2.num_transactions=10;

     	fork
             begin 
               //base_seq.start(p_sequencer.instr_sqr);
               ones_seq.start(p_sequencer.instr_sqr);
                #10;
             end
        join
	      rb_seq.start(p_sequencer.instr_sqr);
        rtype_seq.start(p_sequencer.instr_sqr);
	    fork
             begin 
                min_seq.start(p_sequencer.instr_sqr);
                #10;
                max_seq.start(p_sequencer.instr_sqr);
                #10;
                base_seq.start(p_sequencer.instr_sqr);
                
             end
        join
	      rb_seq.start(p_sequencer.instr_sqr);
        rtype_seq.start(p_sequencer.instr_sqr);
	repeat(3)begin 
	   fork
             begin 
               
               ones_seq.start(p_sequencer.instr_sqr);
	            base_seq.start(p_sequencer.instr_sqr);
                #10;
             end
           join
	rb_seq.start(p_sequencer.instr_sqr);
	rtype_seq.start(p_sequencer.instr_sqr);
	end
	repeat(3)begin 
	  fork
             begin 
               
               max_min_seq.start(p_sequencer.instr_sqr);
               base_seq.start(p_sequencer.instr_sqr);
                #10;
             end
          join
	rb_seq.start(p_sequencer.instr_sqr);
	rtype_seq.start(p_sequencer.instr_sqr);
	end
	repeat(3)begin
	  fork
             begin 
                min_seq.start(p_sequencer.instr_sqr);
                #10;
		            min_seq2.start(p_sequencer.instr_sqr);
                #10;
                max_seq2.start(p_sequencer.instr_sqr);
                #10;
                
             end
        join
     	  rb_seq.start(p_sequencer.instr_sqr);
        rtype_seq.start(p_sequencer.instr_sqr);
	end
	
	  fork
             begin 
                min_seq.start(p_sequencer.instr_sqr);
                #10;
		            min_seq2.start(p_sequencer.instr_sqr);
                #10;
                max_seq2.start(p_sequencer.instr_sqr);
                #10;
                
             end
	  join

	  b_seq.start(p_sequencer.instr_sqr);
	
	  fork
             begin 
               
               ones_seq.start(p_sequencer.instr_sqr);
		            base_seq.start(p_sequencer.instr_sqr);
                #10;
             end
        join
	b_seq.start(p_sequencer.instr_sqr);
	
	
	rtype_seq.start(p_sequencer.instr_sqr);
      
       

    endtask
    endclass
