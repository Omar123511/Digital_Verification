/*######################################################################
## Class Name: Instruction_Coverage  
## Engineer : Omnia Mohamed
## Date: May 2025
   Description: 
    -This class defines the functional coverage model for the instructions,
    covering opcodes, registers, immediate values, and instruction types to ensure all instruction scenarios are exercised.
    -The collected coverage ensures that all instruction formats (R, I, S, B, U, J) and  M-extension are exercised during simulation.
######################################################################*/
class Instruction_Coverage extends uvm_subscriber#(Instruction_Seq_Item);
    `uvm_component_utils(Instruction_Coverage)

    Instruction_Seq_Item cov_item;
    uvm_analysis_imp#(Instruction_Seq_Item,Instruction_Coverage) imp_instruction_cov;

    covergroup cg_instruction;
       opcode: coverpoint cov_item.opcode{
            bins r_type={7'b0110011};// r-type instructions
            bins i_type_reg={7'b0010011};// i-type reg instructions
            bins i_type_load={7'b0000011};// i-type load instructions
            bins s_type={7'b0100011};// s-type
            bins j_instr={7'b1101111,7'b1100111}; //jal,jalr
            bins b_type={7'b1100011};// b-type
            bins u_type={7'b0110111,7'b0010111};//u-type
            bins m_instr={7'b0110011};// m extension
            illegal_bins invalid_opcode = default;
        }
        rd: coverpoint cov_item.rd{
            illegal_bins reg0={0};//register 0 is read only.
            bins rd_bin[]={[1:31]};
        }
        rs1: coverpoint cov_item.rs1{
            bins zero={0};
            bins rs1_bin[]={[1:31]};
        }
        rs2: coverpoint cov_item.rs2{
            bins zero={0};
            bins rs2_bin[]={[1:31]};
        }
        r_type: coverpoint cov_item.funct3 iff (cov_item.opcode==7'b0110011 &&(cov_item.funct7==7'b0000000 || cov_item.funct7==7'b0100000)){
            bins add={3'b000} iff (cov_item.funct7==7'b0000000);
            bins sub={3'b000} iff (cov_item.funct7==7'b0100000);
            bins sll={3'b001} iff (cov_item.funct7==7'b0000000);
            bins slt={3'b010} iff (cov_item.funct7==7'b0000000);
            bins sltu={3'b011} iff (cov_item.funct7==7'b0000000);
            bins xor_op={3'b100}iff (cov_item.funct7==7'b0000000);
            bins srl={3'b101}iff (cov_item.funct7==7'b0000000);
            bins sra={3'b101} iff(cov_item.funct7==7'b0100000);
            bins or_op={3'b110}iff (cov_item.funct7==7'b0000000);
            bins and_op={3'b111}iff (cov_item.funct7==7'b0000000);
        }
        i_type_reg: coverpoint cov_item.funct3 iff (cov_item.opcode==7'b0010011 ){
            bins addi={3'b000} ;
            bins slli={3'b001} iff(cov_item.imm[11:5]==7'b0000000);
            bins slti={3'b010} ;
            bins sltiu={3'b011} iff (cov_item.funct7==7'b0000000);
            bins xori={3'b100}iff (cov_item.funct7==7'b0000000);
            bins srli={3'b101}iff (cov_item.imm[11:5]==7'b0000000);
            bins srai={3'b101} iff(cov_item.imm[11:5]==7'b0100000);
            bins ori={3'b110}iff (cov_item.funct7==7'b0000000);
            bins andi={3'b111}iff (cov_item.funct7==7'b0000000);
        }
        i_type_load: coverpoint cov_item.funct3 iff (cov_item.opcode==7'b0000011 ){
            bins lb={3'b000} ;
            bins lh={3'b001};
            bins lw={3'b010} ;
            bins lbu={3'b100} ;
            bins lhu={3'b101};
        }
        s_type: coverpoint cov_item.funct3 iff (cov_item.opcode==7'b0100011 ){
            bins sb={3'b000} ;
            bins sh={3'b001};
            bins sw={3'b010} ;
        }
        j_instr1: coverpoint cov_item.funct3 iff (cov_item.opcode==7'b1100111 ){
            bins jalr={3'b000} iff (cov_item.opcode==7'b1100111);
        }
        j_instr2: coverpoint cov_item.opcode {
            bins jal={7'b1101111};
        }
        b_type: coverpoint cov_item.funct3 iff (cov_item.opcode==7'b1100011 ){
            bins beq={3'b000} ;
            bins bne={3'b001};
            bins blt={3'b100} ;
            bins bge={3'b101} ;
            bins bltu={3'b110} ;
            bins bgeu={3'b111} ;
        }
        u_type: coverpoint cov_item.opcode{
            bins lui={7'b0110111} ;
            bins auipc={7'b0010111};
        }
        m_extension: coverpoint cov_item.funct3 iff (cov_item.opcode==7'b0110011 && cov_item.funct7 == 7'b0000001 ){
            bins mul={3'b000} ;
            bins mulh={3'b001};
            bins mulsu={3'b010} ;
            bins mulu={3'b011} ;
            bins div={3'b100} ;
            bins divu={3'b101} ;
            bins rem={3'b110} ;
            bins remu={3'b111} ;
        }
        Immediate: coverpoint cov_item.imm[11:0]
        {
            bins all_zeros={12'h000};
            bins all_ones={12'hfff};
            bins min_value={12'h800};
            bins max_value={12'h7ff};
            bins rest=default;
        }
        instruction_Types:coverpoint cov_item.instruction_type;
        // cross coverage
        cross_rd_opcode:cross opcode,rd{
          ignore_bins s_type_no_rd = binsof(opcode.s_type);
          ignore_bins b_type_no_rd = binsof(opcode.b_type);
          }
        cross_rs1_opcode:cross opcode,rs1{
          ignore_bins u_type_no_rs1 = binsof(opcode.u_type);
          ignore_bins jal_no_rs1 = binsof(opcode.j_instr);
          }
        cross_rs2_opcode:cross opcode,rs2{
            ignore_bins i_type_reg_no_rs2 = binsof(opcode.i_type_reg) ;
            ignore_bins i_type_load_no_rs2 = binsof(opcode.i_type_load);
            ignore_bins u_type_no_rs2 = binsof(opcode.u_type);
            ignore_bins j_type_no_rs2 = binsof(opcode) intersect {7'b1101111, 7'b1100111};
        }
        
        


       

        
    endgroup
    function new (string name="Instruction_Coverage", uvm_component parent =null);
        super.new(name,parent);
        cg_instruction=new;

    endfunction
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        imp_instruction_cov=new("imp_instruction_cov",this);
    endfunction
    virtual function void write(Instruction_Seq_Item t);
        cov_item=t;
        cg_instruction.sample();

    endfunction
    function void report_phase (uvm_phase phase);

        `uvm_info("Instruction_Coverage", $sformatf("Instruction_Coverage =%0d%%", cg_instruction.get_coverage), UVM_NONE);
    endfunction

endclass
