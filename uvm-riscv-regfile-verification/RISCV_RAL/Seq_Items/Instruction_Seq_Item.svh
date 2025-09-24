/*######################################################################
## Class Name: Instruction_Seq_Item  
## Engineer : Omnia Mohamed
## Date: April 2025
## Description: 
    .This class contains the transaction level signals that represent the fields of instruction, supporting different instruction type formats.
    .It supports base integer instructions "I" & Integer multiplication and divison "M-extension".
######################################################################*/
class Instruction_Seq_Item extends uvm_sequence_item;

rand bit[6:0] opcode;
randc bit[4:0] rd;
rand bit[2:0] funct3;
randc bit[4:0] rs1;
randc bit[4:0] rs2;
rand bit[6:0] funct7;
rand bit signed[31:0] imm;
rand bit rst_mode;

int instruction_mem[int];// represents an associative array of instructions
int instruction;// holds the signal that will be created later in driver
int address;// contains the address of instruction to be fetched.

randc type_formats instruction_type;// this enum is used to select the format type.
randc rtype_instructions rtype;// this enum is used to select the R-type instruction.
randc itype_reg_imm_instructions itype_reg;// this enum is used to select the I-type Register immediate instruction.
randc itype_load_instructions itype_load;// this enum is used to select the I-type load instruction.
randc stype_instructions stype;// this enum is used to select the S-type instruction.
randc jump_instructions j_instr;// this enum is used to select the Jump instruction.
randc btype_instructions btype;// this enum is used to select the B-type instruction.
randc utype_instructions utype;// this enum is used to select the U-type instruction.
randc m_instructions m_instr;// this enum is used to select the m extension instruction.

//The following constraint constains the valid values of opcode for the supported instruction types.
constraint opcode_valid_values_c{
    opcode inside {7'b0110011,7'b0010011,7'b0000011,7'b0100011,7'b1101111,7'b1100111,7'b1100011, 7'b0110111,7'b0010111};
}
constraint valid_registers_values_c{
    rs1 inside {[0:31]};
    rs2 inside {[0:31]};
    rd inside {[1:31]};// x0 is read only.
}
// The following constraint is for Integer Register-Register Instructions which follow  R-type format.
constraint r_type_c{
    if(instruction_type ==r_type ){
        opcode == 7'b0110011;
        if (rtype == add || rtype== sub){
            funct3 == 3'b000;
        }
        (rtype == sll) -> funct3 == 3'b001;
        (rtype == slt) -> funct3 == 3'b010;
        (rtype == sltu) -> funct3 == 3'b011;
        (rtype == xor_op) -> funct3 == 3'b100;
        (rtype == srl) -> funct3 == 3'b101;
        (rtype == sra) -> funct3 == 3'b101;
        (rtype == or_op) -> funct3 == 3'b110;
        (rtype == and_op) -> funct3 == 3'b111;
        if (rtype != sub && rtype != sra ){
            funct7 == 7'b0000000;
        }
        (rtype == sub) -> funct7 == 7'b0100000;
        (rtype == sra) -> funct7 == 7'b0100000;
    }

}
// The following constraint is for Integer Register-Immediate Instructions which follow I-type format.
constraint i_type_reg_c{ 
    if(instruction_type ==i_type_reg ){
        opcode == 7'b0010011;
        (itype_reg == addi) -> funct3==3'b000;
        (itype_reg == slti) -> funct3==3'b010;
        (itype_reg == sltiu)-> funct3==3'b011;
        (itype_reg == xori) -> funct3==3'b100;
        (itype_reg == ori) ->  funct3==3'b110;
        (itype_reg == andi) -> funct3==3'b111;
        (itype_reg == slli) -> funct3==3'b001 && imm[11:5]=='0 ;
        (itype_reg == srli) -> funct3==3'b101 && imm[11:5]=='0 ;
        (itype_reg == srai) -> funct3==3'b101 && imm[11:5]==7'b0100000 ;
    }
}
// The following constraint is for Load Instructions which follow I-type format.
constraint i_type_load_c{
    if(instruction_type ==i_type_load ){
        opcode == 7'b0000011;
        (itype_load == lb) -> funct3==3'b000;
        (itype_load == lh) -> funct3==3'b001;
        (itype_load == lw)-> funct3==3'b010;
        (itype_load == lbu) -> funct3==3'b100;
        (itype_load == lhu) -> funct3==3'b101;
    }
}
// The following constraint is for Store Instructions which follow S-type format.
constraint s_type_c{
    if(instruction_type ==s_type ){
        opcode == 7'b0100011;
        (stype == sb) -> funct3==3'b000;
        (stype == sh) -> funct3==3'b001;
        (stype == sw)-> funct3==3'b010;
    }
}
// The following constraint is for Jump Instructions.
constraint jump_c{
    if(instruction_type ==j_type ){
        (j_instr == jal) -> opcode == 7'b1101111; //jal instruction follows the J-type format
    }
    else if(instruction_type ==i_type_jump ){
        (j_instr == jalr) -> opcode == 7'b1100111 && funct3==3'b000; //jalr instruction follows the I-type format
    }
}
// The following constraint is for branch Instructions which follow B-type format.
constraint b_type_c{
    if(instruction_type ==b_type ){
        opcode == 7'b1100011;
        (btype == beq) -> funct3==3'b000;
        (btype == bne) -> funct3==3'b001;
        (btype == blt)-> funct3==3'b100;
        (btype == bge) -> funct3==3'b101;
        (btype == bltu) -> funct3==3'b110;
        (btype == bgeu) -> funct3==3'b111;
    }
}
// The following constraint is for U type instructions
constraint u_type_c{
    if(instruction_type ==u_type ){
        ( utype ==lui )-> opcode == 7'b0110111;
        ( utype ==auipc )-> opcode == 7'b0010111;
    }
}
// M-extension for Integer multiplication and division instructions which follow R-type format.
constraint m_extension_c{
    if(instruction_type ==m_extension ){
        opcode == 7'b0110011;
        funct7 == 7'b0000001;
        (m_instr == mul) -> funct3 ==3'b000;
        (m_instr == mulh) -> funct3 ==3'b001;
        (m_instr == mulsu) -> funct3 ==3'b010;
        (m_instr == mulu) -> funct3 ==3'b011;
        (m_instr == div) -> funct3 ==3'b100;
        (m_instr == divu) -> funct3 ==3'b101;
        (m_instr == rem) -> funct3 ==3'b110;
        (m_instr == remu) -> funct3 ==3'b111;
    }
}
constraint enable_reset{
	rst_mode ==0;
}

function new(string name="Instruction_Seq_Item");
    super.new(name);
endfunction

`uvm_object_utils_begin(Instruction_Seq_Item)
    `uvm_field_int(opcode,UVM_ALL_ON )
    `uvm_field_int(rd,UVM_ALL_ON)
    `uvm_field_int(funct3,UVM_ALL_ON)
    `uvm_field_int(rs1,UVM_ALL_ON)
    `uvm_field_int(rs2,UVM_ALL_ON)
    `uvm_field_int(funct7,UVM_ALL_ON)
    `uvm_field_int(imm,UVM_ALL_ON)
    `uvm_field_int(instruction,UVM_ALL_ON)
    `uvm_field_int(address,UVM_ALL_ON)
    `uvm_field_aa_int_int(instruction_mem,UVM_ALL_ON) 
    `uvm_field_enum(type_formats,instruction_type,UVM_ALL_ON)
    `uvm_field_enum(rtype_instructions,rtype,UVM_ALL_ON)
    `uvm_field_enum(itype_reg_imm_instructions,itype_reg,UVM_ALL_ON)
    `uvm_field_enum(itype_load_instructions,itype_load,UVM_ALL_ON)
    `uvm_field_enum(stype_instructions,stype,UVM_ALL_ON)
    `uvm_field_enum(jump_instructions,j_instr,UVM_ALL_ON)
    `uvm_field_enum(btype_instructions,btype,UVM_ALL_ON)
    `uvm_field_enum(utype_instructions,utype,UVM_ALL_ON) 
    `uvm_field_enum(m_instructions,m_instr,UVM_ALL_ON) 
 
`uvm_object_utils_end

endclass:Instruction_Seq_Item
