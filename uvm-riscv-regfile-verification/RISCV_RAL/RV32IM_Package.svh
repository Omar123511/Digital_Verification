
/*######################################################################
## Class Name: RV32IM_Package  
## Date: May 2025
######################################################################*/

import cv32e40p_pkg::*;
package RV32IM_Package;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    import cv32e40p_pkg::*;
    // the following types are used in instruction agent.
    typedef enum int { r_type,i_type_reg,i_type_load,i_type_jump,j_type,b_type,u_type,s_type,m_extension} type_formats;
    typedef enum int{add,sub,sll,slt,sltu,xor_op,srl,sra,or_op,and_op} rtype_instructions;
    typedef enum int{addi,slti,sltiu,xori,ori,andi,slli,srli,srai} itype_reg_imm_instructions;
    typedef enum int{lb,lh,lw,lbu,lhu} itype_load_instructions;
    typedef enum int{sb,sh,sw} stype_instructions;
    typedef enum int{jal,jalr} jump_instructions;
    typedef enum int{beq,bne,blt,bge,bltu,bgeu} btype_instructions;
    typedef enum int{lui,auipc} utype_instructions;
    typedef enum int {mul,mulh,mulsu,mulu,div,divu,rem,remu} m_instructions;
    

    
    // Instruction Sequence Item 
    `include "Seq_Items/Instruction_Seq_Item.svh"
    // Instruction Sequences
    `include "Sequences/Instruction_Sequences/Instruction_base_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_max_min_addi_sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_all_ones_addi_sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_zeros_ones_addi_sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_rand_sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_R_Type_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_addi_sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_I_Type_Register_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_Load_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_S_Type_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_M_Extension_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_B_Type_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_U_Type_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_Jump_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_signed_min_sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_xori_max_sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_mul_op_seq.svh"
    `include "Sequences/Instruction_Sequences/Instruction_rst_Sequence.svh"
    `include "Sequences/Instruction_Sequences/Instruction_corner_Cases_r_seq.svh"
    
    
    

   //Instruction Agent
    `include "Agents/Instruction_Agent/Instruction_Sequencer.svh"
    `include "Agents/Instruction_Agent/Instruction_Driver.svh"
    `include "Agents/Instruction_Agent/Instruction_Monitor.svh"
    `include "Agents/Instruction_Agent/Instruction_Agent_Config.svh"
    `include "Agents/Instruction_Agent/Instruction_Agent.svh"
    `include "Coverage_Collectors/Instruction_Coverage.svh"

    // Configuration Agent
    `include "Agents/Configuration_Agent/Configuration_cfg.sv"
    `include "Seq_Items/Configuration_Seq_Item.sv"
    `include "Agents/Configuration_Agent/Configuration_Driver.sv"
    `include "Agents/Configuration_Agent/Configuration_Monitor.sv"
    `include "Agents/Configuration_Agent/Configuration_Sequencer.sv"
    `include "Agents/Configuration_Agent/Configuration_Agent.sv"
    `include "Sequences/Configuration_Sequence.sv"
    `include "Coverage_Collectors/Configuration_Coverage.sv"
    
      // Register_File Agent
    `include "Seq_Items/Register_File_Sequence_Item.svh"
    `include "Sequences/Register_File_Sequence.svh"
    `include "Agents/RF_Agent/Register_File_Sequencer.svh"
    `include "Agents/RF_Agent/Register_File_Driver.svh"
    `include "Agents/RF_Agent/Register_File_Monitor.svh"
    `include "Agents/RF_Agent/Register_File_CFG.svh"
    `include "Agents/RF_Agent/Register_File_Agent.svh"
    `include "Coverage_Collectors/Register_File_Coverage.svh"

      // Data_Memory Agent
    `include "Seq_Items/Data_Memory_Seq_Item.sv"
    `include "Agents/Data_Memory_Agent/Data_Memory_Storage.sv"
    `include "Agents/Data_Memory_Agent/Data_Memory_Sequencer.sv"
    `include "Agents/Data_Memory_Agent/Data_Memory_Driver.sv"
    `include "Agents/Data_Memory_Agent/Data_Memory_Monitor.sv"
    `include "Agents/Data_Memory_Agent/Data_Memory_Config.sv"
    `include "Agents/Data_Memory_Agent/Data_Memory_Agent.sv"
    `include "Coverage_Collectors/Data_Memory_Coverage.sv"


    // RAL Components
    `include "RAL_Classes/RAL/RAL_Reg.svh"
    `include "RAL_Classes/RAL/RAL_MEM.svh"
    `include "RAL_Classes/RAL/RAL_Reg_Block.svh"
    `include "RAL_Classes/RAL/RAL_RF_Adapter.svh"
    `include "RAL_Classes/RAL/RAL_RF_Read_a_Adapter.svh"
    `include "RAL_Classes/RAL/RAL_RF_Read_b_Adapter.svh"
    `include "RAL_Classes/RAL/RAL_RF_Read_c_Adapter.svh"
    `include "RAL_Classes/RAL/RAL_DM_Adapter.svh"
    `include "RAL_Classes/RAL/RAL_Env.svh"

    `include "Sequences/Data_Memory_Sequence.sv"
    
     // Debug Agent
    `include "Seq_Items/Debug_Seq_Item.sv"
    `include "Sequences/Debug_Sequence.sv"
    `include "Agents/Debug_Agent/Debug_Sequencer.sv"
    `include "Agents/Debug_Agent/Debug_Driver.sv"
    `include "Agents/Debug_Agent/Debug_Monitor.sv"
    `include "Agents/Debug_Agent/Debug_Config.sv"
    `include "Agents/Debug_Agent/Debug_Agent.sv"
    
    // Interrupt Agent
    `include "Seq_Items/Interrupt_Seq_Item.sv"
    `include "Sequences/Interrupt_Sequence.sv"
    `include "Agents/Interrupt_Agent/Interrupt_Sequencer.sv"
    `include "Agents/Interrupt_Agent/Interrupt_Driver.sv"
    `include "Agents/Interrupt_Agent/Interrupt_Monitor.sv"
    `include "Agents/Interrupt_Agent/Interrupt_Config.sv"
    `include "Agents/Interrupt_Agent/Interrupt_Agent.sv"
    `include "Coverage_Collectors/Interrupt_Coverage.sv"
    
    // EX Agent
    `include "Seq_Items/EX_Seq_Item.sv"
    `include "Seq_Items/EX_Ref_Seq_Item.sv"
    `include "Agents/EX_Agent/EX_Sequencer.sv"
    `include "Agents/EX_Agent/EX_Driver.sv"
    `include "Agents/EX_Agent/EX_Monitor.sv"
    `include "Agents/EX_Agent/EX_Config.sv"
    `include "Agents/EX_Agent/EX_Ref_Model.sv"
    `include "Agents/EX_Agent/EX_Agent.sv"
    `include "Coverage_Collectors/EX_Coverage.sv"
    
 
    //virtual sequences
    `include "Env/Virtual_Sequencer.svh"
    `include "Virtual_Seq/Virtual_Base_Seq.svh"
    `include "Virtual_Seq/Virtual_R_Type_Seq.svh"
    `include "Virtual_Seq/Virtual_I_Type_Reg_Seq.svh"
    `include "Virtual_Seq/Virtual_I_Type_Load_Seq.svh"
    `include "Virtual_Seq/Virtual_S_Type_Seq.svh"
    `include "Virtual_Seq/Virtual_Store_Load_Seq.svh"
    `include "Virtual_Seq/Virtual_M_Extension_Seq.svh"
    `include "Virtual_Seq/Virtual_Interrupt_Seq.svh"
    `include "Virtual_Seq/Virtual_B_Type_Seq.svh"
    `include "Virtual_Seq/Virtual_U_Type_Seq.svh"
    `include "Virtual_Seq/Virtual_Jump_Seq.svh"
    `include "Virtual_Seq/Virtual_Rand_Seq.svh"
    `include "Virtual_Seq/Virtual_All_Ones_Seq.svh"
    `include "Virtual_Seq/Virtual_Zeros_Ones_Seq.svh"
    `include "Virtual_Seq/Virtual_Max_Min_Seq.svh"
    `include "Virtual_Seq/Virtual_addi_Seq.svh"
    `include "Virtual_Seq/Virtual_Signed_Max_Seq.svh"
     `include "Virtual_Seq/Virtual_Signed_Min_Seq.svh"
     `include "Virtual_Seq/Virtual_Corner_Cases_M_Seq.svh"
     `include "Virtual_Seq/Virtual_Corner_Cases_R_B_Seq.svh"
     // hazard sequences
    `include "Virtual_Seq/Hazard_Seq.svh"
     
    //env components
     `include "Scoreboard.svh"
    `include "Env/RV32IM_Env_Config.svh"
    `include "Env/RV32IM_Env.svh"
   
    //Instruction Tests 
    `include "Tests/Base_Test.svh"
    `include "Tests/R_Type_Test1.svh"
    `include "Tests/I_Type_Reg_Test1.svh"
    `include "Tests/I_Type_Load_Test.svh"
    `include "Tests/S_Type_Test.svh"
    `include "Tests/Store_Load_Test.svh"
    `include "Tests/M_Extension_Test.svh"
    `include "Tests/Interrupt_Test.svh"
    `include "Tests/B_Type_Test.svh"
    `include "Tests/U_Type_Test.svh"
    `include "Tests/Jump_Test.svh"
    `include "Tests/Rand_Test.svh"
    `include "Tests/All_Ones_Test.svh"
    `include "Tests/Zeros_Ones_Test.svh"
    `include "Tests/Max_Min_Test.svh"
    `include "Tests/Signed_Max_Test.svh" 
    `include "Tests/Signed_Min_Test.svh"
     
    // Hazard tests
    `include "Tests/Hazard_Test.svh"

   
endpackage
