/*###################################################################### 
## Module Name: Top tb for RV32IM 
## Team : Team2
## Date: May 2025 
## Description:  
    This is the top-level module used to instantiate and connect the DUT 
    (cv32e40p_top), interface instances, and SVA modules for formal and dynamic 
    verification. It also sets up the clocking environment and uses UVM Configuration 
    Database (uvm_config_db) to pass virtual interface handles to the UVM testbench. 
######################################################################*/

import RV32IM_Package ::*;
module RV32IM_Top_Tb();

Instruction_Interface instruction_ifc();
Data_Memory_IF data_memory_ifc();
Configuration_IF config_ifc();
Debug_Interface debug_ifc();
EX_Interface ex_ifc();
Interrupt_IF interrupt_ifc();
Register_File_Interface RF_ifc();
cv32e40p_top #(
    .FPU                      ( 0 ),
    .FPU_ADDMUL_LAT           ( 0 ),
    .FPU_OTHERS_LAT           ( 0 ),
    .ZFINX                    ( 0 ),
    .COREV_PULP               ( 0 ),
    .COREV_CLUSTER            ( 0 ),
    .NUM_MHPMCOUNTERS         ( 1 )
) u_core (
    .rst_ni                   (instruction_ifc.rst_n),
    .clk_i                    (instruction_ifc.clk),
    .scan_cg_en_i             (config_ifc.scan_cg_en_i),
    .fetch_enable_i           (config_ifc.fetch_enable_i),
    .pulp_clock_en_i          (config_ifc.pulp_clock_en_i)  ,
    .core_sleep_o              (config_ifc.core_sleep_o)         ,

    // Configuration
    .boot_addr_i              (config_ifc.boot_addr_i),
    .mtvec_addr_i             (config_ifc.mtvec_addr_i),
    .dm_halt_addr_i           (config_ifc.dm_halt_addr_i),
    .dm_exception_addr_i      (config_ifc.dm_exception_addr_i),
    .hart_id_i                (config_ifc.hart_id_i),

    // Instruction memory interface
    .instr_addr_o             (instruction_ifc.instr_addr_o),
    .instr_req_o              (instruction_ifc.instr_req_o),
    .instr_gnt_i              (instruction_ifc.instr_gnt_i),
    .instr_rvalid_i           (instruction_ifc.instr_rvalid_i),
    .instr_rdata_i            (instruction_ifc.instr_rdata_i),

 
    .data_addr_o  (data_memory_ifc.data_addr_o  )     ,
    .data_req_o   (data_memory_ifc.data_req_o  )     ,
    .data_gnt_i   (data_memory_ifc.data_gnt_i)     ,
    .data_we_o    (data_memory_ifc.data_we_o )     ,
    .data_be_o    (data_memory_ifc.data_be_o )     ,
    .data_wdata_o (data_memory_ifc.data_wdata_o)     ,
    .data_rvalid_i(data_memory_ifc.data_rvalid_i)     ,
    .data_rdata_i (data_memory_ifc.data_rdata_i )     ,

     // Interrupt interface
    .irq_i      ( interrupt_ifc.irq_i )              ,
    .irq_ack_o  ( interrupt_ifc.irq_ack_o )              ,
    .irq_id_o   ( interrupt_ifc.irq_id_o )              ,

    // Debug interface
    .debug_req_i           (debug_ifc.debug_req_i  )   ,
    .debug_havereset_o     (debug_ifc.debug_havereset_o  )   ,
    .debug_running_o       (debug_ifc.debug_running_o  )   ,
    .debug_halted_o        (debug_ifc.debug_halted_o  )   
);
// assertions modules binds
bind u_core Instruction_SVA instruction_SVA_inst 	(instruction_ifc.clk,instruction_ifc.rst_n,instruction_ifc.instr_gnt_i,instruction_ifc.instr_rvalid_i,instruction_ifc.instr_rdata_i,instruction_ifc.instr_req_o,instruction_ifc.instr_addr_o);
bind u_core Interrupt_SVA	 Interrupt_SVA_inst (
    	.clk(interrupt_ifc.clk), 
    	.rst_n(interrupt_ifc.rst_n),
		.irq_i(interrupt_ifc.irq_i),
		.irq_ack_o(interrupt_ifc.irq_ack_o),
		.irq_id_o(interrupt_ifc.irq_id_o),
		.Mode(interrupt_ifc.Mode), 
		.Enable(interrupt_ifc.Enable)
		);
bind u_core Data_Memory_SVA Data_Memory_SVA_inst(data_memory_ifc.clk,data_memory_ifc.rst_n,data_memory_ifc.data_req_o,data_memory_ifc.data_we_o,data_memory_ifc.data_addr_o,data_memory_ifc.data_be_o,data_memory_ifc.data_wdata_o,data_memory_ifc.data_gnt_i,data_memory_ifc.data_rvalid_i,data_memory_ifc.data_rdata_i);
assign interrupt_ifc.Mode   = u_core.core_i.cs_registers_i.mtvec_mode_o;
assign interrupt_ifc.Enable = u_core.core_i.cs_registers_i.mstatus_n.mie;
bind u_core.core_i.ex_stage_i EX_SVA EX_SVA_inst(.ex_ifc(RV32IM_Top_Tb.ex_ifc));


// Bind always block for EX Agent
always_comb begin
    ex_ifc.rst_n                = u_core.core_i.ex_stage_i.rst_n;
    ex_ifc.wb_ready_i           = u_core.core_i.ex_stage_i.wb_ready_i;

    ex_ifc.alu_operator_i       = u_core.core_i.ex_stage_i.alu_operator_i;
    ex_ifc.alu_operand_a_i      = u_core.core_i.ex_stage_i.alu_operand_a_i;
    ex_ifc.alu_operand_b_i      = u_core.core_i.ex_stage_i.alu_operand_b_i;
    ex_ifc.alu_operand_c_i      = u_core.core_i.ex_stage_i.alu_operand_c_i;
    ex_ifc.alu_en_i             = u_core.core_i.ex_stage_i.alu_en_i;
    ex_ifc.apu_en_i             = u_core.core_i.ex_stage_i.apu_en_i;
    ex_ifc.lsu_en_i             = u_core.core_i.ex_stage_i.lsu_en_i;
    ex_ifc.csr_access_i         = u_core.core_i.ex_stage_i.csr_access_i;
    ex_ifc.apu_rvalid_i         = u_core.core_i.ex_stage_i.apu_rvalid_i;
    ex_ifc.lsu_ready_ex_i       = u_core.core_i.ex_stage_i.lsu_ready_ex_i;
    ex_ifc.branch_in_ex_i       = u_core.core_i.ex_stage_i.branch_in_ex_i;

    ex_ifc.mult_operator_i      = u_core.core_i.ex_stage_i.mult_operator_i;
    ex_ifc.mult_operand_a_i     = u_core.core_i.ex_stage_i.mult_operand_a_i;
    ex_ifc.mult_operand_b_i     = u_core.core_i.ex_stage_i.mult_operand_b_i;
    ex_ifc.mult_en_i            = u_core.core_i.ex_stage_i.mult_en_i;
    ex_ifc.mult_signed_mode_i   = u_core.core_i.ex_stage_i.mult_signed_mode_i;

    ex_ifc.regfile_alu_we_i     = u_core.core_i.ex_stage_i.regfile_alu_we_i;
    ex_ifc.regfile_alu_waddr_i  = u_core.core_i.ex_stage_i.regfile_alu_waddr_i;

    ex_ifc.alu_is_subrot_i      = u_core.core_i.ex_stage_i.alu_is_subrot_i;
    ex_ifc.alu_is_clpx_i        = u_core.core_i.ex_stage_i.alu_is_clpx_i;
    ex_ifc.alu_vec_mode_i       = u_core.core_i.ex_stage_i.alu_vec_mode_i;
    ex_ifc.bmask_b_i            = u_core.core_i.ex_stage_i.bmask_b_i;
    ex_ifc.mult_is_clpx_i       = u_core.core_i.ex_stage_i.mult_is_clpx_i;
    ex_ifc.mult_operand_c_i     = u_core.core_i.ex_stage_i.mult_operand_c_i;
    ex_ifc.mult_sel_subword_i   = u_core.core_i.ex_stage_i.mult_sel_subword_i;
    ex_ifc.mult_imm_i           = u_core.core_i.ex_stage_i.mult_imm_i;
    ex_ifc.mult_multicycle_o    = u_core.core_i.ex_stage_i.mult_multicycle_o;
    ex_ifc.branch_decision_o    = u_core.core_i.ex_stage_i.branch_decision_o;
    ex_ifc.regfile_alu_wdata_fw_o    = u_core.core_i.ex_stage_i.regfile_alu_wdata_fw_o;
    ex_ifc.jump_target_o        = u_core.core_i.ex_stage_i.jump_target_o;
    ex_ifc.regfile_alu_waddr_fw_o   = u_core.core_i.ex_stage_i.regfile_alu_waddr_fw_o;
    ex_ifc.regfile_alu_we_fw_o  = u_core.core_i.ex_stage_i.regfile_alu_we_fw_o;
    ex_ifc.ex_valid_o           = u_core.core_i.ex_stage_i.ex_valid_o;
    ex_ifc.ex_ready_o           = u_core.core_i.ex_stage_i.ex_ready_o;
end
// Bind always block for RF Agent

always_comb begin
    RF_ifc.rst_n         = u_core.core_i.id_stage_i.register_file_i.rst_n;
    
    RF_ifc.raddr_a_i     = u_core.core_i.id_stage_i.register_file_i.raddr_a_i;
    RF_ifc.rdata_a_o     = u_core.core_i.id_stage_i.register_file_i.rdata_a_o;

    RF_ifc.raddr_b_i     = u_core.core_i.id_stage_i.register_file_i.raddr_b_i;
    RF_ifc.rdata_b_o     = u_core.core_i.id_stage_i.register_file_i.rdata_b_o;

    RF_ifc.raddr_c_i     = u_core.core_i.id_stage_i.register_file_i.raddr_c_i;
    RF_ifc.rdata_c_o     = u_core.core_i.id_stage_i.register_file_i.rdata_c_o;

    RF_ifc.waddr_a_i     = u_core.core_i.id_stage_i.register_file_i.waddr_a_i;
    RF_ifc.wdata_a_i     = u_core.core_i.id_stage_i.register_file_i.wdata_a_i;
    RF_ifc.we_a_i        = u_core.core_i.id_stage_i.register_file_i.we_a_i;

    RF_ifc.waddr_b_i     = u_core.core_i.id_stage_i.register_file_i.waddr_b_i;
    RF_ifc.wdata_b_i     = u_core.core_i.id_stage_i.register_file_i.wdata_b_i;
    RF_ifc.we_b_i        = u_core.core_i.id_stage_i.register_file_i.we_b_i;
end

//clk generation
  initial begin
	  forever #5 instruction_ifc.clk= ~instruction_ifc.clk;
  end
  initial begin
	  forever #5 data_memory_ifc.clk= ~data_memory_ifc.clk;
  end
  initial begin
	  forever #5 config_ifc.clk= ~config_ifc.clk;
  end
   initial begin
	  forever #5 debug_ifc.clk= ~debug_ifc.clk;
  end
   initial begin
	  forever #5 ex_ifc.clk= ~ex_ifc.clk;
  end
   initial begin
	  forever #5 interrupt_ifc.clk= ~interrupt_ifc.clk;
  end
   initial begin
      forever #5 RF_ifc.clk= ~RF_ifc.clk;
  end
  assign data_memory_ifc.rst_n =instruction_ifc.rst_n;
  assign interrupt_ifc.rst_n =instruction_ifc.rst_n;
  initial begin
      uvm_config_db#(virtual Instruction_Interface)::set(null,"uvm_test_top","instruction_vif",instruction_ifc);
      uvm_config_db#(virtual Data_Memory_IF)::set(null,"uvm_test_top","Data_Memory_vif",data_memory_ifc);
      uvm_config_db#(virtual Configuration_IF)::set(null,"uvm_test_top","configuration_vif",config_ifc);
      uvm_config_db#(virtual Debug_Interface)::set(null,"uvm_test_top","debug_vif",debug_ifc);
      uvm_config_db#(virtual EX_Interface)::set(null,"uvm_test_top","ex_vif",ex_ifc);
      uvm_config_db#(virtual Interrupt_IF)::set(null,"uvm_test_top","interrupt_vif",interrupt_ifc);
      uvm_config_db#(virtual Register_File_Interface)::set(null,"uvm_test_top","RF_vif",RF_ifc);

      run_test();
  end
  initial begin
    $dumpfile("RV32IM_Top_Tb.vcd");
    $vcdpluson;
    $dumpvars;
  end
/*`ifdef FSDB
initial begin
    $fsdbDumpfile("waves.fsdb");
    $vcdpluson;
    $fsdbDumpvars(0,RV32IM_Top_Tb);
  end
`endif*/
endmodule
