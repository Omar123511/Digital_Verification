/*######################################################################
## Class Name: Instruction_Driver  
## Engineer : Omnia Mohamed
## Date: April 2025
## Description: 
    This class is responsible for constructing the instructions and driving them to the dut using the Open Bus Interface (OBI).
######################################################################*/
class Instruction_Driver extends uvm_driver#(Instruction_Seq_Item);
	`uvm_component_utils(Instruction_Driver)

    Instruction_Seq_Item item_drv;
    virtual Instruction_Interface vif;

    function new(string name="Instruction_Driver",uvm_component parent=null);
        super.new(name,parent);
    endfunction
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);

	endfunction
	task main_phase(uvm_phase phase);
		reset_item();
        forever begin
			`uvm_info("Instruction_Driver","main phase is started",UVM_MEDIUM)
			`uvm_info("Instruction_Driver","requests a new transaction from the sqr",UVM_MEDIUM)
        	seq_item_port.get_next_item(item_drv);
			`uvm_info("Instruction_Driver","got a new transaction from the sqr",UVM_MEDIUM)
		drive_item(item_drv);
            `uvm_info("Instruction_Driver",item_drv.sprint(),UVM_MEDIUM)
        	seq_item_port.item_done();
			`uvm_info("Instruction_Driver","main phase is finished",UVM_MEDIUM)
        end
    endtask
    // The following task drives the instuctions to dut using obi protocal in the following steps.
    /*  1- It constructs the instruction by concatenating fields according to supported instruction format types.
        2- It waits for the instr_req_o to be asserted high from dut as an indication of starting the address phase transfer.
        3- It asserts an instr_gnt_i signal high for one cycle to grant the request.
        4- It drives the instr_rdata_i with  instr_rvalid_i ==1 -> response phase .
        5- It asserts instr_rvalid_i low.
    */
    task drive_item(input Instruction_Seq_Item item_drv);
        if(item_drv.instruction_type == r_type || item_drv.instruction_type == m_extension)
            item_drv.instruction={item_drv.funct7,item_drv.rs2,item_drv.rs1,item_drv.funct3,item_drv.rd,item_drv.opcode};
        else if(item_drv.instruction_type == i_type_reg || item_drv.instruction_type ==i_type_load || item_drv.instruction_type ==i_type_jump)
           item_drv.instruction={item_drv.imm[11:0],item_drv.rs1,item_drv.funct3,item_drv.rd,item_drv.opcode};
        else if(item_drv.instruction_type == s_type)
            item_drv.instruction={item_drv.imm[11:5],item_drv.rs2,item_drv.rs1,item_drv.funct3,item_drv.imm[4:0],item_drv.opcode};
        else if(item_drv.instruction_type == j_type) 
            item_drv.instruction={item_drv.imm[20],item_drv.imm[10:1],item_drv.imm[11],item_drv.imm[19:12],item_drv.rd,item_drv.opcode};
        else if(item_drv.instruction_type == b_type)
            item_drv.instruction={item_drv.imm[12],item_drv.imm[10:5],item_drv.rs2,item_drv.rs1,item_drv.funct3,item_drv.imm[4:1],item_drv.imm[11],item_drv.opcode};
        else if(item_drv.instruction_type == u_type)
            item_drv.instruction={item_drv.imm[31:12],item_drv.rd,item_drv.opcode};

        @(posedge vif.clk iff vif.instr_req_o);
        vif.instr_gnt_i<=1'b1;
        @(posedge vif.clk);
        vif.instr_gnt_i<=1'b0;
        vif.instr_rvalid_i <= 1'b1;
        vif.instr_rdata_i <= item_drv.instruction;
        `uvm_info("Instruction_Driver",$sformatf("time=%0t rst_n=%0d instr_req_o=%0d instr_req_o=%0d addr_o=%0h gnt_i=%0d valid=%0d instr=%0h ",$time,vif.rst_n,vif.instr_req_o,vif.instr_req_o,vif.instr_addr_o,vif.instr_gnt_i,vif.instr_rvalid_i,vif.instr_rdata_i),UVM_MEDIUM)
	@(posedge vif.clk);
        vif.instr_rvalid_i <= 1'b0;
	if(item_drv.rst_mode==1)
		reset_item();
    endtask
    // the following task resets all input instruction interface signals.
	task reset_item();
	    @(posedge vif.clk);
	    vif.rst_n <= 1'b0;
            vif.instr_gnt_i<=1'b0;
            vif.instr_rvalid_i <= 1'b0;
            vif.instr_rdata_i <= '0;
	    @(posedge vif.clk);
            vif.rst_n <= 1'b1;
    endtask
endclass
