/*######################################################################
## Class Name: Reg_Block
## Engineers : Abdelrahman Tamer - Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .It consists of all registers, maps, and memory.
######################################################################*/
`define REGISTER_NUM 32

class Reg_Block extends uvm_reg_block;
  	`uvm_object_utils(Reg_Block)

	// Declarations
   	Register_File_REG RF_REG [`REGISTER_NUM];
	mem_model  	Memory;    

	function new(string name = "Reg_Block");
		super.new(name);
	endfunction

	virtual function void build();
		// Build register file
		RF_REG[0] = Register_File_REG::type_id::create(.name("RF_REG[0]"), .parent(null), .contxt(get_full_name()));
		RF_REG[0].configure(.blk_parent(this));
		RF_REG[0].build();

		for (int i = 1; i < 32; i++) begin
			RF_REG[i] = Register_File_REG::type_id::create(.name($sformatf("RF_REG[%0d]",i)), .parent(null), .contxt(get_full_name()));
			RF_REG[i].configure(.blk_parent(this));
			RF_REG[i].build();
		end

		// Build the memory
		Memory = new(.name("Memory"));
		Memory.configure(.parent(this));

		// Create main address map
		default_map = create_map("default_map", `UVM_REG_ADDR_WIDTH'h0, 4, UVM_LITTLE_ENDIAN);

		// Map blocks:
		// - Registers start at 0x0000_0000
		// - Memory starts at 0x8000_0000
		for (int i = 0; i < `REGISTER_NUM; i++) begin
			if (i == 0) 
				default_map.add_reg(.rg(RF_REG[i]), .offset(i), .rights("RO"));
			else
				default_map.add_reg(.rg(RF_REG[i]), .offset(i), .rights("RW"));
		end

		default_map.add_mem(Memory, `UVM_REG_ADDR_WIDTH'h8000_0000, "RW");
	endfunction
endclass