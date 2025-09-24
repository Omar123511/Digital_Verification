/*######################################################################
## Class Name: Register_File_REG
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .It mimics the register in the design and represents its field.
######################################################################*/
class Register_File_REG extends uvm_reg;
	`uvm_object_utils(Register_File_REG)

	// Declare the field
    uvm_reg_field VAL_FIELD;

	// Constructor
	function new(string name = "Register_File_REG");
		super.new(name, 32, build_coverage(UVM_NO_COVERAGE)); // 32-bit register, no coverage
	endfunction

	// Build function to define fields
	virtual function void build();
		VAL_FIELD = uvm_reg_field::type_id::create("VAL_FIELD", null, get_full_name());
        VAL_FIELD.configure(    .parent                 (this),
                                .size                   (32),
                                .lsb_pos                (0),
                                .access                 ("RW"),
                                .volatile               (0),
                                .reset                  ('h0),
                                .has_reset              (1),
                                .is_rand                (0),
                                .individually_accessible(1));     
	endfunction

endclass