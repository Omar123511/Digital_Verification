
/*######################################################################
## Class Name: Data_Memory_Config  
## Engineer : Noureldeen Yehia
## Date: May 2025
######################################################################*/

class Data_Memory_Config extends uvm_object;


// Factory Object Registration

	`uvm_object_utils(Data_Memory_Config)

// Instance of Virtual Interface

    virtual Data_Memory_IF Data_Memory_vif;

	uvm_active_passive_enum Data_Memory_is_active;

// Constructor

    function new(string name = "Data_Memory_Config");
	
    	super.new(name);
	
    endfunction 

endclass