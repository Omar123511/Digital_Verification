/*######################################################################
## Class Name: Data_Memory_Storage  
## Engineer : Noureldeen Yahia
## Date: May 2025
######################################################################*/

class Data_Memory_Storage extends uvm_component;

    // Memory array
    static bit [31:0] mem[int];

    // Factory registration
    `uvm_component_utils(Data_Memory_Storage)

    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);    
    endfunction

    // Write method
    function void write(int addr, int value);
        mem[addr] = value;
        `uvm_info("STORAGE_Write",
                  $sformatf("Write Value = 0x%0h is written at addr = 0x%0h", value, addr),
                  UVM_LOW)
    endfunction

    // Read method
    function int read(int addr);
        int data;

        if (mem.exists(addr)) 
            begin
                data = mem[addr];
                `uvm_info("STORAGE_Read",
                        $sformatf("READ 0x%0h FROM addr = 0x%0h", data, addr),
                        UVM_LOW)
            end 
        else 
            begin
                `uvm_info("STORAGE_Read",
                        $sformatf("Address 0x%0h is not initialized, initializing storage with 1", addr),
                        UVM_LOW)

                data = '1; 
                mem[addr] = data;

                `uvm_info("STORAGE_Read",
                        $sformatf("READ after initializing data: 0x%0h for addr = 0x%0h", data, addr),
                        UVM_LOW)
            end

        return data;
    endfunction

endclass
