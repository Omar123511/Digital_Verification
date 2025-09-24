class mem_model extends uvm_mem; 
    `uvm_object_utils(mem_model) 

    // Associative array to model the mirror values written in RAL mem map since uvm_mem doesn't have mirror values 
    static logic [31:0] mirror_mem [int]; 
    
    function new(string name = "mem_model"); 
        super.new(name, 2**32, 32, "RW", UVM_NO_COVERAGE); 
    endfunction 

    task Write(input bit [31:0] addr, input bit [31:0] data);
        mirror_mem[addr] = data;
        `uvm_info("MEM_MODEL", $sformatf("addr=0x%0h, data=0x%0h", addr, mirror_mem[addr]), UVM_LOW);
    endtask

    task Read(input bit [31:0] addr, output bit [31:0] rdata);
        logic [31:0] data;

        if (mirror_mem.exists(addr)) 
            begin
                rdata = mirror_mem[addr];
            end 
        else 
            begin // in case of read before write from this address we will put the data to 1 and put it in the array then read
                data      = '1;
                mirror_mem[addr] = data;
                rdata     = data;
            end
    endtask

endclass: mem_model 