  /*###################################################################### 
## Class Name: Data_Memory_Ref_Model   
## Engineer   : Abdelrhman Tamer 
## Date       : May 2025 
## Description:  
    This UVM component represents the reference model for the Data Memory 
    in the RV32IM verification environment. It mimics the functional behavior 
    of the DUT's memory using an associative array and handles memory 
    transactions (read/write/reset) received from the DUT through an analysis FIFO. 
    
    - The model supports byte-enable based accesses for full-word, half-word, 
      and byte-level granularity.
    - It processes incoming transactions in the run phase and drives expected 
      values to the scoreboard via an analysis port.
    - Reset behavior clears internal memory state.
######################################################################*/

class Data_Memory_Ref_Model extends uvm_component; 
    `uvm_component_utils(Data_Memory_Ref_Model)
    uvm_analysis_port 		#(Data_Memory_Seq_Item) ref_to_scr_ap;

    uvm_analysis_export 	#(Data_Memory_Seq_Item) dut_to_ref_ap;
	uvm_tlm_analysis_fifo 	#(Data_Memory_Seq_Item) dut_to_ref_fifo;

	Data_Memory_Seq_Item dut_to_ref_trns;
	Data_Memory_Seq_Item ref_to_scr_trns; 

    static logic [31:0] mem [int]; // Associative array with int key
    bit has_been_reset = 0; // Track reset state


    function new(string name = "Data_Memory_Ref_Model", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ref_to_scr_ap  		= new("ref_to_scr_ap", this);
        dut_to_ref_ap  		= new("dut_to_ref_ap", this);
		dut_to_ref_fifo 	= new("dut_to_ref_fifo", this);
    endfunction : build_phase

    function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		dut_to_ref_ap.connect(dut_to_ref_fifo.analysis_export);
	endfunction


	extern function void print_mem();
    extern task Write_Assoc(input bit [31:0] addr, input bit [31:0] data);
	extern task Read_Assoc(input bit [31:0] addr, output bit [31:0] rdata);

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
		
		forever 
		begin
			dut_to_ref_fifo.get(dut_to_ref_trns);
			ref_to_scr_trns = Data_Memory_Seq_Item::type_id::create("ref_to_scr_trns");

			if (dut_to_ref_trns.data_we_o == 0) // read -load-
				begin
                    
					Read_Assoc(dut_to_ref_trns.data_addr_o, ref_to_scr_trns.data_rdata_i);
                    //print_mem();
                    ref_to_scr_trns.address = dut_to_ref_trns.data_addr_o;
                    ref_to_scr_trns.data    = ref_to_scr_trns.data_rdata_i;

                    ref_to_scr_ap.write(ref_to_scr_trns);		
				end
			else if (dut_to_ref_trns.data_we_o == 1) // write -store-
				begin
                    //print_mem();
					Write_Assoc(dut_to_ref_trns.data_addr_o, dut_to_ref_trns.data_wdata_o);
                    
                    ref_to_scr_trns.address = dut_to_ref_trns.data_addr_o;
                    ref_to_scr_trns.data    = dut_to_ref_trns.data_wdata_o;
                    ref_to_scr_ap.write(ref_to_scr_trns);				 		
				end 	
		end

	endtask : run_phase

endclass


///////////////////////////////////////////////////////// REFRENCE MODEL TASKS /////////////////////////////////////////////////
function void Data_Memory_Ref_Model::print_mem();
    foreach (mem[addr]) begin
        `uvm_info("MEM_DUMP", $sformatf("mem[%0h] = %0h", addr, mem[addr]), UVM_LOW)
    end
endfunction : print_mem


// Write -Store Case-
task Data_Memory_Ref_Model::Write_Assoc(input bit [31:0] addr, input bit [31:0] data);
    mem[addr] = data;
    has_been_reset = 0; // Clear reset flag after write
endtask

// Task to perform Read - Load Case - with byte/half-word enables
task Data_Memory_Ref_Model::Read_Assoc(
    input bit [31:0] addr, 
    output bit [31:0] rdata);

    logic [31:0] data;

    if (mem.exists(addr)) 
        begin
            rdata = mem[addr];
        end 
    else 
        begin // in case of read before write from this address we will randomize the data and put it in the array then read
            data      = '1;
            mem[addr] = data;
            rdata     = data;
        end
endtask
