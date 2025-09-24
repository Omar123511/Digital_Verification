/*######################################################################
## Class Name: Data_Memory_Sequence_Item  
## Engineer : Noureldeen Yehia
## Date: May 2025
######################################################################*/

class Data_Memory_Seq_Item extends uvm_sequence_item;

    function new(string name = "Data_Memory_Seq_Item");
        super.new(name);
    endfunction

    // Define the signals that will be in the transaction 
    logic rst_n;
    
    // Request Phase Fields (DUT ? TB)
    logic           data_req_o;           
    logic           data_we_o;             
    logic [31:0]    data_addr_o;           
    logic [3:0]     data_be_o;               
    logic [31:0]    data_wdata_o;           

    // Response Phase Fields (TB ? DUT)
    logic           data_gnt_i;         
    logic           data_rvalid_i;  
    logic [31:0]    data_rdata_i;  

    // used signals in ref_model 
    logic [31:0]    data;
    logic [31:0]     address;        
    static int Read_ID, Write_ID;

    `uvm_object_utils_begin(Data_Memory_Seq_Item)
        `uvm_field_int(data_req_o,UVM_ALL_ON )
        `uvm_field_int(data_we_o,UVM_ALL_ON)
        `uvm_field_int(data_addr_o,UVM_ALL_ON)
        `uvm_field_int(data_be_o,UVM_ALL_ON)
        `uvm_field_int(data_wdata_o,UVM_ALL_ON)
        `uvm_field_int(data_gnt_i,UVM_ALL_ON)
        `uvm_field_int(data_rvalid_i,UVM_ALL_ON)
        `uvm_field_int(data_rdata_i,UVM_ALL_ON)
        `uvm_field_int(data,UVM_ALL_ON)
        `uvm_field_int(address,UVM_ALL_ON)
    `uvm_object_utils_end

endclass 