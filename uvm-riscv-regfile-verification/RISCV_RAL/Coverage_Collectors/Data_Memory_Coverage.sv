
/*######################################################################
## Class Name: Data_Memory_Coverage Collector
## Engineer : Noureldeen Yahia
## Date: May 2025
## Description:  
    This class defines the Functional Coverage model for the Data Memory. 
######################################################################*/

class Data_Memory_Coverage extends uvm_subscriber#(Data_Memory_Seq_Item);

/*  Subscriber Class is parameterized with Transaction to pass it to analysis_export #(T)
    and so we don't have to declare and construct it because it's already created implicitly */

// Factory Component Registration
    `uvm_component_utils(Data_Memory_Coverage);

    // Declare TLM Analysis Implementation (imp) for Subscriber to receive Data 
        uvm_analysis_imp#(Data_Memory_Seq_Item, Data_Memory_Coverage) imp_sub;
  
// Instance of Transaction

    Data_Memory_Seq_Item cov_item;

  // Declare Covergroup and its Coverpoints

        covergroup Data_Memory_group;

  // Coverpoint: Request signal

  cp_req:  coverpoint cov_item.data_req_o iff (cov_item.rst_n) {
                                                                        bins requested = {1}; 
                                                                }


  // Coverpoint: Write Enable (1 = store, 0 = load)

  cp_we: coverpoint cov_item.data_we_o {
                                        bins load = {0};
                                        bins store = {1};
                                        }

// Byte enable indicates size and position of read/write

cp_byte_enable: coverpoint cov_item.data_be_o {

                                                bins lb_0 = {4'b0001};          // Load byte from lowest byte
                                                bins lb_1 = {4'b0010};          // Byte 1
                                                bins lb_2 = {4'b0100};          // Byte 2
                                                bins lb_3 = {4'b1000};          // Byte 3

                                                bins lh_01 = {4'b0011};         // Load halfword from byte 0-1
                                                bins lh_23 = {4'b1100};         // Load halfword from byte 2-3

                                                bins lw    = {4'b1111};         // Full word
                                            }



 // Coverpoint: Address Allgin

  cp_addr_allign: coverpoint cov_item.data_addr_o[1:0] {

                                                                bins byte0 = {2'b00};
                                                                bins byte1 = {2'b01};
                                                                bins byte2 = {2'b10};
                                                                bins byte3 = {2'b11};
                                                        }

  // Coverpoint: Read Data (32-bit) — Only when it’s a read
  cp_rdata: coverpoint cov_item.data_rdata_i iff (!cov_item.data_we_o) {
                                                                                bins zero_rdata = {32'h00000000};
                                                                                bins all_ones   = {32'hFFFFFFFF};
                                                                                bins byte_low   = {[0:255]};        // load byte
                                                                                bins hw_low     = {[0:65535]};      // load halfword
                                                                                bins others     = default;
                                                                        }


  // Coverpoint: Write Data
  cp_wdata : coverpoint cov_item.data_wdata_o iff (cov_item.data_we_o) {

                                                                                bins zero       = {32'h00000000};
                                                                                bins all_ones   = {32'hFFFFFFFF};
                                                                                bins byte_only  = {[8'h00:8'hFF]};
                                                                                bins upper_only = {[32'hFF000000:32'hFFFFFFFF]};
                                                                                bins others     = default;
                                                                        }


  // Cross Coverage: Byte Enable with Read/Write Enable
  
  cross_byte_we: cross cp_byte_enable, cp_we;


        endgroup
  
// Factory Component Construction

        function new(string name = "Data_Memory_Coverage", uvm_component parent);

                super.new(name, parent);

// Create Coverage Group (Allocate it in memory)

                Data_Memory_group = new();

        endfunction

// Write Function

                function void write(Data_Memory_Seq_Item t);
                    
                            cov_item = t;
                            Data_Memory_group.sample();
                    
                endfunction


// UVM Phases

        function void build_phase(uvm_phase phase);
                
                super.build_phase(phase);
                `uvm_info(get_type_name(), "Build Phase of Subscriber", UVM_MEDIUM);

// Factory Object Creation
                cov_item = Data_Memory_Seq_Item::type_id::create("cov_item");

// Create TLM Analysis Imp for Coverage Collector to get data from Monitor

               imp_sub = new("imp_sub", this);


        endfunction

        function void connect_phase(uvm_phase phase);
                
                super.connect_phase(phase);
                `uvm_info(get_type_name(), "Connect Phase of Subscriber", UVM_MEDIUM);
            
        endfunction



// Use Extract Phase to Print the Final Coverage Precentage

        function void extract_phase(uvm_phase phase);
                
                super.extract_phase(phase);
                `uvm_info(get_type_name(), "Extract Phase of Subscriber", UVM_MEDIUM);

                `uvm_info(get_type_name(), $sformatf("Final Coverage is: %0.2f%%", Data_Memory_group.get_coverage()), UVM_MEDIUM);
            
        endfunction


endclass 

