/*######################################################################
## Class Name: Data_Memory_Monitor 
## Engineer : Noureldeen Yahia
## Date: May 2025
######################################################################*/

class Data_Memory_Monitor extends uvm_monitor;

// Factory Component Registration
    `uvm_component_utils(Data_Memory_Monitor);


// Declare TLM Analysis Port to broadcast from Monitor to Sequencer

    uvm_analysis_port#(Data_Memory_Seq_Item) req_ap;

// Declare TLM Analysis Port to broadcast from Monitor to Referece Model

    uvm_analysis_port#(Data_Memory_Seq_Item) mon_to_ref_ap;

// Declare TLM Analysis Port to broadcast from Monitor to Agent

    uvm_analysis_port#(Data_Memory_Seq_Item) mon_ap;

// Factory Component Construction

        function new(string name = "Data_Memory_Monitor", uvm_component parent);
                
                super.new(name, parent);
            
        endfunction

// Instance of Transaction
    Data_Memory_Seq_Item mon_trans;

// Instance of Virtual Interface
    virtual Data_Memory_IF vif;

// Handle Storage component

     Data_Memory_Storage storage; 

// UVM Phases

        function void build_phase(uvm_phase phase);
                
                super.build_phase(phase);
                `uvm_info(get_type_name(), "Build Phase of Monitor", UVM_MEDIUM);

// Factory Object Creation

                    mon_trans = Data_Memory_Seq_Item::type_id::create("mon_trans");
                    
                    void'(uvm_config_db#(Data_Memory_Storage)::get(this, "", "Data_Memory_Storage", storage));

// Create TLM Analysis Ports

                            req_ap = new("req_ap", this);
                            mon_ap = new("mon_ap", this);
                            mon_to_ref_ap = new("mon_to_ref_ap", this);


        endfunction

        task main_phase(uvm_phase phase);

                   super.main_phase(phase);
                    `uvm_info(get_type_name(), "Run Phase of Monitor", UVM_MEDIUM);

// Forever loop to Monitor then broadcast

                forever 
                    begin

                        // Sample at Positive edge when there is a Request 

                            @(posedge vif.clk iff vif.data_req_o);

                        // Sample the outputs of DUT: Requests from the Virtual Interface

                                    mon_trans.rst_n = vif.rst_n;

                                    mon_trans.data_req_o = vif.data_req_o;
                                    mon_trans.data_we_o = vif.data_we_o;
                                    mon_trans.data_be_o = vif.data_be_o;
                                    mon_trans.data_addr_o = vif.data_addr_o;
                                    mon_trans.data_wdata_o = vif.data_wdata_o;

// Send Requests to TLM Analysis Port of Sequencer and Reference Model

                                    req_ap.write(mon_trans);
                                    mon_to_ref_ap.write(mon_trans);
                                    
                                    mon_trans.address = vif.data_addr_o;

                                    if(vif.data_we_o)
                                        
                                        begin
                                        
                                            mon_trans.data = vif.data_wdata_o;
                                         
                                        `uvm_info("WRITE_IN_MON", $sformatf(" Req = %b, WE = %b, BE = %b, Address = 0x%0h, Write Data = 0x%0h", mon_trans.data_req_o, mon_trans.data_we_o, mon_trans.data_be_o, mon_trans.address, mon_trans.data), UVM_LOW)

// Send Full Transaction to TLM Analysis Port of Agent

                                            mon_ap.write(mon_trans);
					
                            
                                @(posedge vif.clk iff vif.data_rvalid_i);
                                        
                                        end
                                    
                                    else 
                                        
                                        begin
                                        
                                            @(posedge vif.clk iff vif.data_rvalid_i);
                                            
                                                mon_trans.data_gnt_i = vif.data_gnt_i; 
                                                mon_trans.data_rvalid_i = vif.data_rvalid_i;
                                                mon_trans.data_rdata_i  = vif.data_rdata_i;
                                                mon_trans.data = vif.data_rdata_i;
                                        
                                        `uvm_info("READ_IN_MON", $sformatf("  Read Data = 0x%0h, Address= 0x%0h",  mon_trans.data,mon_trans.address), UVM_LOW)

// Send Full Transaction to TLM Analysis Port of Agent

                                             mon_ap.write(mon_trans);
                                    end

// Print the currently Sampled Requests

                       `uvm_info(get_type_name(), $sformatf(" Request Sampled: Req = %b, WE = %b, BE = %b, Address = 0x%0h, Write Data = 0x%0h", mon_trans.data_req_o, mon_trans.data_we_o, mon_trans.data_be_o, mon_trans.data_addr_o, mon_trans.data_wdata_o), UVM_LOW)
                                                                   

                            end

            endtask            

endclass
