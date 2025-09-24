
/*######################################################################
## Class Name: Data_Memory_Driver  
## Engineer : Noureldeen Yehia
## Date: May 2025
######################################################################*/

class Data_Memory_Driver extends uvm_driver#(Data_Memory_Seq_Item);

/*  Driver Class is parameterized with Transaction to pass it to seq_item_port #(REQ)
    and so we don't have to declare and construct it because it's already created implicitly */

// Factory Component Registration
    `uvm_component_utils(Data_Memory_Driver);

// Factory Component Construction

    function new(string name = "Data_Memory_Driver", uvm_component parent);
            
            super.new(name, parent);
        
    endfunction

// Instance of Transaction

    Data_Memory_Seq_Item stim_seq_item;

// Instance of Virtual Interface
    virtual Data_Memory_IF vif;

// UVM Phases

        function void build_phase(uvm_phase phase);
                
                super.build_phase(phase);
                `uvm_info(get_type_name(), "Build Phase of Driver", UVM_MEDIUM);

// Factory Object Creation
                    stim_seq_item = Data_Memory_Seq_Item::type_id::create("stim_seq_item");

        endfunction

        task main_phase(uvm_phase phase);

                super.main_phase(phase);
                `uvm_info(get_type_name(), "Run Phase of Driver", UVM_MEDIUM);

// Forever loop to drive transaction (Response) from Sequencer to DUT through vif

                    forever 
                        begin
                            vif.data_gnt_i    = 1'b0; 
                            vif.data_rvalid_i = 1'b0;
                            // Request Sequencer to get next transaction (Next Response)
                                seq_item_port.get_next_item(stim_seq_item);


                            // Wait until request is observed on DUT side

                                @(posedge vif.clk iff vif.data_req_o);

                                    @(posedge vif.clk);

                                        if (!vif.data_we_o) 

                                            begin 

                                                // Read 

                                                vif.data_gnt_i = 1; 

                                                @(posedge vif.clk); 

                                                    vif.data_gnt_i = 0;

						@(posedge vif.clk); 

                                                    vif.data_rvalid_i = 1; 
                                                    vif.data_rdata_i = stim_seq_item.data_rdata_i; 

                                            `uvm_info("READ_IN_DRV", $sformatf(" Read Data = 0x%0h ", vif.data_rdata_i), UVM_LOW)

                                            end 
                                        else 
                                            begin 
                                                
                                                // Write 
                                                
                                                vif.data_gnt_i = 1;

                                                @(posedge vif.clk); 

                                                    vif.data_gnt_i = 0; 
                                                    vif.data_rvalid_i = 1;
                                            end 
                                                
                                                @(posedge vif.clk); 
                                                    
                                                    vif.data_rvalid_i = 0;

                // RSP to Sequencer: Response has been sent to DUT through vif, send next item
                                seq_item_port.item_done();

                        end            
        endtask 

endclass

