
/*######################################################################
## Class Name: Data_Memory_Sequence  
## Engineer : Noureldeen Yehia
## Date: May 2025
######################################################################*/

class Data_Memory_Sequence extends uvm_sequence#(Data_Memory_Seq_Item);

// Factory Object Registration
    
    `uvm_object_utils(Data_Memory_Sequence);

    `uvm_declare_p_sequencer(Data_Memory_Sequencer);

// Factory Object Construction

    function new(string name = "Data_Memory_Sequence");
        
            super.new(name);
        
    endfunction

// int num_transactions = 30;

logic [31:0] rdata;

// Instance of Transaction

    Data_Memory_Seq_Item m_request;
    Data_Memory_Seq_Item m_response;

// Main Sequence Body
        
        virtual task body();


           forever

                begin

                    m_request = Data_Memory_Seq_Item::type_id::create("m_request");

                    m_response = Data_Memory_Seq_Item::type_id::create("m_response");
                    
                    // Wait for a transaction request from monitor via FIFO

                        p_sequencer.request_fifo.get(m_request);

                    // Generate response based on request type

                              start_item(m_response);

                                if (!m_request.data_we_o)

                                    begin
                                        
                                        rdata = p_sequencer.storage.read(m_request.data_addr_o);

                                        m_response.data_rvalid_i = 1;
                                        m_response.data_rdata_i = rdata;

                                        `uvm_info(get_type_name(), $sformatf("Reading = 0x%0h at Address = %0h", m_response.data_rdata_i, m_request.data_addr_o), UVM_LOW)

                                    end 

                                else

                                    begin
                                        
                                        p_sequencer.storage.write(m_request.data_addr_o, m_request.data_wdata_o);

                                        m_response.data_rvalid_i = 1;

                                        `uvm_info(get_type_name(), $sformatf("Writing Data = 0x%0h at Address = %0h", m_request.data_wdata_o, m_request.data_addr_o), UVM_LOW)

                                    end 

                              finish_item(m_response);

                end

        endtask 

endclass 