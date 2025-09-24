/*######################################################################
## Class Name: Data_Memory_Sequence  
## Engineer : Noureldeen Yehia
## Date: May 2025
######################################################################*/

class Data_Memory_Sequence extends uvm_sequence#(Data_Memory_Seq_Item);

    // Factory Object Registration
    `uvm_object_utils(Data_Memory_Sequence)
    `uvm_declare_p_sequencer(Data_Memory_Sequencer)

    // Constructor
    function new(string name = "Data_Memory_Sequence");
        super.new(name);
    endfunction

    // Internal Data
    logic [31:0] rdata;

    // Transaction Instances
    Data_Memory_Seq_Item m_request;
    Data_Memory_Seq_Item m_response;

    // Main Sequence Body
    virtual task body();
        forever begin
            // Create Request & Response Items
            m_request  = Data_Memory_Seq_Item::type_id::create("m_request");
            m_response = Data_Memory_Seq_Item::type_id::create("m_response");

            // Wait for a transaction request from Monitor via FIFO
            p_sequencer.request_fifo.get(m_request);

            if (!m_request.data_we_o) 
                begin
                    // Read from memory
                    start_item(m_response);
                    rdata = p_sequencer.storage.read(m_request.data_addr_o);
                    m_response.data_rvalid_i = 1;
                    m_response.data_rdata_i  = rdata;

                    `uvm_info(get_type_name(),$sformatf("Reading Transaction of ID = %0d data= 0x%0h at Address = %0h",m_response.Read_ID, m_response.data_rdata_i, m_request.data_addr_o), UVM_LOW)
                    
                    finish_item(m_response);
                    m_response.Read_ID++;
                end 
            else
                begin
                    start_item(m_response);
                    p_sequencer.storage.write(m_request.data_addr_o, m_request.data_wdata_o);

                    m_response.data_rvalid_i = 1;

                    `uvm_info(get_type_name(),
                        $sformatf("Writing Transaction of ID = %0d, Data = 0x%0h, Address = %0h", m_response.Write_ID,m_request.data_wdata_o, m_request.data_addr_o), UVM_LOW)
                    finish_item(m_response);   
                    m_response.Write_ID ++;
                end  
                
        end
    endtask

endclass