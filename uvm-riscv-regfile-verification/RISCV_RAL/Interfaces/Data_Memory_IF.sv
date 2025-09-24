/* *************** Data_Memory Interface ******************* */
interface Data_Memory_IF;
    // Define Signals
    bit clk;
    bit rst_n;

    // Outputs from LSU
    logic        data_req_o;                 // Request Signal
    logic        data_we_o;                  // Write Enable 
    logic [31:0] data_addr_o;                // Address
    logic [3:0]  data_be_o;                  // Byte Enable 
    logic [31:0] data_wdata_o;               // Data to be written to memory

    // Data Memory to LSU
    logic         data_gnt_i;               // Grant Signal to Acknowledge the Request
    logic         data_rvalid_i;            // Read Data Valid Signal, data is avilable on DM
    logic [31:0]  data_rdata_i;             // Data Read from Data Memory

    // IDs
    int Write_ID; //Store Transactions ID        
    int Read_ID;  //Load Transactions ID 
endinterface 