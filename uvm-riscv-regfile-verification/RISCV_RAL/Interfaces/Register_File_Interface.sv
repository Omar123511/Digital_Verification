/*######################################################################
## Class Name: Register_File_Interface  
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .The interface contains the design ports.
######################################################################*/
interface Register_File_Interface ();
    bit clk;

    parameter ADDR_WIDTH = 6;
    parameter DATA_WIDTH = 32;
    parameter FPU        = 0;
    parameter ZFINX      = 0;
	
    logic rst_n;

    //Read port R1
    logic [ADDR_WIDTH-1:0] raddr_a_i;
    logic [DATA_WIDTH-1:0] rdata_a_o;

    //Read port R2
    logic [ADDR_WIDTH-1:0] raddr_b_i;
    logic [DATA_WIDTH-1:0] rdata_b_o;

    //Read port R3
    logic [ADDR_WIDTH-1:0] raddr_c_i;
    logic [DATA_WIDTH-1:0] rdata_c_o;

    // Write port W1
    logic [ADDR_WIDTH-1:0] waddr_a_i;
    logic [DATA_WIDTH-1:0] wdata_a_i;
    logic                  we_a_i;

    // Write port W2
    logic [ADDR_WIDTH-1:0] waddr_b_i;
    logic [DATA_WIDTH-1:0] wdata_b_i;
    logic                  we_b_i;
	
endinterface : Register_File_Interface