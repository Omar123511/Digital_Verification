
/*######################################################################
## Class Name: Data_Memory_Assertions 
## Engineer : Noureldeen Yahia
## Date: May 2025
## Description:
    .This module perform checks on Data Interface .
    .It verifies the handshake between DUT and Data Memory Agent based on OBI protocol.
######################################################################*/

module Data_Memory_SVA  (
                        
                            input bit clk,
                            input bit rst_n,
                            
                            input logic        data_req_o,               
                            input logic        data_we_o,                 
                            input logic [31:0] data_addr_o,                
                            input logic [3:0]  data_be_o,                  
                            input logic [31:0] data_wdata_o,             

                            input logic         data_gnt_i,             
                            input logic         data_rvalid_i,           
                            input logic [31:0]  data_rdata_i            
                        );

 
// Assertion 1: When Reset is low the Request, Enable, Valid should be low

    property Reset_Check;

        @(posedge clk) (!rst_n) |-> (!data_req_o && !data_we_o && !data_rvalid_i);
 
    endproperty

// Assertion 2: There will be no Surpious Grant when there's no request

    property No_Spurious_Grant;

        @(posedge clk) disable iff (!rst_n) (!data_req_o) |-> (!data_gnt_i);
 
    endproperty

// Assertion 3: Grant should only be asserted when there's a request

    property Grant_Check_A;

        @(posedge clk) disable iff (!rst_n) (data_gnt_i) |-> (data_req_o);
 
    endproperty

// Assertion 4: Grant should be deasserted after one cycle

    property Grant_Check_B;

        @(posedge clk) disable iff (!rst_n) (data_gnt_i) |=> (!data_gnt_i);
 
    endproperty

// Assertion 5: Valid handshake: When there's a request and its granted then Data Memory is ready for read or write

    property Handshake_Check;

        @(posedge clk) disable iff (!rst_n) (data_req_o && data_gnt_i) |-> (data_we_o || !data_we_o);
 
    endproperty

// Assertion 6: R_Valid should be one cycle only

    property R_Valid_Check_A;

        @(posedge clk) disable iff (!rst_n) $rose(data_rvalid_i) |=> (!data_rvalid_i);
 
    endproperty

// Assertion 7: R_Valid should high after one cycle from granting a request for read operations

    property R_Valid_Check_B;

        @(posedge clk) disable iff (!rst_n) (data_req_o && !data_we_o && data_gnt_i) |-> ##2 (data_rvalid_i);
 
    endproperty

// Assertion 8: R_Valid should high after one cycle from granting a request for write operations

    property R_Valid_Check_C;

        @(posedge clk) disable iff (!rst_n) (data_req_o && data_we_o && data_gnt_i) |-> ##1 (data_rvalid_i);
 
    endproperty

// Assertion 9: Read data shouldn't be x or z when r_valid is high

    property Read_Data_Check;

        @(posedge clk) disable iff (!rst_n) (data_rvalid_i && !data_we_o && $past(data_gnt_i,2) ) |-> !($isunknown(data_rdata_i));
 
    endproperty

// Assertion 10: Write data shouldn't be x or z when r_valid is high

    property Write_Data_Check;

        @(posedge clk) disable iff (!rst_n) (data_rvalid_i && data_we_o) |-> !($isunknown(data_wdata_o));
 
    endproperty


// Assertion 11: Byte enable should be correct value when request is high

    property Byte_Enable_Check_A;

        @(posedge clk) disable iff (!rst_n) (data_req_o) |-> !($isunknown(data_be_o));
 
    endproperty

// Assertion 12: Byte enable matches operation type

    property Byte_Enable_Check_B;

        @(posedge clk) disable iff (!rst_n) (data_req_o && data_rvalid_i && !data_we_o) |-> (data_be_o inside {4'b0001, 4'b0010, 4'b0100, 4'b1000, 4'b0011, 4'b1100, 4'b1111, 4'b1110, 4'b0111, 4'b0110});
 
    endproperty


// Assertion 13: Address should be valid when request is high

    property Address_Check_A;

        @(posedge clk) disable iff (!rst_n) (data_req_o) |-> !($isunknown(data_addr_o));
 
    endproperty

// Assertion 14: Address Aligned with byte enables

    property Address_Check_B;

        @(posedge clk) disable iff (!rst_n) $rose(data_req_o && !data_we_o) |->     (data_be_o == 4'b0001) ? (data_addr_o[1:0] == 2'b00) :      // Byte 0
                                                                                    (data_be_o == 4'b0010) ? (data_addr_o[1:0] == 2'b01) :      // Byte 1
                                                                                    (data_be_o == 4'b0100) ? (data_addr_o[1:0] == 2'b10) :      // Byte 2
                                                                                    (data_be_o == 4'b1000) ? (data_addr_o[1:0] == 2'b11) :      // Byte 3
                                                                                    (data_be_o == 4'b0011) ? (data_addr_o[1:0] == 2'b00) :      // Half-word lower
                                                                                    (data_be_o == 4'b1100) ? (data_addr_o[1:0] == 2'b10) :      // Half-word upper
                                                                                    (data_be_o == 4'b0111) ? (data_addr_o[1:0] == 2'b00) :      // Unaligned 3-byte access (0–2)
                                                                                    (data_be_o == 4'b1110) ? (data_addr_o[1:0] == 2'b01) :      // Unaligned 3-byte access (1–3)
                                                                                    (data_be_o == 4'b0110) ? (data_addr_o[1:0] == 2'b01) :      // Unaligned half-word access (1–2)
                                                                                    (data_addr_o[1:0] == 2'b00);                                // Default: word access
 
    endproperty



// Assertion Instantiation of Properties

    Reset_Check_Assert: assert property (Reset_Check);
    No_Spurious_Grant_Assert: assert property (No_Spurious_Grant);

    Grant_Check_A_Assert: assert property (Grant_Check_A);
    Grant_Check_B_Assert: assert property (Grant_Check_B);
    Handshake_Check_Assert: assert property (Handshake_Check);

    R_Valid_Check_A_Assert: assert property (R_Valid_Check_A);
    R_Valid_Check_B_Assert: assert property (R_Valid_Check_B);
    R_Valid_Check_C_Assert: assert property (R_Valid_Check_C);


    Read_Data_Check_Assert: assert property (Read_Data_Check);

    Write_Data_Check_Assert: assert property (Write_Data_Check);

    Byte_Enable_Check_A_Assert: assert property (Byte_Enable_Check_A);
    Byte_Enable_Check_B_Assert: assert property (Byte_Enable_Check_B);

    Address_Check_A_Assert: assert property (Address_Check_A);
    Address_Check_B_Assert: assert property (Address_Check_B);





// Assertion Coverage of Properties 

    Reset_Check_Cover: cover property (Reset_Check);
    No_Spurious_Grant_Cover: cover property (No_Spurious_Grant);

    Grant_Check_A_Cover: cover property (Grant_Check_A);
    Grant_Check_B_Cover: cover property (Grant_Check_B);
    Handshake_Check_Cover: cover property (Handshake_Check);

    R_Valid_Check_A_Cover: cover property (R_Valid_Check_A);
    R_Valid_Check_B_Cover: cover property (R_Valid_Check_B);
    R_Valid_Check_C_Cover: cover property (R_Valid_Check_C);

    Read_Data_Check_Cover: cover property (Read_Data_Check);

    Write_Data_Check_Cover: cover property (Write_Data_Check);

    Byte_Enable_Check_A_Cover: cover property (Byte_Enable_Check_A);
    Byte_Enable_Check_B_Cover: cover property (Byte_Enable_Check_B);

    Address_Check_A_Cover: cover property (Address_Check_A);
    Address_Check_B_Cover: cover property (Address_Check_B);




endmodule
