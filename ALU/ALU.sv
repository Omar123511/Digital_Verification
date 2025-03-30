//`timescale 1ns / 1ps

module ALU #(parameter DATA_WIDTH = 5, OUTPUT_WIDTH = 6, A_OP_WIDTH = 3, B_OP_WIDTH = 2)(
    input clk,    // Clock
    input rst_n,  // Asynchronous reset active low
    
    input ALU_en,   //System enable
    
    input a_en, b_en, //operations enable
    
    input [A_OP_WIDTH-1:0] a_op,
    input [B_OP_WIDTH-1:0] b_op,

    input signed [DATA_WIDTH-1:0] A, B,

    output logic [OUTPUT_WIDTH-1:0] C
    
);
    
    
    always_ff @(posedge clk or negedge rst_n) begin
        
        if (~rst_n) begin                                   
            C <= 'd0;
        end
        else if (ALU_en) begin                              //ALU_1
            if (a_en && !b_en) begin
                case (a_op)
                    3'd0 : C <= {A[4], A} + {B[4], B};                    //ALU_2
                    3'd1 : C <= {A[4], A} - {B[4], B};                    //ALU_3
                    3'd2 : C <= A ^ B;                  //ALU_4
                    3'd3 : C <= A & B;                  //ALU_5
                    3'd4 : C <= A & B;                  //ALU_6
                    3'd5 : C <= A | B;                  //ALU_7
                    3'd6 : C <= ~(A ^ B);                   //ALU_8
                    default : C <= 'd0;                     //ALU_9
                endcase
            end

            else if (!a_en && b_en) begin
                case (b_op)
                    2'd0 : C <= ~(A & B);               //ALU_10
                    2'd1 : C <= {A[4], A} + {B[4], B};                    //ALU_11
                    2'd2 : C <= {A[4], A} + {B[4], B};                    //ALU_12
                    default : C <= 'd0;                     //ALU_13
                endcase
            end

            else if (a_en && b_en) begin
                case (b_op)
                    2'd0 : C <= A ^ B;                  //ALU_14
                    2'd1 : C <= ~(A ^ B);               //ALU_15
                    2'd2 : C <= {A[4], A} - 6'd1;              //ALU_16
                    2'd3 : C <= {B[4], B} + 6'd2;              //ALU_17
                endcase
            end
        end

    end
        
    

endmodule : ALU
