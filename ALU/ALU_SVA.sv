import mypkg::*;

module ALU_SVA (intf i_intf);

    

    property p_ALU_2;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && !i_intf.b_en) && (i_intf.a_op == ADD_A)) |=> (i_intf.C == ({$past(i_intf.A[4]), $past(i_intf.A)} + {$past(i_intf.B[4]), $past(i_intf.B)}));
        //((i_intf.a_en && !i_intf.b_en) && (i_intf.a_op == ADD_A)) |=> (i_intf.C == ($past(i_intf.A) + $past(i_intf.B)));
	//else $error("ALU_2 failed: A = %0d, B = %0d, C = %0d", $past(i_intf.A), $past(i_intf.B), i_intf.C);
    endproperty

    property p_ALU_3;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && !i_intf.b_en) && (i_intf.a_op == SUB_A)) |=> (i_intf.C == ({$past(i_intf.A[4]), $past(i_intf.A)} - {$past(i_intf.B[4]), $past(i_intf.B)}));
    endproperty

    property p_ALU_4;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && !i_intf.b_en) && (i_intf.a_op == XOR_A)) |=> (i_intf.C == ($past(i_intf.A) ^ $past(i_intf.B)));
    endproperty

    property p_ALU_5;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && !i_intf.b_en) && (i_intf.a_op == AND_A_1)) |=> (i_intf.C == ($past(i_intf.A) & $past(i_intf.B)));
    endproperty

    property p_ALU_6;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && !i_intf.b_en) && (i_intf.a_op == AND_A_2)) |=> (i_intf.C == ($past(i_intf.A) & $past(i_intf.B)));
    endproperty

    property p_ALU_7;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && !i_intf.b_en) && (i_intf.a_op == OR_A)) |=> (i_intf.C == ($past(i_intf.A) | $past(i_intf.B)));
    endproperty

    property p_ALU_8;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && !i_intf.b_en) && (i_intf.a_op == XNOR_A)) |=> (i_intf.C == ~($past(i_intf.A) ^ $past(i_intf.B)));
    endproperty

    // property p_ALU_9;
    //     @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
    //     ((!i_intf.a_en && i_intf.b_en) && (i_intf.b_op == NAND_B_1)) |=> (i_intf.C == ~($past(i_intf.A) & $past(i_intf.B)));
    // endproperty

    property p_ALU_10;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((!i_intf.a_en && i_intf.b_en) && (i_intf.b_op == NAND_B_1)) |=> (i_intf.C == ~($past(i_intf.A) & $past(i_intf.B)));
    endproperty

    property p_ALU_11;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((!i_intf.a_en && i_intf.b_en) && (i_intf.b_op == ADD1_B_1)) |=> (i_intf.C == ({$past(i_intf.A[4]), $past(i_intf.A)} + {$past(i_intf.B[4]), $past(i_intf.B)}));
    endproperty

    property p_ALU_12;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((!i_intf.a_en && i_intf.b_en) && (i_intf.b_op == ADD2_B_1)) |=> (i_intf.C == ({$past(i_intf.A[4]), $past(i_intf.A)} + {$past(i_intf.B[4]), $past(i_intf.B)}));
    endproperty



    property p_ALU_14;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && i_intf.b_en) && (i_intf.b_op == XOR_B_2)) |=> (i_intf.C == $past(i_intf.A) ^ $past(i_intf.B));
    endproperty

    property p_ALU_15;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && i_intf.b_en) && (i_intf.b_op == XNOR_B_2)) |=> (i_intf.C == ~($past(i_intf.A) ^ $past(i_intf.B)));
    endproperty

    property p_ALU_16;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && i_intf.b_en) && (i_intf.b_op == SUBONE_B_2)) |=> (i_intf.C == ({$past(i_intf.A[4]), $past(i_intf.A)} - 6'd1));
    endproperty

    property p_ALU_17;
        @(posedge i_intf.clk) disable iff (!i_intf.rst_n)
        ((i_intf.a_en && i_intf.b_en) && (i_intf.b_op == ADDTWO_B_2)) |=> (i_intf.C == ({$past(i_intf.B[4]), $past(i_intf.B)} + 6'd2));
    endproperty

   

    s_ALU_2  : assert property(p_ALU_2);
    s_ALU_3  : assert property(p_ALU_3);
    s_ALU_4  : assert property(p_ALU_4);
    s_ALU_5  : assert property(p_ALU_5);
    s_ALU_6  : assert property(p_ALU_6);
    s_ALU_7  : assert property(p_ALU_7);
    s_ALU_8  : assert property(p_ALU_8);
    //s_ALU_9  : assert property(p_ALU_9);
    s_ALU_10 : assert property(p_ALU_10);
    s_ALU_11 : assert property(p_ALU_11);
    s_ALU_12 : assert property(p_ALU_12);
    //s_ALU_13 : assert property(p_ALU_13);
    s_ALU_14 : assert property(p_ALU_14);
    s_ALU_15 : assert property(p_ALU_15);
    s_ALU_16 : assert property(p_ALU_16);
    s_ALU_17 : assert property(p_ALU_17);


    c_ALU_2  : cover property(p_ALU_2);
    c_ALU_3  : cover property(p_ALU_3);
    c_ALU_4  : cover property(p_ALU_4);
    c_ALU_5  : cover property(p_ALU_5);
    c_ALU_6  : cover property(p_ALU_6);
    c_ALU_7  : cover property(p_ALU_7);
    c_ALU_8  : cover property(p_ALU_8);
    //c_ALU_9  : cover property(p_ALU_9);
    c_ALU_10 : cover property(p_ALU_10);
    c_ALU_11 : cover property(p_ALU_11);
    c_ALU_12 : cover property(p_ALU_12);
    //c_ALU_13 : cover property(p_ALU_13);
    c_ALU_14 : cover property(p_ALU_14);
    c_ALU_15 : cover property(p_ALU_15);
    c_ALU_16 : cover property(p_ALU_16);
    c_ALU_17 : cover property(p_ALU_17);


endmodule : ALU_SVA

