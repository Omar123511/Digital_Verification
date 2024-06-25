////////////////////////////////////////////////////////////////////////////////
// Author: Kareem Waseem
// Course: Digital Verification using SV & UVM
//
// Description: Counter Design 
// 
////////////////////////////////////////////////////////////////////////////////
module counter (counter_if.DUT counterif);

always @(posedge counterif.clk) begin
    if (!counterif.rst_n)
        counterif.count_out <= 0;
    else if (!counterif.load_n)
        counterif.count_out <= counterif.data_load;
    else if (counterif.ce)
        if (counterif.up_down)
            counterif.count_out <= counterif.count_out + 1;
        else 
            counterif.count_out <= counterif.count_out - 1;
end

assign counterif.max_count = (counterif.count_out == {counterif.WIDTH{1'b1}})? 1:0;
assign counterif.zero = (counterif.count_out == 0)? 1:0;

endmodule