////////////////////////////////////////////////////////////////////////////////
// Author: Kareem Waseem
// Course: Digital Verification using SV & UVM
//
// Description: Shift register Design 
// 
////////////////////////////////////////////////////////////////////////////////
module shift_reg (shift_reg_if shift_regif);

always @(posedge shift_regif.clk or posedge shift_regif.reset) begin
   if (shift_regif.reset)
      shift_regif.dataout <= 0;
   else
      if (shift_regif.mode) // rotate
         if (shift_regif.direction) // left
            shift_regif.dataout <= {shift_regif.datain[4:0], shift_regif.datain[5]};
         else
            shift_regif.dataout <= {shift_regif.datain[0], shift_regif.datain[5:1]};
      else // shift
         if (shift_regif.direction) // left
            shift_regif.dataout <= {shift_regif.datain[4:0], shift_regif.serial_in};
         else
            shift_regif.dataout <= {shift_regif.serial_in, shift_regif.datain[5:1]};
end
endmodule
