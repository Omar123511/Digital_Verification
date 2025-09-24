/*######################################################################
## Interface Name: Debug_Interface  
## Engineer : Ahmed Awwad
## Date: MAY 2025
## Description: EX stage inputs and outputs interface
######################################################################*/

interface Debug_Interface;

	//Debug Interface inputs and outputs
	bit clk;
	logic debug_req_i;
	logic debug_havereset_o;
	logic debug_running_o;
	logic debug_halted_o;

	// Modport for DUT connections
	modport dut(output debug_havereset_o, debug_running_o, debug_halted_o, input debug_req_i);

endinterface