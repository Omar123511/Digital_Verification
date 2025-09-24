/*######################################################################
## Class Name: Register_File_Coverage  
## Engineer : Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .The coverage collector class monitors the functional coverage from the actual sequence item coming from the DUT.
######################################################################*/
class Register_File_Coverage extends uvm_subscriber #(Register_File_Sequence_Item);

  `uvm_component_utils(Register_File_Coverage)

  Register_File_Sequence_Item seq_item;

  covergroup Register_File_cg;

    cp_we_a_i: coverpoint seq_item.we_a_i;
    cp_we_b_i: coverpoint seq_item.we_b_i;

    cp_raddr_a_i: coverpoint seq_item.raddr_a_i {
      bins zero = {0};
      bins rest[] = {[1:31]};
    }

    cp_rdata_a_o: coverpoint seq_item.rdata_a_o {
      bins zero = {32'h0};
      bins max = {32'hFFFF_FFFF};
      bins random_data = default;
    }


    cp_raddr_b_i: coverpoint seq_item.raddr_b_i {
      bins zero = {0};
      bins rest[] = {[1:31]};
    }

    cp_rdata_b_o: coverpoint seq_item.rdata_b_o {
      bins zero = {32'h0};
      bins max = {32'hFFFF_FFFF};
      bins random_data = default;
    }


    cp_raddr_c_i: coverpoint seq_item.raddr_c_i {
      bins zero = {0};
      ignore_bins rest[] = {[1:31]};
    }

    cp_rdata_c_o: coverpoint seq_item.rdata_c_o {
      bins zero = {32'h0};
      ignore_bins max = {32'hFFFF_FFFF};
      bins random_data = default;
    }
    
    cp_waddr_a_i: coverpoint seq_item.waddr_a_i {
      ignore_bins zero = {0};
      bins rest[] = {[1:31]};
    }

    cp_wdata_a_i: coverpoint seq_item.wdata_a_i {
      bins zero = {32'h0};
      bins max = {32'hFFFF_FFFF};
      bins random_data = default;
    }


    cp_waddr_b_i: coverpoint seq_item.waddr_b_i {
      ignore_bins zero = {0};
      bins rest[] = {[1:31]};
    }

    cp_wdata_b_i: coverpoint seq_item.wdata_b_i {
      bins zero = {32'h0};
      bins max = {32'hFFFF_FFFF};
      bins random_data = default;
    }

    cross_we_a_i_waddr_a_i :  cross cp_we_a_i, cp_waddr_a_i;
    cross_we_b_i_waddr_b_i :  cross cp_we_b_i, cp_waddr_b_i;



  endgroup


  function new(string name = "Register_File_Coverage", uvm_component parent = null);
    super.new(name, parent);
    Register_File_cg = new();
  endfunction
  function void build_phase (uvm_phase phase);
		super.build_phase(phase);
		//cov  		= new("cov", this);
	endfunction : build_phase

  function void write(Register_File_Sequence_Item t);
    seq_item = t;
    Register_File_cg.sample();
  endfunction

  virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      `uvm_info("Register_File_Coverage", $sformatf("Register_File_Coverage_Report: %0d%%", Register_File_cg.get_coverage()), UVM_NONE)
  endfunction

endclass
