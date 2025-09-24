//-----------------------------------------------------------------------------
// Class: Configuration_Coverage
// Engineer: Nourhan
// Description: Coverage collector for Configuration interface
//-----------------------------------------------------------------------------
class Configuration_Coverage extends uvm_subscriber #(Configuration_Seq_Item);
    `uvm_component_utils(Configuration_Coverage)
    Configuration_Seq_Item item;
    uvm_analysis_imp#(Configuration_Seq_Item,Configuration_Coverage) cov;
       
    // Covergroups
    covergroup address_cg;
        boot_addr: coverpoint item.boot_addr_i {
            bins boot_addr_rang = {[32'h0000_0000:32'h0000_0FFF]};

        }
    endgroup
    
    covergroup control_cg;
        reset: coverpoint item.rst_n {
            bins active   = {0};
            bins inactive = {1};
        }
        

        
        fetch: coverpoint item.fetch_enable_i {
            bins disabled = {0};
            bins enabled = {1};
        }
    endgroup
    
    //-----------------------------------------------------------------------------
    // Function: new
    // Description: Constructor
    //-----------------------------------------------------------------------------
    function new(string name = "Configuration_Coverage", uvm_component parent = null);
        super.new(name, parent);
        address_cg = new();
        control_cg = new();
    endfunction
    
    //-----------------------------------------------------------------------------
    // Function: write
    // Parameters:
    //  t - Transaction item to sample coverage from
    // Description: Main coverage sampling method
    //-----------------------------------------------------------------------------
    function void write(Configuration_Seq_Item t);
            item = t;  // Store transaction for coverage sampling
            address_cg.sample();
            control_cg.sample();
            `uvm_info("COV", $sformatf("Sampled coverage for:\n%s", 
                      t.convert2string()), UVM_FULL)
       
    endfunction
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cov=new("cov",this);
    endfunction
    //-----------------------------------------------------------------------------
    // Function: report_phase
    // Description: Reports final coverage statistics
    //-----------------------------------------------------------------------------
    function void report_phase(uvm_phase phase);
            `uvm_info("Configuration_Coverage", $sformatf("Address Coverage: =%0d%%", address_cg.get_coverage()), UVM_NONE);
             `uvm_info("Configuration_Coverage", $sformatf("Control Coverage:%0d%%", control_cg.get_coverage()), UVM_NONE);
        
    endfunction
endclass