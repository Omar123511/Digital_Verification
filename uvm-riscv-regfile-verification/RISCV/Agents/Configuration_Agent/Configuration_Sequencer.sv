class Configuration_Sequencer extends uvm_sequencer#(Configuration_Seq_Item);
    `uvm_component_utils(Configuration_Sequencer)
    
    function new(string name="Configuration_Sequencer",uvm_component parent=null);
        super.new(name,parent);

    endfunction
endclass