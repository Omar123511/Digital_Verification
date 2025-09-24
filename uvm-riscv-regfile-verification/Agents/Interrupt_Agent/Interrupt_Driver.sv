/*###################################################################### 
## Class Name: Interrupt_Driver   
## Engineer : Abdelrhman Tamer 
## Date: May 2025 
## Description:  
    This class is responsible for driving the interrupt vector to the DUT 
    through the interrupt interface based on transactions received from the sequencer.
######################################################################*/
class Interrupt_Driver extends uvm_driver #(Interrupt_Seq_Item); 
    `uvm_component_utils(Interrupt_Driver) 
     
    virtual Interrupt_IF d_if; 
    Interrupt_Seq_Item req; 
    Interrupt_Sequencer sqr;
 
    function new (string name = "Interrupt_Driver", uvm_component parent = null); 
        super.new(name, parent); 
    endfunction : new 
    
    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
    endfunction : build_phase

    task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req); // Get next sequence item
      `uvm_info("Interrupt_Driver", req.convert2string, UVM_LOW);
      drive_interrupt(req); // Drive the interrupt
      seq_item_port.item_done();
    end
    endtask

    task drive_interrupt(Interrupt_Seq_Item item);
        if(item.interrupt_id!= 0)begin// in case of interrupt mode is activated
            // Wait until ack
            d_if.irq_i[item.interrupt_id] = 1;
            `uvm_info("Interrupt_Driver", item.convert2string, UVM_LOW);
            @(posedge d_if.clk);
            if (d_if.irq_ack_o && (d_if.irq_id_o == item.interrupt_id))
                `uvm_info("Interrupt_Driver", item.convert2string, UVM_LOW);
            d_if.irq_i[item.interrupt_id] = 0;
        end
        else begin// no interrupt mode
            d_if.irq_i =0 ;
        end

    endtask 
endclass