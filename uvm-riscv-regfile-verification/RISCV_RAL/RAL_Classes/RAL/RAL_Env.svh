/*######################################################################
## Class Name: RAL_Env
## Engineers : Abdelrahman Tamer - Omar Magdy Elsayed
## Date: MAY 2025
## Description:
    .It encapsulates RAL components and connect the predictors to the model's map.
######################################################################*/
class RAL_Env extends uvm_env;
    `uvm_component_utils (RAL_Env)

    function new (string name = "RAL_Env", uvm_component parent);
        super.new (name, parent);
    endfunction

    Reg_Block           Reg_Block_inst;  // Register Model
    DM_Adapter          DM_Adapter_inst; // Convert Reg Tx <-> Bus-type packets
    RF_Adapter          RF_Adapter_inst; // Convert Reg Tx <-> Bus-type packets
    
    RF_Read_a_Adapter          RF_Read_a_Adapter_inst; // Convert Reg Tx <-> Bus-type packets
    RF_Read_b_Adapter          RF_Read_b_Adapter_inst; // Convert Reg Tx <-> Bus-type packets
    RF_Read_c_Adapter          RF_Read_c_Adapter_inst; // Convert Reg Tx <-> Bus-type packets    

    Data_Memory_Agent   DM_agent;        // Agent to drive/monitor transactions
    Register_File_Agent RF_agent;        // Agent to drive/monitor transactions

    uvm_reg_predictor #(Data_Memory_Seq_Item)           DM_Predictor; // Map APB tx to register in model
    uvm_reg_predictor #(Register_File_Sequence_Item)    RF_Predictor; // Map APB tx to register in model

    uvm_reg_predictor #(Register_File_Sequence_Item)    RF_Read_a_Predictor; // Map APB tx to register in model
    uvm_reg_predictor #(Register_File_Sequence_Item)    RF_Read_b_Predictor; // Map APB tx to register in model
    uvm_reg_predictor #(Register_File_Sequence_Item)    RF_Read_c_Predictor; // Map APB tx to register in model

    virtual function void build_phase (uvm_phase phase);
        super.build_phase (phase);
        Reg_Block_inst      = Reg_Block  :: type_id :: create ("Reg_Block_inst", this);
        DM_Adapter_inst     = DM_Adapter :: type_id :: create ("DM_Adapter_inst");
        RF_Adapter_inst     = RF_Adapter :: type_id :: create ("RF_Adapter_inst");
        
        RF_Read_a_Adapter_inst     = RF_Read_a_Adapter :: type_id :: create ("RF_Read_a_Adapter_inst");
        RF_Read_b_Adapter_inst     = RF_Read_b_Adapter :: type_id :: create ("RF_Read_b_Adapter_inst");
        RF_Read_c_Adapter_inst     = RF_Read_c_Adapter :: type_id :: create ("RF_Read_c_Adapter_inst"); 

        DM_Predictor = uvm_reg_predictor #(Data_Memory_Seq_Item)        :: type_id :: create ("DM_Predictor", this);
        RF_Predictor = uvm_reg_predictor #(Register_File_Sequence_Item) :: type_id :: create ("RF_Predictor", this);

        RF_Read_a_Predictor = uvm_reg_predictor #(Register_File_Sequence_Item) :: type_id :: create ("RF_Read_a_Predictor", this);
        RF_Read_b_Predictor = uvm_reg_predictor #(Register_File_Sequence_Item) :: type_id :: create ("RF_Read_b_Predictor", this);
        RF_Read_c_Predictor = uvm_reg_predictor #(Register_File_Sequence_Item) :: type_id :: create ("RF_Read_c_Predictor", this);

        Reg_Block_inst.build ();
        Reg_Block_inst.lock_model();

        uvm_config_db #(Reg_Block)::set(uvm_root::get(), "*", "Reg_Block_inst", Reg_Block_inst);
    endfunction

    virtual function void connect_phase (uvm_phase phase);
        super.connect_phase (phase);
        //Connect Data Memory Predictior
        DM_Predictor.map        = Reg_Block_inst.default_map;
        DM_Predictor.adapter    = DM_Adapter_inst;

        DM_Adapter_inst.adapter_Reg_Block_inst = Reg_Block_inst;
        RF_Adapter_inst.adapter_Reg_Block_inst = Reg_Block_inst;

        //Connect Register File Predictior
        RF_Predictor.map        = Reg_Block_inst.default_map;
        RF_Predictor.adapter    = RF_Adapter_inst;

        RF_Read_a_Predictor.map        = Reg_Block_inst.default_map;
        RF_Read_a_Predictor.adapter    = RF_Read_a_Adapter_inst;

        RF_Read_b_Predictor.map        = Reg_Block_inst.default_map;
        RF_Read_b_Predictor.adapter    = RF_Read_b_Adapter_inst;

        RF_Read_c_Predictor.map        = Reg_Block_inst.default_map;
        RF_Read_c_Predictor.adapter    = RF_Read_c_Adapter_inst;
        
   endfunction
endclass