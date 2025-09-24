/*######################################################################
## Class Name: Instruction_Monitor  
## Engineer : Omnia Mohamed
## Date: April 2025
## Description: 
    This class is responsible for transforming the pin level to transaction level and 
	monitoring the address phase and the response phase based on obi interface.
	It broadcasts the collected transaction to the subscriber and scoreboard.
######################################################################*/
class Instruction_Monitor extends uvm_monitor;
	`uvm_component_utils(Instruction_Monitor)

    Instruction_Seq_Item item_mon;
    virtual Instruction_Interface vif;
	uvm_analysis_port#(Instruction_Seq_Item) mon_ap;
	int addresses[$];

    function new(string name="Instruction_Monitor",uvm_component parent=null);
        super.new(name,parent);
    endfunction
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		item_mon=Instruction_Seq_Item::type_id::create("item_mon");
		mon_ap=new("mon_ap",this);
	endfunction
	task main_phase(uvm_phase phase);
        forever begin
			`uvm_info("Instruction_Monitor","main phase is started",UVM_MEDIUM)
			fork 
        		begin
					monitor_response();
				end
				begin
					monitor_address();
				end
			join
			`uvm_info("Instruction_Monitor","main phase is finished",UVM_MEDIUM)
        end
    endtask
//The following task is used to monitor the response phase.
//It monitors the response phase when instr_rvalid_i is high.
//And It extracts the fields of instruction based on the opcode value. 
	task monitor_response();
		@(posedge vif.clk iff vif.instr_rvalid_i);
        if(vif.instr_rvalid_i == 1'b1) begin
            item_mon.instruction= vif.instr_rdata_i ;
			if(item_mon.instruction[6:0]== 7'b0110011)begin //r-type format
				item_mon.opcode=item_mon.instruction[6:0];
				item_mon.rd=item_mon.instruction[11:7];
				item_mon.funct3=item_mon.instruction[14:12];
				item_mon.rs1=item_mon.instruction[19:15];
				item_mon.rs2=item_mon.instruction[24:20];
				item_mon.funct7=item_mon.instruction[31:25];
				if(item_mon.funct7==7'b0000001)begin
					item_mon.instruction_type=m_extension;
					case (item_mon.funct3)
						3'b000: item_mon.m_instr= mul;
						3'b001: item_mon.m_instr= mulh;
						3'b010: item_mon.m_instr= mulsu;
						3'b011: item_mon.m_instr= mulu;
						3'b100: item_mon.m_instr= div;
						3'b101: item_mon.m_instr= divu;
						3'b110: item_mon.m_instr= rem;
						3'b111: item_mon.m_instr= remu;
					endcase
				end
				else begin
					item_mon.instruction_type=r_type;
					case (item_mon.funct3)
						3'b000: begin 
							if(item_mon.funct7==7'b0100000) 
								item_mon.rtype= sub;
							else 
								item_mon.rtype= add;
						end
						3'b001: item_mon.rtype= sll;
						3'b010: item_mon.rtype= slt;
						3'b011: item_mon.rtype= sltu;
						3'b100: item_mon.rtype= xor_op;
						3'b101: begin 
							if(item_mon.funct7==7'b0100000) 
								item_mon.rtype= sra;
						 	else 
								item_mon.rtype= srl;
						end
						3'b110: item_mon.rtype= or_op;
						3'b111: item_mon.rtype= and_op;
					endcase
				end
			end
			else if(item_mon.instruction[6:0]== 7'b0010011 || item_mon.instruction[6:0]== 7'b0000011 || item_mon.instruction[6:0]==7'b1100111)begin //i-type immediate register, load and jump format
				item_mon.opcode=item_mon.instruction[6:0];
				item_mon.rd=item_mon.instruction[11:7];
				item_mon.funct3=item_mon.instruction[14:12];
				item_mon.rs1=item_mon.instruction[19:15];
				item_mon.imm={{20{item_mon.instruction[31]}},item_mon.instruction[31:20]};
				if(item_mon.opcode == 7'b0010011)begin
					item_mon.instruction_type=i_type_reg;
					case (item_mon.funct3)
						3'b000: item_mon.itype_reg= addi;
						3'b010: item_mon.itype_reg= slti;
						3'b011: item_mon.itype_reg= sltiu;
						3'b100: item_mon.itype_reg= xori;
						3'b110: item_mon.itype_reg= ori;
						3'b111: item_mon.itype_reg= andi;
						3'b001: item_mon.itype_reg= slli;
						3'b101: begin
							if(item_mon.imm[11:5]==7'b0100000)
								item_mon.itype_reg= srai;
							else item_mon.itype_reg= srli;
						end
					endcase
				end
				else if(item_mon.opcode == 7'b0000011)begin
					item_mon.instruction_type=i_type_load;
					case (item_mon.funct3)
						3'b000: item_mon.itype_load= lb;
						3'b001: item_mon.itype_load= lh;
						3'b010: item_mon.itype_load= lw;
						3'b100: item_mon.itype_load= lbu;
						3'b101: item_mon.itype_load= lhu;
					endcase
				end
				else if(item_mon.opcode == 7'b1100111) begin
					item_mon.instruction_type=i_type_jump;
					item_mon.j_instr= jalr;
				end
			end
			else if(item_mon.instruction[6:0]== 7'b0100011 )begin //s-type format
				item_mon.instruction_type=s_type;
				item_mon.opcode=item_mon.instruction[6:0];
				item_mon.funct3=item_mon.instruction[14:12];
				item_mon.rs1=item_mon.instruction[19:15];
				item_mon.rs2=item_mon.instruction[24:20];
				item_mon.imm={{20{item_mon.instruction[31]}},item_mon.instruction[31:25],item_mon.instruction[11:7]};
				case (item_mon.funct3)
					3'b000: item_mon.stype= sb;
					3'b001: item_mon.stype= sh;
					3'b010: item_mon.stype= sw;
				endcase
			end
			else if(item_mon.instruction[6:0]== 7'b1101111 )begin //j-type format jal
				item_mon.instruction_type=j_type;
				item_mon.opcode=item_mon.instruction[6:0];
				item_mon.rd=item_mon.instruction[11:7];
				item_mon.imm={{12{item_mon.instruction[31]}},item_mon.instruction[19:12],item_mon.instruction[20],item_mon.instruction[30:21]};
				item_mon.j_instr= jal;
			end
			else if(item_mon.instruction[6:0]== 7'b1100011 )begin //b-type format
				item_mon.instruction_type=b_type;
				item_mon.opcode=item_mon.instruction[6:0];
				item_mon.funct3=item_mon.instruction[14:12];
				item_mon.rs1=item_mon.instruction[19:15];
				item_mon.rs2=item_mon.instruction[24:20];
				item_mon.imm={{20{item_mon.instruction[31]}},item_mon.instruction[7],item_mon.instruction[30:25],item_mon.instruction[11:8],1'b0};
				case (item_mon.funct3)
					3'b000: item_mon.btype= beq;
					3'b001: item_mon.btype= bne;
					3'b100: item_mon.btype= blt;
					3'b101: item_mon.btype= bge;
					3'b110: item_mon.btype= bltu;
					3'b111: item_mon.btype= bgeu;
				endcase
			end
			else if(item_mon.instruction[6:0]== 7'b0110111 || item_mon.instruction[6:0]== 7'b0010111)begin //u-type format
				item_mon.instruction_type=u_type;
				item_mon.opcode=item_mon.instruction[6:0];
				item_mon.rd=item_mon.instruction[11:7];
				item_mon.imm={item_mon.instruction[31:12],12'b0};
				if (item_mon.instruction[6:0]== 7'b0110111)
					item_mon.utype =lui;
				else item_mon.utype =auipc;
			end
			item_mon.address=addresses.pop_front();
			item_mon.instruction_mem[item_mon.address]=item_mon.instruction ;
			`uvm_info("Instruction_Monitor", item_mon.sprint(),UVM_MEDIUM)
			`uvm_info("Instruction_Monitor",$sformatf("monitor: time=%0t rst_n=%0d instr_req_o=%0d  addr_o=%0h gnt_i=%0d valid=%0d instr=%0h ",$time,vif.rst_n,vif.instr_req_o,vif.instr_addr_o,vif.instr_gnt_i,vif.instr_rvalid_i,vif.instr_rdata_i),UVM_MEDIUM)
			mon_ap.write(item_mon);
		end
	endtask
//The following task is used to monitor the address phase.
	task monitor_address(); 
			@(posedge vif.clk  iff (vif.instr_req_o && vif.instr_gnt_i));
            if(vif.instr_req_o && vif.instr_gnt_i) begin
				addresses.push_back(vif.instr_addr_o);
			end
	endtask
endclass