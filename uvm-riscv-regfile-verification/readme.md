# UVM RISC-V Register File Verification

This project demonstrates two verification approaches for a **RISC-V register file** using the **UVM (Universal Verification Methodology)** framework.  
The register file has **two write ports** and **three read ports**, and the verification focuses on validating its functionality.

---

## 🔹 Project Versions
The project contains two separate versions of the same testbench:

1. **RAL (Register Abstraction Layer) Based Verification**  
   - Uses UVM RAL model for register access and checking.  
   - Provides abstraction for register operations.  

2. **Reference Model Based Verification**  
   - Uses a custom reference model of the register file for result checking.  
   - Allows direct comparison of DUT outputs against the expected model behavior.  

---

## 🔹 Contributions
- **My Work**  
  - Implemented **UVM RAL model** for the register file.  
  - Developed **Reference Model** for functional checking.  

- **Other Components** (developed by teammates)  
  - UVM environment (agents, drivers, monitors, scoreboard, etc.)  
  - Test scenarios and sequences.  

---

## 🔹 Repository Structure
```
uvm-riscv-regfile-verification/
├── RISCV/
│ ├── Agents/
│ │ ├── Configuration_Agent/
│ │ ├── Data_Memory_Agent/
│ │ ├── Debug_Agent/
│ │ ├── EX_Agent/
│ │ ├── Instruction_Agent/
│ │ ├── Interrupt_Agent/
│ │ └── RF_Agent/
│ │
│ ├── Assertions/
│ ├── Coverage_Collectors/
│ ├── Env/
│ ├── Interfaces/
│ ├── Sequences/
│ │ └── Instruction_Sequences/
│ │
│ ├── Seq_Items/
│ ├── Tests/
│ └── Virtual_Seq/
|
├── RISCV_RAL
│ ├── Agents/
│ │ ├── Configuration_Agent/
│ │ ├── Data_Memory_Agent/
│ │ ├── Debug_Agent/
│ │ ├── EX_Agent/
│ │ ├── Instruction_Agent/
│ │ ├── Interrupt_Agent/
│ │ └── RF_Agent/
│ │
│ ├── Assertions/
│ ├── Coverage_Collectors/
│ ├── Env/
│ ├── Interfaces/
│ ├── RAL_Classes/
│ │ └── RAL/
│ │
│ ├── Sequences/
│ │ └── Instruction_Sequences/
│ │
│ ├── Seq_Items/
│ ├── Tests/
│ └── Virtual_Seq/
```

## 🔹 How to Run
1. Clone the repository:
   ```bash
   git clone https://github.com/Omar123511/uvm-riscv-regfile-verification.git
   cd uvm-riscv-regfile-verification
2. For each environment:
   - For the reference model version:
     ```bash
     cd RISCV
   - For the reference model version:
     ```bash
     cd RISCV_RAL
2. Compile and run simulations using VCS:
   ```bash
   make

Example (Questa):
vlog -f filelist.f
vsim -c top_tb -do run.do


Example Output
```
Sample simulation log (truncated for clarity):
UVM_INFO @ 0: reporter [RNTST] Running test test_regfile_basic...
UVM_INFO @ 20: uvm_test_top.env.agent.monitor [MON] Read reg[5] = 0x000000AA
UVM_INFO @ 30: uvm_test_top.env.agent.monitor [MON] Write reg[5] = 0x00000055
UVM_INFO @ 40: uvm_test_top.scoreboard [SCBD] Match: reg[5] expected=0x55, actual=0x55
UVM_INFO @ 100: reporter [UVM/REPORT/SUMMARY]
---------------------------------------------------
UVM Report Summary
  ** Report counts by severity
  UVM_INFO    :   10
  UVM_WARNING :    0
  UVM_ERROR   :    0
  UVM_FATAL   :    0
  ** 0 errors, 0 fatals
  ** Simulation PASSED
---------------------------------------------------
```

Simulator: VCS
