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

## 🔹 Log Files Path
   - RISCV/simulation/log_files
   - RISCV_RAL/simulation/log_files
