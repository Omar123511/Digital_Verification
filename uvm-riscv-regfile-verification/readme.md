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
├── ral_version/ # UVM RAL-based verification
│ ├── ral_model.sv
│ ├── ...
│
├── refmodel_version/ # Reference model-based verification
│ ├── regfile_refmodel.sv
│ ├── ...
│
├── docs/ # Documentation (if any)
├── tests/ # Test scenarios
└── README.md
```

---

## 🔹 How to Run
1. Clone the repository:
   ```bash
   git clone https://github.com/<your-username>/uvm-riscv-regfile-verification.git
   cd uvm-riscv-regfile-verification
2. Compile and run simulations with your preferred simulator (Questa, VCS, Xcelium, etc.).

Example (Questa):
vlog -f filelist.f
vsim -c top_tb -do run.do


Example Output

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

Requirements

SystemVerilog with UVM 1.2 or later

Simulator: Questa / VCS / Xcelium
