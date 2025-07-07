# Getting Started with RISC-V Core

## Quick Start Guide

This guide will help you get up and running with the RISC-V core implementation quickly. Whether you're a student learning computer architecture, a researcher exploring RISC-V, or a developer integrating the core into your project, this guide covers everything you need to know.

## Prerequisites

### Required Tools
- **SystemVerilog Simulator:** ModelSim, VCS, Xcelium, or similar
- **Synthesis Tool:** Xilinx Vivado, Intel Quartus, or Synopsys Design Compiler
- **RISC-V Toolchain:** For compiling test programs (optional but recommended)

### Recommended Tools
- **Verilator:** Open-source SystemVerilog simulator
- **GTKWave:** Waveform viewer
- **RISC-V Compliance Tests:** For verification

## Installation and Setup

### 1. Clone the Repository
```bash
git clone https://github.com/JuanSync7/RISC-V.git
cd RISC-V
```

### 2. Verify Directory Structure
```bash
ls -la
# You should see:
# rtl/          - RTL design files
# docs/         - Documentation
# tb/           - Testbench files
# sim/          - Simulation files
# fpga/         - FPGA implementation
# asic/         - ASIC implementation
```

### 3. Check RTL Files
```bash
ls rtl/pkg/     # Core pipeline stages
ls rtl/units/    # Functional units
ls rtl/control/  # Control logic
ls rtl/prediction/ # Branch prediction
```

## Simulation Setup

### Using ModelSim/QuestaSim

#### 1. Create a Simulation Script
Create `sim/scripts/compile.tcl`:
```tcl
# Create work library
vlib work

# Compile files in dependency order
vlog rtl/pkg/riscv_core_pkg.sv
vlog rtl/units/*.sv
vlog rtl/control/*.sv
vlog rtl/prediction/*.sv
vlog rtl/core/*.sv

# Load the top-level module
vsim -c riscv_core

# Run simulation
run -all
quit
```

#### 2. Run Simulation
```bash
cd sim
vsim -do scripts/compile.tcl
```

### Using Verilator (Open Source)

#### 1. Install Verilator
```bash
# Ubuntu/Debian
sudo apt-get install verilator

# macOS
brew install verilator

# Windows (WSL or Cygwin)
# Follow instructions at https://verilator.org/guide/latest/install.html
```

#### 2. Create Verilator Wrapper
Create `tb/testbench/riscv_core_tb.cpp`:
```cpp
#include "Vriscv_core.h"
#include "verilated.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    
    Vriscv_core* top = new Vriscv_core;
    
    // Initialize
    top->clk_i = 0;
    top->rst_ni = 0;
    
    // Reset
    for (int i = 0; i < 10; i++) {
        top->clk_i = !top->clk_i;
        top->eval();
    }
    
    top->rst_ni = 1;
    
    // Run simulation
    for (int i = 0; i < 1000; i++) {
        top->clk_i = !top->clk_i;
        top->eval();
    }
    
    delete top;
    return 0;
}
```

#### 3. Compile and Run
```bash
verilator --cc rtl/core/riscv_core.sv --exe tb/testbench/riscv_core_tb.cpp
make -C obj_dir -f Vriscv_core.mk
./obj_dir/Vriscv_core
```

## Understanding the Core

### Architecture Overview
The RISC-V core implements a 5-stage pipeline:
1. **Fetch:** Instruction fetching with branch prediction
2. **Decode:** Instruction decoding and register read
3. **Execute:** ALU operations, multiplication, division
4. **Memory:** Load/store operations
5. **Writeback:** Register file write

### Key Features
- **RV32IM Support:** Complete integer and multiply/divide instructions
- **Branch Prediction:** 2-bit saturating counter with BTB/BHT
- **Hazard Handling:** Full data and control hazard management
- **AXI4-Lite Interface:** Industry-standard memory interface
- **Multi-cycle Operations:** Multiplication and division support

### Performance Characteristics
- **Target Frequency:** 100+ MHz (FPGA), 500+ MHz (ASIC)
- **IPC:** ~0.8 (typical for 5-stage pipeline)
- **Branch Prediction Accuracy:** >85%
- **Pipeline Efficiency:** ~70-80%

## Running Tests

### 1. Basic Functionality Test
```bash
# Create a simple test program
cat > test_program.s << EOF
.text
.global _start
_start:
    li x1, 10
    li x2, 20
    add x3, x1, x2
    sw x3, 0(x0)
    j _start
EOF

# Compile with RISC-V toolchain
riscv64-unknown-elf-gcc -march=rv32im -mabi=ilp32 -nostdlib -o test_program test_program.s
```

### 2. RISC-V Compliance Tests
```bash
# Clone compliance tests
git clone https://github.com/riscv/riscv-compliance.git
cd riscv-compliance

# Run specific tests
make TARGETDIR=../RISC-V/tb/tests/compliance_tests
```

### 3. Performance Benchmarks
```bash
# Dhrystone benchmark
cd software/benchmarks/dhrystone
make
# Run with your simulator
```

## FPGA Implementation

### Xilinx Vivado Setup

#### 1. Create Vivado Project
```tcl
# Create project
create_project riscv_core vivado_project -part xc7a35tcpg236-1

# Add RTL files
add_files rtl/core/
add_files rtl/units/
add_files rtl/control/
add_files rtl/prediction/

# Set top module
set_property top riscv_core [current_fileset]
```

#### 2. Add Constraints
Create `fpga/constraints/pins.xdc`:
```tcl
# Clock
set_property PACKAGE_PIN W5 [get_ports clk_i]
set_property IOSTANDARD LVCMOS33 [get_ports clk_i]

# Reset
set_property PACKAGE_PIN U18 [get_ports rst_ni]
set_property IOSTANDARD LVCMOS33 [get_ports rst_ni]

# Add more pin constraints as needed
```

#### 3. Run Synthesis and Implementation
```tcl
# Synthesize
launch_runs synth_1
wait_on_run synth_1

# Implement
launch_runs impl_1 -to_step write_bitstream
wait_on_run impl_1
```

### Intel Quartus Setup

#### 1. Create Quartus Project
```bash
# Create project
quartus_sh --flow compile riscv_core
```

#### 2. Add RTL Files
- Add all SystemVerilog files from `rtl/` directory
- Set `riscv_core` as top-level entity

#### 3. Add Constraints
Create `fpga/constraints/pins.qsf`:
```
set_location_assignment PIN_P11 -to clk_i
set_location_assignment PIN_R9 -to rst_ni
# Add more pin assignments
```

## Configuration Options

### Core Parameters
```systemverilog
// In riscv_core.sv
module riscv_core #(
    parameter addr_t RESET_VECTOR = 32'h0000_0000,  // Reset address
    parameter integer BTB_ENTRIES = 64,             // BTB size
    parameter integer BHT_ENTRIES = 256             // BHT size
) (
    // ... ports
);
```

### Memory Interface Configuration
```systemverilog
// AXI4-Lite interface parameters
parameter integer AXI_DATA_WIDTH = 32;
parameter integer AXI_ADDR_WIDTH = 32;
parameter integer AXI_ID_WIDTH = 0;  // Lite specification
```

### Performance Tuning
- **BTB Size:** Increase for better branch prediction
- **BHT Size:** Increase for better pattern recognition
- **Pipeline Depth:** Current 5-stage is optimal for RV32IM

## Debugging and Troubleshooting

### Common Issues

#### 1. Compilation Errors
**Problem:** SystemVerilog syntax errors
**Solution:** 
- Ensure all files are compiled in dependency order
- Check for missing semicolons and brackets
- Verify package imports

#### 2. Simulation Hangs
**Problem:** Simulation doesn't progress
**Solution:**
- Check reset signal is properly asserted
- Verify memory interface handshaking
- Look for infinite loops in test programs

#### 3. Branch Prediction Issues
**Problem:** Low prediction accuracy
**Solution:**
- Check BTB and BHT initialization
- Verify update logic in execute stage
- Monitor branch patterns in test programs

### Debug Techniques

#### 1. Waveform Analysis
```tcl
# In ModelSim
add wave -position insertpoint sim:/riscv_core/*
run -all
```

#### 2. Signal Monitoring
```systemverilog
// Add debug signals to modules
always @(posedge clk_i) begin
    if (debug_enable) begin
        $display("PC: %h, Instruction: %h", pc_f_o, if_id_reg_o.instr);
    end
end
```

#### 3. Performance Monitoring
```systemverilog
// Add performance counters
always @(posedge clk_i) begin
    if (rst_ni) begin
        cycle_count <= cycle_count + 1;
        if (branch_taken) branch_count <= branch_count + 1;
    end
end
```

## Next Steps

### For Students
1. **Study the Pipeline:** Understand each stage's function
2. **Modify Instructions:** Add new instructions to the decode stage
3. **Experiment with Hazards:** Create test cases for different hazard types
4. **Optimize Performance:** Implement additional optimizations

### For Researchers
1. **Extend the Architecture:** Add new pipeline stages or features
2. **Implement New Instructions:** Add custom instructions or extensions
3. **Performance Analysis:** Measure and optimize performance
4. **Publication:** Use the core for research publications

### For Developers
1. **Integration:** Integrate the core into your SoC design
2. **Customization:** Modify for specific application requirements
3. **Verification:** Add comprehensive test suites
4. **Documentation:** Contribute to project documentation

## Getting Help

### Resources
- **[RISC-V Specification](https://riscv.org/specifications/):** Official RISC-V documentation
- **[SystemVerilog LRM](https://ieeexplore.ieee.org/document/8299595):** Language reference
- **[Project Documentation](docs/):** Detailed implementation documentation

### Support Channels
- **GitHub Issues:** Report bugs and request features
- **GitHub Discussions:** Ask questions and share ideas
- **Documentation:** Check the comprehensive docs in `docs/`

### Contributing
1. **Fork the Repository:** Create your own fork
2. **Create Feature Branch:** Work on new features
3. **Add Tests:** Include tests for new functionality
4. **Submit Pull Request:** Contribute back to the project

---

**Quick Start Version:** 1.0  
**Last Updated:** June 2025  
**Core Version:** RV32IM 5-stage Pipeline 