# RISC-V Core Implementation
## RV32IM 5-Stage Pipeline Processor

[![RISC-V](https://img.shields.io/badge/RISC--V-RV32IM-blue.svg)](https://riscv.org/)
[![SystemVerilog](https://img.shields.io/badge/SystemVerilog-IEEE%201800--2017-orange.svg)](https://ieeexplore.ieee.org/document/8299595)
[![License](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Status](https://img.shields.io/badge/Status-Production%20Ready-brightgreen.svg)](CURRENT_IMPLEMENTATION.md)

A complete, synthesizable RISC-V RV32IM core implementation featuring a 5-stage pipeline with advanced hazard detection, forwarding logic, and support for all RV32I base instructions plus RV32M multiplication and division extensions.

---

## 🚀 Features

### ✅ **Complete RV32IM Support**
- **RV32I Base Integer Instructions:** All arithmetic, logical, shift, comparison, branch, jump, and memory operations
- **RV32M Multiplication:** MUL, MULH, MULHSU, MULHU with multi-cycle implementation
- **RV32M Division:** DIV, DIVU, REM, REMU with exception handling (division by zero, overflow)

### 🏗️ **Advanced Pipeline Architecture**
- **5-Stage Pipeline:** Fetch, Decode, Execute, Memory, Writeback
- **Hazard Detection:** Comprehensive data, control, and structural hazard handling
- **Forwarding Logic:** EX/MEM → EX and MEM/WB → EX forwarding paths
- **Stall Management:** Intelligent pipeline stalling for multi-cycle operations

### 🔧 **Industry-Standard Interfaces**
- **AXI4-Lite Memory Interface:** Instruction and data memory interfaces
- **Synthesizable Design:** Clean, lint-free RTL code following IEEE 1800-2017
- **Configurable Parameters:** Easily adaptable for different target technologies

### 🛡️ **Robust Design**
- **Overflow Detection:** ALU overflow detection for arithmetic operations
- **Exception Handling:** Basic exception detection and handling framework
- **CSR Support:** Control and status register operations
- **Reset Strategy:** Asynchronous reset with synchronous de-assertion

---

## 📊 Performance Characteristics

| Metric | Value | Notes |
|--------|-------|-------|
| **IPC (Instructions Per Cycle)** | ~0.8 | Typical for 5-stage pipeline |
| **Pipeline Efficiency** | ~70% | Due to hazards and stalls |
| **Clock Frequency Target** | 100MHz | Depends on synthesis |
| **Resource Utilization** | ~5K-8K LUTs | FPGA implementation estimate |

---

## 🏗️ Architecture Overview

```
┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐
│  Fetch  │───▶│ Decode  │───▶│Execute  │───▶│ Memory  │───▶│Writeback│
│  Stage  │    │  Stage  │    │ Stage   │    │  Stage  │    │  Stage  │
└─────────┘    └─────────┘    └─────────┘    └─────────┘    └─────────┘
     │              │              │              │              │
     ▼              ▼              ▼              ▼              ▼
  PC + 4        Register      ALU/Mult/Div    Memory        Register
  Branch        Read          Operations      Access         Write
  Prediction    Hazard        Forwarding      AXI4          Hazard
  (Future)      Detection     Logic           Interface     Resolution
```

### Pipeline Stages
1. **Fetch Stage:** Instruction fetching via AXI4-Lite interface
2. **Decode Stage:** Instruction decoding and register file read
3. **Execute Stage:** ALU, multiplier, divider, and branch operations
4. **Memory Stage:** Load/store operations via AXI4-Lite interface
5. **Writeback Stage:** Register file write and result forwarding

---

## 📁 Project Structure

```
RISC-V/
├── 📚 Documentation
│   ├── docs/
│   │   ├── architecture/           # Architecture documentation
│   │   ├── implementation/         # Implementation details
│   │   └── user_guide/             # User guides and tutorials
│   ├── CURRENT_IMPLEMENTATION.md   # Current implementation details
│   ├── PHASE1_IMPROVEMENTS.md      # Phase 1 improvement roadmap
│   └── README.md                   # This file
├── 🔧 RTL Design Files (rtl/)
│   ├── config/                     # Configuration packages
│   │   ├── core/                   # Core-specific configuration
│   │   ├── memory/                 # Memory configuration  
│   │   └── protocol/               # Protocol configuration
│   ├── core/                       # Core processor implementation
│   │   ├── riscv_core.sv           # Top-level core integration
│   │   ├── pipeline/               # Pipeline stages
│   │   │   ├── fetch_stage.sv      # Instruction fetch stage
│   │   │   ├── decode_stage.sv     # Instruction decode stage
│   │   │   ├── execute_stage.sv    # Execute stage with ALU/Mult/Div
│   │   │   ├── mem_stage.sv        # Memory access stage
│   │   │   └── writeback_stage.sv  # Writeback stage
│   │   ├── control/                # Control and hazard logic
│   │   │   └── hazard_unit.sv      # Hazard detection and forwarding
│   │   ├── execution/              # Out-of-order execution
│   │   │   ├── reorder_buffer.sv   # Reorder buffer
│   │   │   └── reservation_station.sv # Reservation stations
│   │   ├── prediction/             # Branch prediction components
│   │   │   └── branch_predictor.sv # Tournament branch predictor
│   │   └── integration/            # System integration
│   │       └── multi_core_system.sv # Multi-core system
│   ├── memory/                     # Memory subsystem
│   │   ├── cache/                  # Cache implementations
│   │   │   ├── icache.sv           # L1 instruction cache
│   │   │   ├── l2_cache.sv         # L2 shared cache
│   │   │   └── l3_cache.sv         # L3 cache
│   │   └── wrappers/               # Memory interface wrappers
│   │       └── memory_wrapper.sv   # Protocol abstraction
│   ├── protocol/                   # Protocol implementations
│   │   ├── axi/                    # AXI4 protocol
│   │   │   └── axi4_adapter.sv     # AXI4 adapter
│   │   └── chi/                    # CHI protocol
│   │       └── chi_adapter.sv      # CHI adapter
│   ├── shared/                     # Shared components
│   │   ├── interfaces/             # Interface definitions
│   │   │   ├── axi4_if.sv          # AXI4 interface
│   │   │   └── memory_req_rsp_if.sv # Generic memory interface
│   │   └── packages/               # Type definitions
│   │       └── riscv_core_pkg.sv   # Core types and constants
│   ├── units/                      # Functional units
│   │   ├── alu.sv                  # Arithmetic Logic Unit
│   │   ├── mult_unit.sv            # Multi-cycle multiplier
│   │   ├── div_unit.sv             # Multi-cycle divider
│   │   ├── reg_file.sv             # 32x32 register file
│   │   └── csr_regfile.sv          # Control and status registers
│   └── peripherals/                # Peripheral components
│       └── (Future: uart.sv, timer.sv)
├── 🧪 Testbench and Verification (tb/)
│   ├── testbench/                  # Testbench files
│   ├── tests/                      # Test cases
│   ├── models/                     # Behavioral models
│   └── scripts/                    # Test automation
├── 🔬 Simulation (sim/)
│   ├── scripts/                    # Simulation scripts
│   ├── constraints/                # Timing constraints
│   └── logs/                       # Simulation logs
├── 🔌 FPGA Implementation (fpga/)
│   ├── projects/                   # FPGA project files
│   ├── constraints/                # FPGA constraints
│   └── bitstreams/                 # Generated bitstreams
├── 🏭 ASIC Implementation (asic/)
│   ├── synthesis/                  # Synthesis files
│   ├── place_route/                # Place and route files
│   └── verification/               # ASIC verification
├── 🛠️ Development Tools (tools/)
│   ├── scripts/                    # Utility scripts
│   ├── config/                     # Tool configurations
│   └── templates/                  # Code templates
├── 💻 Software (software/)
│   ├── examples/                   # Example programs
│   ├── benchmarks/                 # Benchmark programs
│   └── tools/                      # Software tools
└── 🔄 Continuous Integration (ci/)
    ├── .github/                    # GitHub Actions
    └── docker/                     # Docker configurations
```

---

## 🚀 Quick Start

### Prerequisites
- **SystemVerilog Simulator:** ModelSim, VCS, Xcelium, or similar
- **Synthesis Tool:** Xilinx Vivado, Intel Quartus, or Synopsys Design Compiler
- **RISC-V Toolchain:** For compiling test programs

### Simulation Setup
```bash
# Clone the repository
git clone <repository-url>
cd RISC-V

# Compile SystemVerilog files (updated directory structure)
# Configuration packages (must be first)
vlog rtl/config/core/*.sv

# Shared packages and interfaces
vlog rtl/shared/packages/*.sv
vlog rtl/shared/interfaces/*.sv

# Functional units
vlog rtl/units/alu.sv
vlog rtl/units/mult_unit.sv
vlog rtl/units/div_unit.sv
vlog rtl/units/reg_file.sv
vlog rtl/units/csr_regfile.sv

# Memory subsystem
vlog rtl/memory/cache/*.sv
vlog rtl/memory/wrappers/*.sv

# Protocol adapters
vlog rtl/protocol/axi/*.sv

# Core control and prediction
vlog rtl/core/control/hazard_unit.sv
vlog rtl/core/prediction/branch_predictor.sv
vlog rtl/core/execution/*.sv

# Core pipeline stages
vlog rtl/core/pipeline/fetch_stage.sv
vlog rtl/core/pipeline/decode_stage.sv
vlog rtl/core/pipeline/execute_stage.sv
vlog rtl/core/pipeline/mem_stage.sv
vlog rtl/core/pipeline/writeback_stage.sv

# Core integration and top-level
vlog rtl/core/integration/*.sv
vlog rtl/core/riscv_core.sv

# Run simulation (example with ModelSim)
vsim -c riscv_core -do "run -all; quit"
```

### Synthesis Setup
```bash
# For Xilinx Vivado
vivado -mode batch -source synth_script.tcl

# For Intel Quartus
quartus_sh --flow compile riscv_core
```

---

## 🔧 Configuration

### Key Parameters
```systemverilog
// Core configuration
parameter addr_t RESET_VECTOR = 32'h0000_0000;  // Reset vector address
parameter integer DATA_WIDTH = 32;              // Data width
parameter integer ADDR_WIDTH = 32;              // Address width

// Memory interface configuration
parameter integer AXI_DATA_WIDTH = 32;          // AXI data width
parameter integer AXI_ADDR_WIDTH = 32;          // AXI address width
```

### Target Technology
- **FPGA:** Xilinx 7-series, Intel Cyclone V, and compatible families
- **ASIC:** 28nm and below technology nodes
- **Clock Frequency:** 100MHz target (configurable)

---

## 🧪 Testing and Verification

### Verification Status
- ✅ **RV32I Base Instructions:** All instructions verified
- ✅ **RV32M Multiplication:** All multiplication types verified
- ✅ **RV32M Division:** All division types verified
- ✅ **Hazard Handling:** Data hazards and forwarding verified
- ✅ **Memory Operations:** Load/store operations verified
- ✅ **AXI4-Lite Protocol:** Interface compliance verified

### Test Programs
- **RISC-V Compliance Tests:** Basic instruction compliance
- **Synthetic Benchmarks:** Performance and functionality testing
- **Custom Test Programs:** Specific feature verification

### Running Tests
```bash
# Run compliance tests
make compliance

# Run performance benchmarks
make benchmark

# Run custom tests
make test
```

---

## 📈 Development Roadmap

### ✅ **Current Status (v1.3.0)**
- Complete RV32IMA implementation (including RV32A atomic extension)
- Phase 3 interface refactoring **COMPLETED**
  - Generic `memory_if` interface introduced
  - Placeholder `axi4_if` interface for SoC integration
  - Adapter path for future TileLink/CHI support
- Comprehensive verification infrastructure (unit, subsystem, system)
- New test automation script `scripts/run_tb.sh` (Icarus Verilog)
- Development status report (`DEVELOPMENT_STATUS.md`) added

### � **Next Milestones**
- **Phase 4:** System-level configuration validation and performance counters
- **Phase 5:** RV32F/D floating-point unit integration

---

## 📚 Documentation

### 📖 **Detailed Documentation**
- **[Current Implementation](CURRENT_IMPLEMENTATION.md):** Comprehensive implementation details
- **[Phase 1 Roadmap](PHASE1_IMPROVEMENTS.md):** Detailed improvement plans
- **[RISC-V Specification](https://riscv.org/specifications/):** Official RISC-V documentation

### 🔍 **Module Documentation**
Each SystemVerilog module includes:
- Detailed header comments with AI_TAG documentation
- Interface descriptions and parameter definitions
- Implementation notes and design decisions
- Verification requirements and test scenarios

---

## 🤝 Contributing

### Development Guidelines
1. **Follow SystemVerilog Standards:** IEEE 1800-2017 compliance
2. **Use AI_TAG Documentation:** For automated documentation generation
3. **Maintain Code Quality:** Lint-free, synthesizable RTL
4. **Add Tests:** Comprehensive verification for new features
5. **Update Documentation:** Keep documentation current

### Code Style
- **Naming Convention:** snake_case for signals, UPPER_CASE for parameters
- **File Headers:** Standard header with version and description
- **Comments:** Comprehensive inline documentation
- **Modular Design:** Clear interfaces and separation of concerns

---

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

---

## 🙏 Acknowledgments

- **RISC-V Foundation:** For the open instruction set architecture
- **IEEE:** For SystemVerilog standard (IEEE 1800-2017)
- **Open Source Community:** For tools and resources

---

## 📞 Support

### Getting Help
- **Documentation:** Check the detailed implementation docs
- **Issues:** Report bugs and feature requests via GitHub issues
- **Discussions:** Use GitHub discussions for questions and ideas

### Resources
- **[RISC-V Foundation](https://riscv.org/):** Official RISC-V resources
- **[SystemVerilog LRM](https://ieeexplore.ieee.org/document/8299595):** Language reference
- **[Verification Resources](https://github.com/riscv/riscv-compliance):** RISC-V compliance tests

---

## 🎯 Project Goals

This RISC-V core implementation aims to provide:

1. **Educational Value:** Clear, well-documented implementation for learning
2. **Research Platform:** Foundation for computer architecture research
3. **Production Ready:** Synthesizable design for real-world applications
4. **Extensible Architecture:** Easy to add new features and extensions
5. **Open Source:** Freely available for academic and commercial use

---

**Version:** 1.3.0  
**Last Updated:** 2025-01-29  
**Status:** Production Ready  
**Maintainer:** RISC-V Core Development Team
