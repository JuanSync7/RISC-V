# RTL Directory

## Overview

This directory contains the Register Transfer Level (RTL) implementation of the RISC-V RV32IM core. The RTL is written in SystemVerilog and follows a modular design approach with clear separation of concerns. The implementation includes a complete 5-stage pipeline with all major functional units.

## Directory Structure

```
rtl/
├── core/                          # Core pipeline implementation
│   ├── riscv_core.sv             # ✅ Main core module
│   ├── riscv_core_pkg.sv         # ✅ Core package definitions
│   ├── fetch_stage.sv            # ✅ Instruction fetch stage
│   ├── decode_stage.sv           # ✅ Instruction decode stage
│   ├── execute_stage.sv          # ✅ Execute stage
│   ├── mem_stage.sv              # ✅ Memory access stage
│   └── writeback_stage.sv        # ✅ Writeback stage
├── units/                         # Functional units
│   ├── alu.sv                    # ✅ Arithmetic Logic Unit
│   ├── reg_file.sv               # ✅ Register file
│   ├── mult_unit.sv              # ✅ Multiplier unit
│   ├── div_unit.sv               # ✅ Divider unit
│   ├── csr_regfile.sv            # ✅ Control and Status Registers
│   └── exception_handler.sv      # ✅ Exception handling
├── control/                       # Control logic
│   └── hazard_unit.sv            # ✅ Pipeline hazard detection
├── memory/                        # Memory system
│   ├── icache.sv                 # ✅ Instruction cache
│   ├── memory_wrapper.sv         # ✅ Memory interface wrapper
│   └── memory_req_rsp_if.sv      # ✅ Memory request/response interface
├── prediction/                    # Branch prediction
│   └── branch_predictor.sv       # ✅ Branch predictor
├── protocols/                     # Communication protocols
│   └── axi4_adapter.sv           # ✅ AXI4 bus adapter
├── interfaces/                    # SystemVerilog interfaces
└── peripherals/                   # Peripheral modules
```

## Design Philosophy

### Modular Architecture
- Each functional unit is implemented as a separate module
- Clear interfaces between modules using SystemVerilog interfaces
- Standardized naming conventions and port structures

### Pipeline Design
- 5-stage pipeline: Fetch, Decode, Execute, Memory, Writeback
- Hazard detection and resolution
- Forwarding logic for data hazards

### Memory System
- Separate instruction and data memory interfaces
- Cache hierarchy support
- Memory-mapped I/O support

## Key Components

### Core Pipeline (`core/`)
The main pipeline implementation with five stages:
- **Fetch Stage**: Instruction memory access and PC management
- **Decode Stage**: Instruction decoding and register file access
- **Execute Stage**: ALU operations and branch resolution
- **Memory Stage**: Data memory access
- **Writeback Stage**: Register file updates

### Functional Units (`units/`)
Specialized processing units:
- **ALU**: Arithmetic and logical operations
- **Register File**: 32 general-purpose registers
- **Multiplier**: Hardware multiplication support
- **Divider**: Hardware division support
- **CSR Register File**: Control and status registers
- **Exception Handler**: Exception and interrupt handling

### Control Logic (`control/`)
Pipeline control and hazard management:
- **Hazard Unit**: Data and control hazard detection
- Forwarding logic implementation
- Pipeline stall and flush control

### Memory System (`memory/`)
Memory interface and caching:
- **Instruction Cache**: L1 instruction cache
- **Memory Wrapper**: Memory interface abstraction
- **Memory Interfaces**: Standardized memory protocols

### Branch Prediction (`prediction/`)
Branch prediction and control flow:
- **Branch Predictor**: Dynamic branch prediction
- Branch target calculation
- Prediction accuracy tracking

### Protocol Adapters (`protocols/`)
Communication protocol support:
- **AXI4 Adapter**: AXI4 bus protocol support
- Memory interface adaptation
- Bus protocol compliance

## Coding Standards

### Naming Conventions
- Module names: `snake_case`
- Signal names: `snake_case` with direction suffix (`_i`, `_o`, `_io`)
- Parameter names: `UPPER_SNAKE_CASE`
- Interface names: `snake_case_if`

### Port Conventions
- Clock: `clk_i`
- Reset: `rst_n_i` (active low)
- Input signals: `signal_name_i`
- Output signals: `signal_name_o`
- Bidirectional signals: `signal_name_io`

### Documentation
- Header comments for all modules
- Parameter descriptions
- Port descriptions
- Function descriptions

## Implementation Status

| Module | Status | Description |
|--------|--------|-------------|
| Core Pipeline | ✅ Complete | All 5 stages implemented |
| ALU | ✅ Complete | All RV32IM operations |
| Register File | ✅ Complete | 32 registers with hazard support |
| Multiplier | ✅ Complete | Hardware multiplication |
| Divider | ✅ Complete | Hardware division |
| CSR Register File | ✅ Complete | Control and status registers |
| Exception Handler | ✅ Complete | Exception and interrupt handling |
| Hazard Unit | ✅ Complete | Pipeline hazard detection |
| Memory Wrapper | ✅ Complete | Memory interface abstraction |
| ICache | ✅ Complete | Instruction cache implementation |
| Branch Predictor | ✅ Complete | Dynamic branch prediction |
| AXI4 Adapter | ✅ Complete | AXI4 bus protocol support |

## Dependencies

### Required Packages
- `riscv_core_pkg.sv`: Core package definitions
- SystemVerilog interfaces for module communication

### External Dependencies
- SystemVerilog 2012 or later
- Synthesis tools supporting SystemVerilog

## Usage

### Compilation
```bash
# Compile all RTL files
vcs -full64 -sverilog -f filelist.f

# Compile specific module
vcs -full64 -sverilog rtl/core/riscv_core.sv
```

### Synthesis
```bash
# Using Design Compiler
dc_shell -f synthesis.tcl

# Using Quartus (FPGA)
quartus_map riscv_core
```

## Future Enhancements

### Phase 1: Performance Optimization
1. **Pipeline Optimization**: Reduce critical path
2. **Cache Optimization**: Improve cache performance
3. **Branch Prediction**: Enhance prediction accuracy
4. **Memory System**: Optimize memory hierarchy

### Phase 2: Advanced Features
1. **Superscalar Execution**: Multiple instructions per cycle
2. **Out-of-Order Execution**: Dynamic instruction scheduling
3. **Speculative Execution**: Branch speculation
4. **Vector Processing**: SIMD operations

### Phase 3: System Integration
1. **Peripheral Support**: UART, SPI, I2C interfaces
2. **Memory Management**: MMU and TLB support
3. **Security Features**: Memory protection units
4. **Debug Support**: Debug interface and trace

## Contributing

When adding new modules:

1. Follow the established naming conventions
2. Include comprehensive header documentation
3. Use SystemVerilog interfaces for module communication
4. Add appropriate parameterization
5. Include reset and clock domain considerations
6. Update this README with new module information

## Support

For questions or issues:
1. Check the module header documentation
2. Review similar modules for examples
3. Consult the architecture documentation
4. Check the testbench for usage examples 