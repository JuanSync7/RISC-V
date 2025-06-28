# RISC-V Core Documentation

## Overview
This directory contains comprehensive documentation for the RISC-V core project, organized by category for easy navigation and reference.

## Documentation Structure

### Architecture Documentation (`architecture/`)
- **pipeline.md** - Detailed pipeline architecture and stage descriptions
- **memory_system.md** - Memory hierarchy and interface specifications
- **exception_handling.md** - Exception and interrupt handling mechanisms
- **performance.md** - Performance characteristics and optimization strategies

### Implementation Documentation (`implementation/`)
- **current_implementation.md** - Current implementation status and details
- **phase1_improvements.md** - Phase 1 improvement plans and progress
- **verification_plan.md** - Verification strategy and test plans

### User Guide (`user_guide/`)
- **getting_started.md** - Quick start guide for new users
- **configuration.md** - Configuration options and parameters
- **troubleshooting.md** - Common issues and solutions

## Project Structure

```
RISC-V/
├── rtl/                    # RTL Design Files
│   ├── core/              # Core pipeline stages
│   ├── units/             # Functional units (ALU, multiplier, etc.)
│   ├── control/           # Control and hazard logic
│   ├── prediction/        # Branch prediction components
│   ├── memory/            # Memory system components
│   ├── interfaces/        # Interface definitions
│   └── peripherals/       # Peripheral components
├── tb/                    # Testbench and verification
├── sim/                   # Simulation files
├── fpga/                  # FPGA implementation
├── asic/                  # ASIC implementation
├── tools/                 # Development tools
├── software/              # Software tools and examples
└── ci/                    # Continuous Integration
```

## Current Status

### Completed Features
- **RV32IM Core Pipeline** - 5-stage pipelined RISC-V core
- **Branch Prediction Unit** - 2-bit saturating counter with BTB/BHT
- **Multiplication Unit** - Multi-cycle RV32M multiplication
- **Division Unit** - Multi-cycle RV32M division
- **CSR Support** - Machine-mode CSR operations
- **Hazard Detection** - Full data and control hazard handling
- **AXI4 Interface** - Memory interface for instruction and data

### Phase 1 Improvements (In Progress)
- **Instruction Cache** - 4KB 2-way set associative cache
- **Enhanced Exception Handling** - Complete M-mode exception support

## Quick Reference

### Core Specifications
- **Architecture:** RV32IM (RISC-V 32-bit Integer + Multiply/Divide)
- **Pipeline Stages:** 5 (Fetch, Decode, Execute, Memory, Writeback)
- **Data Width:** 32-bit
- **Address Width:** 32-bit
- **Register File:** 32 general-purpose registers
- **Memory Interface:** AXI4

### Performance Targets
- **Frequency:** 100+ MHz (FPGA), 500+ MHz (ASIC)
- **IPC:** >0.8 (current), >1.0 (with Phase 1 improvements)
- **Branch Prediction Accuracy:** >85%
- **Cache Hit Rate:** >90% (with instruction cache) 