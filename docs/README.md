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
- **exception_handling_implementation.md** - Detailed exception handling implementation guide
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
- **Instruction Cache** - 4KB 2-way set associative cache
- **Enhanced Exception Handling** - Complete M-mode exception support

### Phase 1 Improvements (Completed)
- **Branch Prediction** - Enhanced 2-bit saturating counter with BTB/BHT
- **Instruction Cache** - 4KB 2-way set associative cache with LRU replacement
- **Enhanced Exception Handling** - Complete M-mode exception and interrupt support
  - Exception Handler Module (`exception_handler.sv`)
  - Distributed exception detection across pipeline stages
  - Enhanced CSR file with complete M-mode support
  - Proper exception prioritization and vector generation
  - Interrupt masking and control
  - Context saving and restoration

## Exception Handling System

### Key Components
1. **Exception Handler Module** - Central exception coordination and prioritization
2. **Pipeline Stage Detection** - Distributed exception detection across fetch, execute, and memory stages
3. **Enhanced CSR File** - Complete M-mode CSR support with context saving/restoration
4. **Pipeline Integration** - Exception propagation, PC redirection, and pipeline flush

### Supported Exceptions
- **Instruction Exceptions:** Address misalignment, access faults, illegal instructions
- **Arithmetic Exceptions:** Division by zero, overflow
- **Memory Exceptions:** Load/store misalignment, access faults
- **System Exceptions:** ECALL, EBREAK
- **Interrupts:** Software, timer, external interrupts

### Performance Characteristics
- **Exception Detection:** 1-3 cycles (pipeline stage dependent)
- **Handler Entry:** 1 cycle (PC redirect)
- **Context Save:** 1 cycle (CSR updates)
- **Total Latency:** 3-5 cycles from exception to handler
- **Interrupt Response:** 3 cycles total

## Quick Reference

### Core Specifications
- **Architecture:** RV32IM (RISC-V 32-bit Integer + Multiply/Divide)
- **Pipeline Stages:** 5 (Fetch, Decode, Execute, Memory, Writeback)
- **Data Width:** 32-bit
- **Address Width:** 32-bit
- **Register File:** 32 general-purpose registers
- **Memory Interface:** AXI4 with protocol-agnostic wrapper

### Performance Targets
- **Frequency:** 100+ MHz (FPGA), 500+ MHz (ASIC)
- **IPC:** >0.8 (current), >1.0 (with Phase 1 improvements)
- **Branch Prediction Accuracy:** >85%
- **Cache Hit Rate:** >90% (with instruction cache)
- **Exception Latency:** <5 cycles

## Documentation Updates

### Recent Updates (2025-06-28)
- Enhanced Exception Handling Documentation - Complete architecture and implementation guides
- Phase 1 Improvements Status - Updated to reflect completed features
- Exception Handler Implementation Guide - Detailed implementation documentation
- Memory Wrapper Documentation - Protocol-agnostic memory interface

### Next Steps
- Integration testing and performance benchmarking
- Verification of exception handling system
- Performance optimization and tuning
- Phase 2 planning (multicore support, advanced features) 