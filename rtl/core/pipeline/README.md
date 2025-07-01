# Pipeline Stages

## Overview
This directory contains SystemVerilog modules that implement the 5-stage RISC-V processor pipeline: Fetch, Decode, Execute, Memory, and Writeback stages. Each stage is optimized for high performance and supports advanced features.

## Purpose
- Implement classical RISC pipeline architecture
- Support out-of-order execution integration
- Provide high-performance instruction processing
- Enable advanced pipeline optimizations

## Contents

### Pipeline Stage Modules
- `fetch_stage.sv` - Instruction fetch stage with branch prediction
- `decode_stage.sv` - Instruction decode and register read stage
- `execute_stage.sv` - Instruction execution stage
- `mem_stage.sv` - Memory access stage with cache interface
- `writeback_stage.sv` - Register writeback and commit stage

## Pipeline Architecture

### 5-Stage Pipeline
1. **Fetch (IF)**: Instruction fetch from I-cache
2. **Decode (ID)**: Instruction decode and register file read
3. **Execute (EX)**: ALU operations and address calculation
4. **Memory (MEM)**: Data cache access for load/store
5. **Writeback (WB)**: Register file write and instruction commit

### Advanced Features
- **Branch Prediction**: Integrated branch prediction in fetch stage
- **Forwarding**: Data forwarding between pipeline stages
- **Hazard Handling**: Pipeline stall and flush support
- **Out-of-Order Integration**: Interface with OoO execution engine

## Pipeline Flow
```
[Fetch] → [Decode] → [Execute] → [Memory] → [Writeback]
   ↓         ↓          ↓          ↓           ↓
Branch    Register   ALU Ops    Cache      Register
Predict   Decode     Address    Access     Commit
```

### Stage Interfaces
- Standard pipeline registers between stages
- Control signal propagation
- Exception and interrupt handling
- Performance monitoring integration

## Performance Optimizations
- Pipeline register optimization
- Critical path analysis and optimization
- Branch prediction integration
- Cache interface optimization

## Dependencies
- Functional units (`rtl/units/`)
- Cache system (`rtl/memory/cache/`)
- Control logic (`rtl/core/control/`)
- Branch prediction (`rtl/core/prediction/`)

## Integration
Pipeline stages are integrated in the core subsystem and work with:
- Out-of-order execution engine
- Cache hierarchy
- Exception handling system
- Performance monitoring

---
**Document Version:** 1.0  
**Last Updated:** 2024-12-19  
**Status:** Active 