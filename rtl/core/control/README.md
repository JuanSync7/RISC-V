# Core Control Logic

## Overview
This directory contains SystemVerilog modules that implement the control logic for the RISC-V processor core, including hazard detection, pipeline control, and execution flow management.

## Purpose
- Implement pipeline hazard detection and resolution
- Manage instruction flow and control signals
- Handle pipeline stalls and flushes
- Coordinate between pipeline stages

## Contents

### Control Logic Modules
- `hazard_unit.sv` - Pipeline hazard detection and mitigation

## Control Functions

### Hazard Detection
- **Data Hazards**: RAW (Read-After-Write) hazard detection
- **Control Hazards**: Branch and jump instruction handling
- **Structural Hazards**: Resource conflict detection
- **Memory Hazards**: Load/store dependency tracking

### Pipeline Control
- Pipeline stall generation
- Pipeline flush control
- Forwarding path management
- Instruction retirement control

### Advanced Features
- Out-of-order execution support
- Speculative execution control
- Exception and interrupt handling integration
- Quality of Service (QoS) aware control

## Interface Dependencies
- Pipeline stage interfaces
- Execution unit control signals
- Memory system control
- Exception handling interfaces

## Usage
Control modules are instantiated in the main core integration:

```systemverilog
hazard_unit u_hazard_unit (
    .clk(clk),
    .rst_n(rst_n),
    // Pipeline interfaces
    // Control signals
);
```

## Related Directories
- `rtl/core/pipeline/` - Pipeline stage implementations
- `rtl/core/execution/` - Execution unit control
- `rtl/units/` - Functional unit interfaces

---
**Document Version:** 1.0  
**Last Updated:** 2025-07-06  
**Status:** Active 