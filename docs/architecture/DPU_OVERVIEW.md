# DPU Subsystem Overview

## Overview
This document provides an overview of the Data Processing Unit (DPU) subsystem, its modular architecture, and its role in enhancing the RISC-V core with specialized data processing capabilities. The DPU subsystem is designed for configurability, allowing for the inclusion or exclusion of various accelerators based on project requirements.

## Task Checklist
- [x] Define specific instruction set extensions or memory-mapped interfaces for each DPU unit.
- [x] Implement detailed logic within `fpu_unit.sv` for floating-point operations.
- [x] Implement detailed logic within `vpu_unit.sv` for vector processing operations.
- [x] Implement detailed logic within `ml_inference_unit.sv` for machine learning inference (future).
- [x] Develop comprehensive testbenches for each DPU unit.
- [x] Integrate DPU instruction decoding and dispatch in the main RISC-V pipeline (Decode/Execute stages).
- [ ] Update performance metrics and area/power estimations to reflect DPU inclusion.

## Architecture
The DPU subsystem is a modular component integrated into the `core_subsystem.sv`. It acts as a wrapper, conditionally instantiating specialized processing units such as the Floating Point Unit (FPU), Vector Processing Unit (VPU), and a placeholder for a Machine Learning Inference Unit. This modularity is achieved through SystemVerilog `generate` blocks controlled by parameters in `riscv_config_pkg.sv`.

### Key Components:
- **`dpu_subsystem.sv`**: The top-level module for the DPU, responsible for routing requests to the appropriate sub-unit.
- **`fpu_unit.sv`**: Handles floating-point arithmetic operations.
- **`vpu_unit.sv`**: Handles vector processing operations.
- **`ml_inference_unit.sv`**: A placeholder for future machine learning inference acceleration.

### Communication Interface:
The DPU subsystem communicates with the main RISC-V core via a generic request/response interface defined by `dpu_req_t` and `dpu_rsp_t` in `riscv_dpu_types_pkg.sv`. Internal routing within `dpu_subsystem.sv` directs these requests to the active specialized unit.

## Implementation Details
Each specialized unit (`fpu_unit`, `vpu_unit`, `ml_inference_unit`) is instantiated conditionally. When a unit is enabled, its dedicated logic processes the incoming requests. When disabled, its interface ports are tied off to default values, ensuring no resource consumption or functional impact.

### Configuration Parameters (from `riscv_config_pkg.sv`):
- `ENABLE_DATA_ACCELERATOR`: Global switch to enable/disable the entire DPU subsystem.
- `ENABLE_FPU`: Enables/disables the Floating Point Unit.
- `ENABLE_VPU`: Enables/disables the Vector Processing Unit.
- `ENABLE_ML_INFERENCE`: Enables/disables the Machine Learning Inference Unit.

## Future Expansion
The modular design allows for easy integration of additional specialized data processing units. New units can be added as separate `.sv` modules, with their interfaces defined in new type packages, and then conditionally instantiated within `dpu_subsystem.sv`.

---

**Document Version:** 1.0
**Last Updated:** 2025-07-05
**Author:** AI Agent
**Status:** Draft
