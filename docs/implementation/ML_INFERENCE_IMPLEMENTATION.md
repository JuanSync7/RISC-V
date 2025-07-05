# Machine Learning Inference Unit (MLIU) Implementation

## Overview
This document outlines the conceptual implementation of a Machine Learning Inference Unit (MLIU) as part of the RISC-V core's Data Processing Unit (DPU) subsystem. The MLIU is envisioned to accelerate common machine learning inference tasks, such as neural network forward passes. This module is currently a placeholder, designed for future expansion and integration.

## Task Checklist
- [x] Define specific ML inference operations (e.g., matrix multiplication, convolution, activation functions).
- [ ] Determine optimal data types for ML inference (e.g., fixed-point, INT8, BFloat16).
- [ ] Design the MLIU's internal architecture (e.g., systolic arrays, specialized MAC units).
- [ ] Implement data loading and weight storage mechanisms.
- [ ] Develop a comprehensive testbench (`mliu_tb.sv`) for MLIU functionality.
- [x] Integrate MLIU instruction decoding and dispatch in the main RISC-V pipeline.

## Implementation Details (Conceptual)
The MLIU will be implemented as `ml_inference_unit.sv` and instantiated within `dpu_subsystem.sv` if `ENABLE_ML_INFERENCE` is set to `1'b1`. The current placeholder provides basic pass-through functionality.

### Operations:
Future operations will focus on accelerating key primitives for neural network inference.

### Data Flow:
Data and weights will likely be streamed into the MLIU, and results will be streamed out or written back to memory.

## Interface (`ml_inference_unit.sv`):
- `clk_i`: System clock.
- `rst_ni`: Asynchronous active-low reset.
- `mliu_req_i`: Input request from `dpu_subsystem`.
- `mliu_req_ready_o`: Indicates MLIU is ready to accept a new request.
- `mliu_rsp_o`: Output response to `dpu_subsystem`.
- `mliu_rsp_ready_i`: Acknowledgment from `dpu_subsystem` that response has been consumed.

## Future Considerations:
- Support for various neural network architectures (CNNs, RNNs, Transformers).
- Programmable weight and bias storage.
- Quantization support for reduced precision inference.
- Integration with higher-level ML frameworks.

---

**Document Version:** 1.0
**Last Updated:** 2025-07-05
**Author:** AI Agent
**Status:** Placeholder / Conceptual
