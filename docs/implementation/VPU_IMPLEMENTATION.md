# Vector Processing Unit (VPU) Implementation

## Overview
This document details the implementation of the Vector Processing Unit (VPU) within the RISC-V core's Data Processing Unit (DPU) subsystem. The VPU is designed to perform parallel operations on vectors of data, significantly accelerating data-parallel workloads. Its modular design allows for optional inclusion based on the `ENABLE_VPU` configuration parameter.

## Task Checklist
- [x] Implement vector addition (`VPU_ADD`).
- [x] Implement vector subtraction (`VPU_SUB`).
- [x] Implement vector multiplication (`VPU_MUL`).
- [x] Implement vector division (`VPU_DIV`).
- [x] Implement vector load (`VPU_LOAD`) from memory.
- [x] Implement vector store (`VPU_STORE`) to memory.
- [ ] Define vector register file structure and access mechanisms.
- [ ] Handle vector length and element-width configurations.
- [ ] Develop a comprehensive testbench (`vpu_tb.sv`) covering all VPU operations and edge cases.
- [ ] Integrate VPU instruction decoding and dispatch in the `decode_stage` and `execute_stage`.

## Implementation Details
The VPU is implemented as `vpu_unit.sv` and is instantiated within `dpu_subsystem.sv` if `ENABLE_VPU` is set to `1'b1`. It communicates via the `vpu_req_t` and `vpu_rsp_t` structures defined in `riscv_vpu_types_pkg.sv`.

### Vector Operations:
The `vpu_op_e` enumeration defines the supported vector operations. Each operation will process multiple data elements in parallel.

### Data Representation:
Vectors are composed of `word_t` elements, with the maximum vector length defined by `MAX_VECTOR_LENGTH` in `riscv_vpu_types_pkg.sv`.

### Pipelining:
The VPU operations can be pipelined internally to maximize throughput for vector computations.

### Memory Access:
`VPU_LOAD` and `VPU_STORE` operations will interact with the memory subsystem to fetch or write entire vectors.

## Interface (`vpu_unit.sv`):
- `clk_i`: System clock.
- `rst_ni`: Asynchronous active-low reset.
- `vpu_req_i`: Input request from `dpu_subsystem`.
- `vpu_req_ready_o`: Indicates VPU is ready to accept a new request.
- `vpu_rsp_o`: Output response to `dpu_subsystem`.
- `vpu_rsp_ready_i`: Acknowledgment from `dpu_subsystem` that response has been consumed.

## Future Considerations:
- Support for masked operations (predication).
- Advanced vector addressing modes (strided, indexed).
- Integration with RISC-V Vector Extensions (RVV) instruction set.
- Support for different element data types (e.g., byte, half-word).

---

**Document Version:** 1.0
**Last Updated:** 2025-07-05
**Author:** AI Agent
**Status:** Draft
