# Floating Point Unit (FPU) Implementation

## Overview
This document details the implementation of the Floating Point Unit (FPU) within the RISC-V core's Data Processing Unit (DPU) subsystem. The FPU is designed to handle single-precision (32-bit) floating-point arithmetic operations as defined by the IEEE 754 standard. Its modular design allows for optional inclusion based on the `ENABLE_FPU` configuration parameter.

## Task Checklist
- [x] Implement IEEE 754 single-precision floating-point addition (`FPU_ADD`).
- [x] Implement IEEE 754 single-precision floating-point subtraction (`FPU_SUB`).
- [x] Implement IEEE 754 single-precision floating-point multiplication (`FPU_MUL`).
- [x] Implement IEEE 754 single-precision floating-point division (`FPU_DIV`).
- [x] Implement IEEE 754 single-precision floating-point square root (`FPU_SQRT`).
- [x] Implement floating-point to integer conversion (`FPU_F2I`).
- [x] Implement integer to floating-point conversion (`FPU_I2F`).
- [ ] Handle denormalized numbers, infinities, NaNs, and rounding modes.
- [ ] Develop a comprehensive testbench (`fpu_tb.sv`) covering all FPU operations and edge cases.
- [ ] Integrate FPU instruction decoding and dispatch in the `decode_stage` and `execute_stage`.

## Implementation Details
The FPU is implemented as `fpu_unit.sv` and is instantiated within `dpu_subsystem.sv` if `ENABLE_FPU` is set to `1'b1`. It communicates via the `fpu_req_t` and `fpu_rsp_t` structures defined in `riscv_fpu_types_pkg.sv`.

### FPU Operations:
The `fpu_op_e` enumeration defines the supported floating-point operations. Each operation will require dedicated combinational or sequential logic for its computation.

### Data Representation:
All floating-point numbers are assumed to be in IEEE 754 single-precision (32-bit) format.

### Pipelining:
The FPU operations can be pipelined internally to achieve higher throughput, depending on the complexity of the operation and performance targets.

### Exception Handling:
The FPU will generate floating-point exceptions (e.g., invalid operation, division by zero, overflow, underflow, inexact) and report them via the `error` field in `fpu_rsp_t`.

## Interface (`fpu_unit.sv`):
- `clk_i`: System clock.
- `rst_ni`: Asynchronous active-low reset.
- `fpu_req_i`: Input request from `dpu_subsystem`.
- `fpu_req_ready_o`: Indicates FPU is ready to accept a new request.
- `fpu_rsp_o`: Output response to `dpu_subsystem`.
- `fpu_rsp_ready_i`: Acknowledgment from `dpu_subsystem` that response has been consumed.

## Future Considerations:
- Support for double-precision floating-point operations.
- Hardware support for fused multiply-add (FMA) operations.
- Integration with RISC-V Floating-Point Extensions (RVF, RVD) instruction set.

---

**Document Version:** 1.0
**Last Updated:** 2025-07-05
**Author:** AI Agent
**Status:** Draft
