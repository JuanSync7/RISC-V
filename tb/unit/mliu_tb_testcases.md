# MLIU Testbench Test Cases

This document details the test cases implemented in `mliu_tb.sv` for verifying the functionality of the Machine Learning Inference Unit (MLIU).

## Testbench Overview

The `mliu_tb.sv` testbench is designed to perform unit-level verification of the `ml_inference_unit` module. It simulates various ML-specific operations, including matrix multiplication, convolution, activation functions (ReLU), and pooling (Max Pooling). It also includes tests for unsupported opcodes.

## Test Scenarios

### MLIU_TC_001: MLIU_MATRIX_MUL (Placeholder)

- **Description:** Verifies the MLIU_MATRIX_MUL operation with example inputs.
- **Operation:** Example Matrix Multiplication
- **Inputs:**
    - `operand1`: 32'h0000000A (Example input)
    - `operand2`: 32'h00000005 (Example weight)
- **Expected Output:** 32'h0000000F (Example result)
- **Expected Error:** None

### MLIU_TC_002: MLIU_CONVOLUTION (Placeholder)

- **Description:** Verifies the MLIU_CONVOLUTION operation with example inputs.
- **Operation:** Example Convolution
- **Inputs:**
    - `operand1`: 32'h00000003 (Example input)
    - `operand2`: 32'h00000002 (Example kernel)
- **Expected Output:** 32'h00000006 (Example result)
- **Expected Error:** None

### MLIU_TC_003: MLIU_ACTIVATION (ReLU)

- **Description:** Verifies the MLIU_ACTIVATION operation with ReLU function for negative and positive inputs.
- **Operation:** ReLU(-16) and ReLU(10)
- **Inputs:**
    - `operand1`: 32'hFFFFFFF0 (-16)
    - `operand1`: 32'h0000000A (10)
- **Expected Output:** 32'h00000000 (for -16), 32'h0000000A (for 10)
- **Expected Error:** None

### MLIU_TC_004: MLIU_POOLING (Max Pooling)

- **Description:** Verifies the MLIU_POOLING operation with Max Pooling.
- **Operation:** Max(7, 12)
- **Inputs:**
    - `operand1`: 32'h00000007 (7)
    - `operand2`: 32'h0000000C (12)
- **Expected Output:** 32'h0000000C (12)
- **Expected Error:** None

### MLIU_TC_005: Unsupported Opcode

- **Description:** Tests the MLIU's behavior with an unsupported opcode, expecting an error.
- **Operation:** Invalid opcode (4'hF)
- **Inputs:**
    - `opcode`: 4'hF
- **Expected Output:** Undefined (error flag set)
- **Expected Error:** `error` flag set to 1
