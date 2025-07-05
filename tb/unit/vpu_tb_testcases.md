# VPU Testbench Test Cases

This document details the test cases implemented in `vpu_tb.sv` for verifying the functionality of the Vector Processing Unit (VPU).

## Testbench Overview

The `vpu_tb.sv` testbench is designed to perform unit-level verification of the `vpu_unit` module. It simulates various vector operations, including arithmetic operations (ADD, SUB, MUL, DIV), and memory operations (LOAD, STORE). It also includes tests for error conditions like division by zero.

## Test Scenarios

### VPU_TC_001: VPU_ADD (Vector Addition)

- **Description:** Verifies the VPU_ADD operation with two input vectors.
- **Operation:** Vector1 + Vector2
- **Inputs:**
    - `vector_length`: 4
    - `operand1_vector`: {1, 2, 3, 4}
    - `operand2_vector`: {5, 6, 7, 8}
- **Expected Output:** {6, 8, 10, 12}
- **Expected Error:** None

### VPU_TC_002: VPU_SUB (Vector Subtraction)

- **Description:** Verifies the VPU_SUB operation with two input vectors.
- **Operation:** Vector1 - Vector2
- **Inputs:**
    - `vector_length`: 4
    - `operand1_vector`: {10, 11, 12, 13}
    - `operand2_vector`: {1, 2, 3, 4}
- **Expected Output:** {9, 9, 9, 9}
- **Expected Error:** None

### VPU_TC_003: VPU_MUL (Vector Multiplication)

- **Description:** Verifies the VPU_MUL operation with two input vectors.
- **Operation:** Vector1 * Vector2
- **Inputs:**
    - `vector_length`: 3
    - `operand1_vector`: {2, 3, 4}
    - `operand2_vector`: {5, 6, 7}
- **Expected Output:** {10, 18, 28}
- **Expected Error:** None

### VPU_TC_004: VPU_DIV (Vector Division)

- **Description:** Verifies the VPU_DIV operation with two input vectors.
- **Operation:** Vector1 / Vector2
- **Inputs:**
    - `vector_length`: 2
    - `operand1_vector`: {10, 12}
    - `operand2_vector`: {2, 3}
- **Expected Output:** {5, 4}
- **Expected Error:** None

### VPU_TC_005: VPU_DIV (Division by Zero)

- **Description:** Verifies the VPU_DIV operation with division by zero in one of the elements, expecting an error.
- **Operation:** {10, 12} / {2, 0}
- **Inputs:**
    - `vector_length`: 2
    - `operand1_vector`: {10, 12}
    - `operand2_vector`: {2, 0}
- **Expected Output:** Undefined (error flag set)
- **Expected Error:** `error` flag set to 1

### VPU_TC_006: VPU_STORE (Store Vector to Memory)

- **Description:** Verifies the VPU_STORE operation, storing a vector to a specified memory address.
- **Operation:** Store {AA, BB, CC, DD} to address 0x100
- **Inputs:**
    - `vector_length`: 4
    - `addr`: 32'h100
    - `operand1_vector`: {32'hAA, 32'hBB, 32'hCC, 32'hDD}
- **Expected Output:** Memory at 0x100 contains {AA, BB, CC, DD}
- **Expected Error:** None

### VPU_TC_007: VPU_LOAD (Load Vector from Memory)

- **Description:** Verifies the VPU_LOAD operation, loading a vector from a specified memory address.
- **Operation:** Load 4 elements from address 0x100 (assuming VPU_TC_006 was executed previously)
- **Inputs:**
    - `vector_length`: 4
    - `addr`: 32'h100
- **Expected Output:** {AA, BB, CC, DD}
- **Expected Error:** None

### VPU_TC_008: Unsupported Opcode

- **Description:** Tests the VPU's behavior with an unsupported opcode, expecting an error.
- **Operation:** Invalid opcode (4'hF)
- **Inputs:**
    - `opcode`: 4'hF
- **Expected Output:** Undefined (error flag set)
- **Expected Error:** `error` flag set to 1
