# FPU Testbench Test Cases

This document details the test cases implemented in `fpu_tb.sv` for verifying the functionality of the Floating Point Unit (FPU).

## Testbench Overview

The `fpu_tb.sv` testbench is designed to perform unit-level verification of the `fpu_unit` module. It simulates various floating-point operations, including arithmetic operations (ADD, SUB, MUL, DIV), square root (SQRT), float-to-integer conversion (F2I), and integer-to-float conversion (I2F). It also includes tests for error conditions like division by zero and square root of a negative number.

## Test Scenarios

### FPU_TC_001: FPU_ADD (Positive Numbers)

- **Description:** Verifies the FPU_ADD operation with two positive floating-point numbers.
- **Operation:** 3.0 + 4.0
- **Inputs:**
    - `operand1`: 32'h40400000 (3.0 float)
    - `operand2`: 32'h40800000 (4.0 float)
- **Expected Output:** 32'h40E00000 (7.0 float)
- **Expected Error:** None

### FPU_TC_002: FPU_SUB (Positive Numbers)

- **Description:** Verifies the FPU_SUB operation with two positive floating-point numbers.
- **Operation:** 7.0 - 3.0
- **Inputs:**
    - `operand1`: 32'h40E00000 (7.0 float)
    - `operand2`: 32'h40400000 (3.0 float)
- **Expected Output:** 32'h40800000 (4.0 float)
- **Expected Error:** None

### FPU_TC_003: FPU_MUL (Positive Numbers)

- **Description:** Verifies the FPU_MUL operation with two positive floating-point numbers.
- **Operation:** 2.5 * 2.0
- **Inputs:**
    - `operand1`: 32'h40200000 (2.5 float)
    - `operand2`: 32'h40000000 (2.0 float)
- **Expected Output:** 32'h40A00000 (5.0 float)
- **Expected Error:** None

### FPU_TC_004: FPU_DIV (Positive Numbers)

- **Description:** Verifies the FPU_DIV operation with two positive floating-point numbers.
- **Operation:** 10.0 / 2.0
- **Inputs:**
    - `operand1`: 32'h41200000 (10.0 float)
    - `operand2`: 32'h40000000 (2.0 float)
- **Expected Output:** 32'h40A00000 (5.0 float)
- **Expected Error:** None

### FPU_TC_005: FPU_DIV (Division by Zero)

- **Description:** Verifies the FPU_DIV operation with division by zero, expecting an error.
- **Operation:** 2.0 / 0.0
- **Inputs:**
    - `operand1`: 32'h40000000 (2.0 float)
    - `operand2`: 32'h00000000 (0.0 float)
- **Expected Output:** Undefined (error flag set)
- **Expected Error:** `error` flag set to 1

### FPU_TC_006: FPU_SQRT (Positive Number)

- **Description:** Verifies the FPU_SQRT operation with a positive floating-point number.
- **Operation:** SQRT(25.0)
- **Inputs:**
    - `operand1`: 32'h41C80000 (25.0 float)
- **Expected Output:** 32'h40A00000 (5.0 float)
- **Expected Error:** None

### FPU_TC_007: FPU_SQRT (Negative Number)

- **Description:** Verifies the FPU_SQRT operation with a negative floating-point number, expecting an error.
- **Operation:** SQRT(-4.0)
- **Inputs:**
    - `operand1`: 32'hC0800000 (-4.0 float)
- **Expected Output:** Undefined (error flag set)
- **Expected Error:** `error` flag set to 1

### FPU_TC_008: FPU_F2I (Float to Integer Conversion)

- **Description:** Verifies the FPU_F2I operation, converting a floating-point number to an integer.
- **Operation:** F2I(3.75)
- **Inputs:**
    - `operand1`: 32'h40700000 (3.75 float)
- **Expected Output:** 32'h00000003 (3 integer)
- **Expected Error:** None

### FPU_TC_009: FPU_I2F (Integer to Float Conversion)

- **Description:** Verifies the FPU_I2F operation, converting an integer to a floating-point number.
- **Operation:** I2F(5)
- **Inputs:**
    - `operand1`: 32'h00000005 (5 integer)
- **Expected Output:** 32'h40A00000 (5.0 float)
- **Expected Error:** None

### FPU_TC_010: Unsupported Opcode

- **Description:** Tests the FPU's behavior with an unsupported opcode, expecting an error.
- **Operation:** Invalid opcode (4'hF)
- **Inputs:**
    - `opcode`: 4'hF
- **Expected Output:** Undefined (error flag set)
- **Expected Error:** `error` flag set to 1

### FPU_TC_011: FPU_ADD (Negative Numbers)

- **Description:** Verifies the FPU_ADD operation with a negative and a positive floating-point number.
- **Operation:** -4.0 + 5.0
- **Inputs:**
    - `operand1`: 32'hC0800000 (-4.0 float)
    - `operand2`: 32'h40A00000 (5.0 float)
- **Expected Output:** 32'h3F800000 (1.0 float)
- **Expected Error:** None
