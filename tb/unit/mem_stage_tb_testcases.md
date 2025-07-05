# Test Cases for `mem_stage_tb.sv`

This document outlines the test scenarios implemented in the `mem_stage_tb.sv` testbench to verify the functionality of the `mem_stage` module.

## Test Scenarios

### Test Case 1: Load Word (LW) - Successful Read
- **Instruction:** `LW`
- **Input:** `alu_result = 0x1000` (memory address), `mem_read_data_i = 0xDEADBEEF`
- **Description:** Verifies a successful word load operation from data memory.
- **Expected Behavior:**
    - A memory read request is issued to address `0x1000` with type `MEM_WORD`.
    - The `mem_read_data` in `mem_wb_reg_o` should be `0xDEADBEEF`.
    - The `rd` and `mem_to_reg` signals should be propagated correctly.

### Test Case 2: Store Word (SW) - Successful Write
- **Instruction:** `SW`
- **Input:** `alu_result = 0x2000` (memory address), `mem_write_data = 0xCAFEBABE`
- **Description:** Verifies a successful word store operation to data memory.
- **Expected Behavior:**
    - A memory write request is issued to address `0x2000` with data `0xCAFEBABE` and type `MEM_WORD`.
    - The pipeline should advance, and `reg_write` should be disabled.

### Test Case 3: Load Byte Unsigned (LBU) - Successful Read
- **Instruction:** `LBU`
- **Input:** `alu_result = 0x3001` (memory address), `mem_read_data_i = 0x12345678`
- **Description:** Verifies a successful unsigned byte load operation from data memory, extracting the correct byte.
- **Expected Behavior:**
    - A memory read request is issued to address `0x3001` with type `MEM_BYTE_U`.
    - The `mem_read_data` in `mem_wb_reg_o` should be `0x00000056` (assuming little-endian byte extraction from `0x12345678`).

### Test Case 4: Memory Read Error (Load Word)
- **Instruction:** `LW`
- **Input:** `alu_result = 0x4000` (memory address), `mem_resp_error_i = 1`
- **Description:** Verifies that a load access fault exception is generated when the data memory signals an error during a read.
- **Expected Behavior:**
    - `exception_en` should be `1`.
    - `exception_code` should be `EXC_LOAD_ACCESS_FAULT`.

### Test Case 5: Memory Write Error (Store Word)
- **Instruction:** `SW`
- **Input:** `alu_result = 0x5000` (memory address), `mem_resp_error_i = 1`
- **Description:** Verifies that a store access fault exception is generated when the data memory signals an error during a write.
- **Expected Behavior:**
    - `exception_en` should be `1`.
    - `exception_code` should be `EXC_STORE_ACCESS_FAULT`.

### Test Case 6: Flush signal active
- **Description:** Verifies that the `mem_stage` correctly flushes its output and propagates the flush signal when `flush_i` is asserted.
- **Expected Behavior:**
    - `mem_wb_valid_o` should be `0`.
    - `mem_flush_o` should be `1`.

### Test Case 7: Stall signal active
- **Description:** Verifies that the `mem_stage` correctly stalls, preventing new valid output and propagating the stall signal, when `stall_i` is asserted.
- **Expected Behavior:**
    - `mem_wb_valid_o` should be `0`.
    - `mem_stall_o` should be `1`.
