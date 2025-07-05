# Test Cases for `execute_stage_tb.sv`

This document outlines the test scenarios implemented in the `execute_stage_tb.sv` testbench to verify the functionality of the `execute_stage` module.

## Test Scenarios

### Test Case 1: R-type instruction (ADD x1, x2, x3) - No bypass
- **Instruction:** `ADD x1, x2, x3`
- **Input:** `x2 = 10`, `x3 = 20`
- **Description:** Verifies correct execution of a standard R-type arithmetic instruction without data bypass.
- **Expected Behavior:**
    - `alu_result` should be `30`.
    - `rd` should be `1`.
    - `reg_write` should be enabled.

### Test Case 2: I-type instruction (ADDI x5, x6, 10) - No bypass
- **Instruction:** `ADDI x5, x6, 10`
- **Input:** `x6 = 50`
- **Description:** Verifies correct execution of an I-type immediate instruction without data bypass.
- **Expected Behavior:**
    - `alu_result` should be `60`.
    - `rd` should be `5`.
    - `reg_write` should be enabled.

### Test Case 3: S-type instruction (SW x7, 0(x8)) - No bypass
- **Instruction:** `SW x7, 0(x8)`
- **Input:** `x7 = 100`, `x8 = 0x1000`
- **Description:** Verifies correct execution of an S-type store instruction, calculating the memory address and providing data to be written.
- **Expected Behavior:**
    - `alu_result` (memory address) should be `0x1000`.
    - `mem_write_data` should be `100`.
    - `mem_write` should be enabled for word access.

### Test Case 4: B-type instruction (BEQ x9, x10, 0x10) - Branch Taken
- **Instruction:** `BEQ x9, x10, 0x10`
- **Input:** `x9 = 5`, `x10 = 5`
- **Description:** Verifies correct execution of a B-type branch instruction where the branch condition is met.
- **Expected Behavior:**
    - `branch_taken` should be `1`.
    - `branch_target` should be `pc + 16`.

### Test Case 5: DPU FPU instruction (FPU_ADD) - ENABLE_FPU = 1
- **Instruction:** `CUSTOM0` with `funct3 = FUNCT3_DPU_FPU` (e.g., FPU_ADD)
- **Input:** `op1 = 1.5` (as bit pattern `32'h3fc00000`), `op2 = 2.5` (as bit pattern `32'h40200000`)
- **Description:** Verifies that the execute stage correctly handles a DPU FPU instruction, routing it to the DPU and propagating relevant control signals. (Note: Actual FPU calculation is done in `fpu_unit.sv`, this test focuses on the execute stage's routing and control).
- **Expected Behavior:**
    - `mem_to_reg` should be `WB_SEL_DPU`.
    - `reg_write` should be enabled.

### Test Case 6: Flush signal active
- **Description:** Verifies that the `execute_stage` correctly flushes its output and propagates the flush signal when `flush_i` is asserted.
- **Expected Behavior:**
    - `ex_mem_valid_o` should be `0`.
    - `ex_flush_o` should be `1`.

### Test Case 7: Stall signal active
- **Description:** Verifies that the `execute_stage` correctly stalls, preventing new valid output and propagating the stall signal, when `stall_i` is asserted.
- **Expected Behavior:**
    - `ex_mem_valid_o` should be `0`.
    - `ex_stall_o` should be `1`.

### Test Case 8: Data Bypass from Memory Stage
- **Instruction:** `ADD x1, x2, x3`
- **Input:** `x2 = 10`, `x3` is bypassed from Memory stage with value `30`.
- **Description:** Verifies that the execute stage correctly bypasses data from the Memory stage for dependent instructions.
- **Expected Behavior:**
    - `alu_result` should be `40`.
    - `rd` should be `1`.
    - `reg_write` should be enabled.

### Test Case 9: Data Bypass from Writeback Stage
- **Instruction:** `ADD x1, x2, x3`
- **Input:** `x2 = 10`, `x3` is bypassed from Writeback stage with value `30`.
- **Description:** Verifies that the execute stage correctly bypasses data from the Writeback stage for dependent instructions.
- **Expected Behavior:**
    - `alu_result` should be `40`.
    - `rd` should be `1`.
    - `reg_write` should be enabled.

### Test Case 10: Illegal Instruction Exception
- **Instruction:** An illegal instruction (e.g., `0xFFFFFFFF`)
- **Description:** Verifies that the execute stage correctly generates an illegal instruction exception.
- **Expected Behavior:**
    - `exception_en` should be `1`.
    - `exception_code` should be `EXC_ILLEGAL_INSTR`.
