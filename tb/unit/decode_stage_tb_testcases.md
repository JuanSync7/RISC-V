# Test Cases for `decode_stage_tb.sv`

This document outlines the test scenarios implemented in the `decode_stage_tb.sv` testbench to verify the functionality of the `decode_stage` module.

## Test Scenarios

### Test Case 1: R-type instruction (ADD x1, x2, x3)
- **Instruction:** `ADD x1, x2, x3` (RISC-V instruction: `0x003100B3`)
- **Description:** Verifies correct decoding of a standard R-type arithmetic instruction.
- **Expected Behavior:**
    - `op_code` should be `OP_R_TYPE`.
    - `funct3` should be `3'b000`.
    - `funct7` should be `7'b0000000`.
    - `rd` should be `1`.
    - `rs1` should be `2`.
    - `rs2` should be `3`.
    - Control signals (`alu_op`, `mem_read`, `mem_write`, `branch`, `reg_write`, `mem_to_reg`, `pc_src`) should be set appropriately for an ADD operation.

### Test Case 2: I-type instruction (ADDI x5, x6, 10)
- **Instruction:** `ADDI x5, x6, 10` (RISC-V instruction: `0x00A30293`)
- **Description:** Verifies correct decoding of an I-type immediate instruction.
- **Expected Behavior:**
    - `op_code` should be `OP_I_TYPE`.
    - `funct3` should be `3'b000`.
    - `rd` should be `5`.
    - `rs1` should be `6`.
    - `imm` should be `10`.
    - Control signals should be set appropriately for an ADDI operation.

### Test Case 3: S-type instruction (SW x7, 0(x8))
- **Instruction:** `SW x7, 0(x8)` (RISC-V instruction: `0x00742023`)
- **Description:** Verifies correct decoding of an S-type store instruction.
- **Expected Behavior:**
    - `op_code` should be `OP_S_TYPE`.
    - `funct3` should be `3'b010`.
    - `rs1` should be `8`.
    - `rs2` should be `7`.
    - `imm` should be `0`.
    - Control signals should be set appropriately for a SW operation (e.g., `mem_write` enabled).

### Test Case 4: B-type instruction (BEQ x9, x10, 0x10)
- **Instruction:** `BEQ x9, x10, 0x10` (RISC-V instruction: `0x00A48463`)
- **Description:** Verifies correct decoding of a B-type branch instruction.
- **Expected Behavior:**
    - `op_code` should be `OP_B_TYPE`.
    - `funct3` should be `3'b000`.
    - `rs1` should be `9`.
    - `rs2` should be `10`.
    - `imm` should be `16`.
    - Control signals should be set appropriately for a BEQ operation (e.g., `branch` enabled, `alu_op` for comparison).

### Test Case 5: U-type instruction (LUI x11, 0x12345)
- **Instruction:** `LUI x11, 0x12345` (RISC-V instruction: `0x00012345B7`)
- **Description:** Verifies correct decoding of a U-type instruction.
- **Expected Behavior:**
    - `op_code` should be `OP_U_TYPE`.
    - `rd` should be `11`.
    - `imm` should be `32'h12345000`.
    - Control signals should be set appropriately for an LUI operation.

### Test Case 6: J-type instruction (JAL x12, 0x20)
- **Instruction:** `JAL x12, 0x20` (RISC-V instruction: `0x020006EF`)
- **Description:** Verifies correct decoding of a J-type jump and link instruction.
- **Expected Behavior:**
    - `op_code` should be `OP_J_TYPE`.
    - `rd` should be `12`.
    - `imm` should be `32`.
    - Control signals should be set appropriately for a JAL operation (e.g., `branch` for JAL, `mem_to_reg` for PC+4).

### Test Case 7: DPU FPU instruction (CUSTOM0, FPU_ADD)
- **Instruction:** Example: `CUSTOM0` with `funct3 = FUNCT3_DPU_FPU` (e.g., `0x0000000B` if `FUNCT3_DPU_FPU` is 0 and `rs2, rs1, rd` are 0).
- **Description:** Verifies decoding of a custom instruction intended for the DPU FPU.
- **Expected Behavior:**
    - `op_code` should be `OP_CUSTOM0`.
    - `funct3` should match `FUNCT3_DPU_FPU`.
    - Control signals should indicate a DPU operation (`alu_op = ALU_DPU`, `mem_to_reg = WB_SEL_DPU`).

### Test Case 8: Flush signal active
- **Description:** Verifies that the `decode_stage` correctly flushes its output when the `flush_i` signal is asserted.
- **Expected Behavior:**
    - `id_ex_valid_o` should be `0` (invalidating the pipeline register).

### Test Case 9: Stall signal active
- **Description:** Verifies that the `decode_stage` correctly stalls, preventing new valid output, when the `stall_i` signal is asserted.
- **Expected Behavior:**
    - `id_ex_valid_o` should be `0` (assuming no new instruction is processed and output is held).
