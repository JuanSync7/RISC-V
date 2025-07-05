# Test Cases for `writeback_stage_tb.sv`

This document outlines the test scenarios implemented in the `writeback_stage_tb.sv` testbench to verify the functionality of the `writeback_stage` module.

## Test Scenarios

### Test Case 1: Writeback from ALU (WB_SEL_ALU)
- **Input:** `alu_result = 100`, `rd = 5`, `reg_write_en = 1`
- **Description:** Verifies that the writeback stage correctly selects and writes the ALU result to the register file.
- **Expected Behavior:**
    - `wb_rd_addr_o` should be `5`.
    - `wb_write_data_o` should be `100`.
    - `wb_reg_write_en_o` should be `REG_WRITE_EN`.

### Test Case 2: Writeback from Memory (WB_SEL_MEM)
- **Input:** `mem_read_data = 0xABCDEF01`, `rd = 10`, `reg_write_en = 1`
- **Description:** Verifies that the writeback stage correctly selects and writes the memory read data to the register file.
- **Expected Behavior:**
    - `wb_rd_addr_o` should be `10`.
    - `wb_write_data_o` should be `0xABCDEF01`.
    - `wb_reg_write_en_o` should be `REG_WRITE_EN`.

### Test Case 3: Writeback PC+4 (WB_SEL_PC_PLUS_4) for JAL
- **Input:** `pc_plus_4 = 0x80000004`, `rd = 1`, `reg_write_en = 1`
- **Description:** Verifies that the writeback stage correctly selects and writes the PC+4 value (for JAL instruction) to the register file.
- **Expected Behavior:**
    - `wb_rd_addr_o` should be `1`.
    - `wb_write_data_o` should be `0x80000004`.
    - `wb_reg_write_en_o` should be `REG_WRITE_EN`.

### Test Case 4: Writeback from DPU (WB_SEL_DPU)
- **Input:** `dpu_result = 0x12345678`, `rd = 7`, `reg_write_en = 1`
- **Description:** Verifies that the writeback stage correctly selects and writes the DPU result to the register file.
- **Expected Behavior:**
    - `wb_rd_addr_o` should be `7`.
    - `wb_write_data_o` should be `0x12345678`.
    - `wb_reg_write_en_o` should be `REG_WRITE_EN`.

### Test Case 5: No Register Write (REG_WRITE_DIS)
- **Input:** `reg_write_en = 0`
- **Description:** Verifies that no write occurs to the register file when `reg_write_en` is disabled.
- **Expected Behavior:**
    - `wb_reg_write_en_o` should be `REG_WRITE_DIS`.

### Test Case 6: Flush signal active
- **Input:** `flush_i = 1`
- **Description:** Verifies that the writeback stage correctly disables register write when the `flush_i` signal is asserted.
- **Expected Behavior:**
    - `wb_reg_write_en_o` should be `REG_WRITE_DIS`.

### Test Case 7: Stall signal active
- **Input:** `stall_i = 1`
- **Description:** Verifies that the writeback stage correctly disables register write when the `stall_i` signal is asserted.
- **Expected Behavior:**
    - `wb_reg_write_en_o` should be `REG_WRITE_DIS`.
