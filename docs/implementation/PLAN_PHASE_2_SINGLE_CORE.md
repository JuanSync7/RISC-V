# Detailed Plan: Phase 2 - Single-Core In-Order Implementation

**Version:** 1.0
**Status:** Not Started

## 1. Objective

This phase focuses on constructing a complete, verifiable, and functional single-core RV32IM processor with a classic 5-stage in-order pipeline. This will serve as the baseline for all future enhancements.

## 2. Task Breakdown

### Task 2.1: Implement Fetch Stage

*   **Status:** `Not Started`
*   **Objective:** Implement the logic to fetch instructions from the instruction memory/cache.
*   **File to be modified:** `rtl/core/fetch_stage.sv`
*   **Inputs:** `clk_i`, `rst_ni`, `pc_in` (from branch/jump logic), `stall_i` (from hazard unit)
*   **Outputs:** `if_id_pipe_o` (to decode stage), `pc_out` (to branch predictor)
*   **Interfaces:** `icache_if.master`
*   **Logic:**
    *   A program counter (PC) register.
    *   Logic to select the next PC based on `stall_i`, branch/jump requests, and sequential fetching.
    *   Logic to drive the `icache_if` with the current PC.
    *   Logic to handle cache stalls (`req_ready` de-assertion).
*   **Verification:**
    *   Test sequential instruction fetching.
    *   Test PC update on branch/jump.
    *   Test stall functionality.

### Task 2.2: Implement Decode Stage

*   **Status:** `Not Started`
*   **Objective:** Implement the instruction decoder and register file read logic.
*   **File to be modified:** `rtl/core/decode_stage.sv`
*   **Inputs:** `if_id_pipe_i` (from fetch stage), `wb_data_i` (from writeback stage), `rd_write_en_i` (from writeback stage)
*   **Outputs:** `id_ex_pipe_o` (to execute stage)
*   **Logic:**
    *   Decode the instruction opcode, funct3, and funct7 fields.
    *   Generate control signals for the subsequent pipeline stages.
    *   Read source registers from the `reg_file`.
    *   Handle immediate value extraction.
*   **Verification:**
    *   Test decoding of all supported RV32I instructions.
    *   Test correct generation of control signals.
    *   Test register file read and forwarding logic.

### Task 2.3: Implement Execute Stage

*   **Status:** `Not Started`
*   **Objective:** Implement the ALU and branch/jump execution logic.
*   **File to be modified:** `rtl/core/execute_stage.sv`
*   **Inputs:** `id_ex_pipe_i` (from decode stage)
*   **Outputs:** `ex_mem_pipe_o` (to memory stage), `branch_target_o` (to fetch stage)
*   **Logic:**
    *   Instantiate the ALU.
    *   Select ALU inputs based on the instruction type.
    *   Calculate branch/jump target addresses.
    *   Evaluate branch conditions.
*   **Verification:**
    *   Test all ALU operations.
    *   Test all branch and jump instructions.

### Task 2.4: Implement Memory Stage

*   **Status:** `Not Started`
*   **Objective:** Implement the logic to access the data memory/cache.
*   **File to be modified:** `rtl/core/mem_stage.sv`
*   **Inputs:** `ex_mem_pipe_i` (from execute stage)
*   **Outputs:** `mem_wb_pipe_o` (to writeback stage)
*   **Interfaces:** `dcache_if.master`
*   **Logic:**
    *   Drive the `dcache_if` for load and store operations.
    *   Handle cache stalls.
*   **Verification:**
    *   Test all load and store instructions (`lb`, `lh`, `lw`, `sb`, `sh`, `sw`).
    *   Test memory alignment.

### Task 2.5: Implement Writeback Stage

*   **Status:** `Not Started`
*   **Objective:** Implement the logic to write results back to the register file.
*   **File to be modified:** `rtl/core/writeback_stage.sv`
*   **Inputs:** `mem_wb_pipe_i` (from memory stage)
*   **Outputs:** `wb_data_o` (to decode stage for forwarding), `rd_write_en_o` (to decode stage)
*   **Logic:**
    *   Select the data to be written back to the register file (from ALU result or memory read).
*   **Verification:**
    *   Test writeback for all instruction types.

### Task 2.6: Implement Hazard Unit

*   **Status:** `Not Started`
*   **Objective:** Implement the hazard detection and pipeline stall logic.
*   **File to be modified:** `rtl/core/hazard_unit.sv`
*   **Inputs:** Decoded instruction information from the pipeline stages.
*   **Outputs:** Stall signals for the pipeline stages.
*   **Logic:**
    *   Detect data hazards (RAW).
    *   Detect control hazards.
    *   Generate stall signals to freeze the appropriate pipeline stages.
*   **Verification:**
    *   Test all hazard scenarios with a variety of instruction sequences.

### Task 2.7: Full Single-Core Integration and Verification

*   **Status:** `Not Started`
*   **Objective:** Integrate all single-core components and verify the complete processor.
*   **Files to be modified:** `rtl/core/core_subsystem.sv`
*   **Verification:**
    *   Run the `riscv-tests` suite.
    *   Achieve >90% code and functional coverage.
