# Reservation Station (RS) Architecture

## 1. Overview

The `reservation_station` module is a key component in the out-of-order execution pipeline of the RISC-V RV32IM core. It serves as a temporary buffer for instructions that have been dispatched but are awaiting their source operands to become available. The RS continuously monitors the Common Data Bus (CDB) for results from completed functional units and, once all operands for an instruction are ready, it issues the instruction to an available functional unit for execution.

This module enables instructions to execute out of program order, maximizing functional unit utilization and overall pipeline throughput by decoupling instruction dispatch from execution.

## 2. Features

*   **Unified Buffer:** A single, unified reservation station handles all types of instructions.
*   **Operand Waiting:** Holds instructions until all their source operands are available.
*   **Result Forwarding:** Implements full result forwarding logic, allowing instructions to receive operand values directly from the CDB as soon as they are computed, bypassing the register file.
*   **Instruction Issuing:** Selects and issues ready instructions to functional units.
*   **Configurable Size:** The number of entries in the reservation station is configurable, allowing for trade-offs between performance and hardware cost.

## 3. Internal Blocks

The `reservation_station` module comprises the following key internal blocks:

### 3.1. RS Entries (`rs_r`, `rs_ns`)

*   **Description:** This is the main storage array for instructions awaiting execution. Each entry (`rs_entry_t`) holds the instruction's opcode, its source operand values (if ready), flags indicating if operands are still waiting for results, and the ROB tag for its own result.
*   **Structure:** An array of `rs_entry_t` structs.
    ```systemverilog
    typedef struct packed {
        logic                       busy;          // Indicates if the entry is occupied
        logic [31:0]                opcode;        // Instruction opcode/data
        logic [DATA_WIDTH-1:0]      v_rs1;         // Value of source operand 1
        logic                       q_rs1_valid;   // Flag: 1 if rs1 is waiting for a result (tag is valid)
        logic [ROB_ADDR_WIDTH-1:0]  q_rs1;         // ROB tag for rs1 if waiting
        logic [DATA_WIDTH-1:0]      v_rs2;         // Value of source operand 2
        logic                       q_rs2_valid;   // Flag: 1 if rs2 is waiting for a result (tag is valid)
        logic [ROB_ADDR_WIDTH-1:0]  q_rs2;         // ROB tag for rs2 if waiting
        logic [ROB_ADDR_WIDTH-1:0]  rob_tag;       // ROB tag for this instruction's result
    } rs_entry_t;
    rs_entry_t [RS_SIZE-1:0] rs_r, rs_ns;
    ```
*   **Functionality:**
    *   **Allocation:** When an instruction is dispatched, a free entry is found (or allocated using `alloc_ptr_r`), and the instruction's details are stored. If an operand is not yet ready, its `q_rsX_valid` flag is set, and its `q_rsX` field stores the ROB tag it is waiting for.
    *   **Update:** The `ResultWatcher` logic updates `v_rsX` and clears `q_rsX_valid` when a matching result appears on the CDB.

### 3.2. Dispatch Logic

*   **Description:** Manages the allocation of new entries in the RS for instructions coming from the Rename stage.
*   **Functionality:**
    *   Checks `dispatch_ready_o` to ensure there is space in the RS.
    *   When `dispatch_valid_i` is asserted and space is available, the instruction's details (opcode, operand values/tags, and its own ROB tag) are written into the entry pointed to by `alloc_ptr_r`.
    *   `alloc_ptr_r` is incremented to point to the next potential free slot.
    *   `entry_count_r` is incremented.

### 3.3. Result Watcher (Result Forwarding Logic)

*   **Description:** This logic continuously monitors the `result_valid_i`, `result_rob_tag_i`, and `result_data_i` signals from the CDB. It updates any waiting RS entries whose operands match the broadcasted ROB tag.
*   **Functionality:**
    *   When a valid result is broadcast on the CDB, the `ResultWatcher` iterates through all RS entries.
    *   If an entry's `q_rs1` or `q_rs2` matches `result_rob_tag_i`, the corresponding `v_rs1` or `v_rs2` is updated with `result_data_i`, and the `q_rs1_valid` or `q_rs2_valid` flag is cleared.

### 3.4. Issue Selector (`issue_idx_c`)

*   **Description:** This combinational logic identifies an instruction within the RS that is ready to be issued to a functional unit. A simple priority encoder is used to select the first ready instruction.
*   **Functionality:**
    *   Scans all RS entries.
    *   An instruction is considered "ready" if its `busy` flag is set and both `q_rs1_valid` and `q_rs2_valid` are `0` (meaning all operands are available).
    *   The index of the first ready instruction found is assigned to `issue_idx_c`.

## 4. Interfaces

| Port Name                 | Direction | Description                                                               | Clock Domain |
| :------------------------ | :-------- | :------------------------------------------------------------------------ | :----------- |
| `clk_i`                   | Input     | System clock                                                              | `clk_i`      |
| `rst_ni`                  | Input     | Asynchronous active-low reset                                             | `clk_i` (async assert) |
| `flush_i`                 | Input     | High to flush all entries in the RS (on exceptions/mispredictions).       | `clk_i`      |
| `dispatch_valid_i`        | Input     | The instruction dispatched from rename is valid.                          | `clk_i`      |
| `dispatch_ready_o`        | Output    | RS is ready to accept a new instruction (not full).                       | `clk_i`      |
| `dispatch_opcode_i`       | Input     | The full instruction opcode/data.                                         | `clk_i`      |
| `dispatch_v_rs1_i`        | Input     | Value of operand 1 if available (from Register Renaming).                 | `clk_i`      |
| `dispatch_q_rs1_valid_i`  | Input     | Flag indicating if operand 1 is waiting for a result from the ROB.        | `clk_i`      |
| `dispatch_q_rs1_i`        | Input     | ROB tag for operand 1 if waiting.                                         | `clk_i`      |
| `dispatch_v_rs2_i`        | Input     | Value of operand 2 if available (from Register Renaming).                 | `clk_i`      |
| `dispatch_q_rs2_valid_i`  | Input     | Flag indicating if operand 2 is waiting for a result from the ROB.        | `clk_i`      |
| `dispatch_q_rs2_i`        | Input     | ROB tag for operand 2 if waiting.                                         | `clk_i`      |
| `dispatch_rob_tag_i`      | Input     | ROB tag for this new instruction's result.                                | `clk_i`      |
| `result_valid_i`          | Input     | A valid result is being broadcast on the Common Data Bus (CDB).           | `clk_i`      |
| `result_rob_tag_i`        | Input     | The ROB tag of the broadcasted result.                                    | `clk_i`      |
| `result_data_i`           | Input     | The data value of the broadcasted result.                                 | `clk_i`      |
| `issue_valid_o`           | Output    | A valid instruction is ready to be issued to a functional unit.           | `clk_i`      |
| `issue_ready_i`           | Input     | The functional unit is ready to accept an instruction.                    | `clk_i`      |
| `issue_opcode_o`          | Output    | Opcode of the issued instruction.                                         | `clk_i`      |
| `issue_v_rs1_o`           | Output    | Value of operand 1 for the issued instruction.                            | `clk_i`      |
| `issue_v_rs2_o`           | Output    | Value of operand 2 for the issued instruction.                            | `clk_i`      |
| `issue_rob_tag_o`         | Output    | ROB tag of the issued instruction.                                        | `clk_i`      |

## 5. Parameters

| Parameter Name   | Type    | Description                                    | Default Value |
| :--------------- | :------ | :--------------------------------------------- | :------------ |
| `DATA_WIDTH`     | `integer` | Width of the data path and instruction operands. | `XLEN`        |
| `RS_SIZE`        | `integer` | Number of entries in the reservation station. Should be a power of 2. | `DEFAULT_RS_SIZE` |
| `ROB_ADDR_WIDTH` | `integer` | Width of the Re-Order Buffer (ROB) tag. Must match the ROB's address width. | `$clog2(DEFAULT_ROB_SIZE)` |

## 6. State Machine (Implicit)

The `reservation_station` module's behavior is governed by its internal state (RS entries, `alloc_ptr_r`, `entry_count_r`) and the interactions between dispatch, result forwarding, and issue logic.

*   **Reset/Flush:** On reset (`rst_ni` de-asserted) or flush (`flush_i` asserted), all RS entries are marked as not busy, `alloc_ptr_r` and `entry_count_r` are reset to `0`, effectively clearing the RS.

*   **Dispatch:**
    *   When `dispatch_valid_i` is asserted and `dispatch_ready_o` is high, a new instruction is written into the RS entry pointed to by `alloc_ptr_r`.
    *   The `busy` flag for that entry is set to `1`.
    *   `alloc_ptr_ns` is incremented, and `entry_count_ns` is incremented (unless a simultaneous issue frees up the same slot).

*   **Result Forwarding:**
    *   When `result_valid_i` is asserted, the `ResultWatcher` logic updates the `v_rsX` and `q_rsX_valid` fields of any RS entries whose `q_rsX` matches `result_rob_tag_i`.

*   **Issue:**
    *   The `IssueSelector` continuously identifies the first ready instruction.
    *   If `issue_valid_o` is high and `issue_ready_i` is asserted, the selected instruction's `busy` flag is cleared, and `entry_count_ns` is decremented.

*   **Simultaneous Dispatch and Issue:** The logic handles cases where an instruction is issued from an entry, and a new instruction is dispatched into the same entry in the same clock cycle. The `entry_count_ns` is carefully managed to reflect the net change.

## 7. Dependencies

*   `riscv_config_pkg`: Used for `XLEN`, `DEFAULT_RS_SIZE`, and `DEFAULT_ROB_SIZE` parameters.

## 8. Performance, Area, and Verification

*   **Performance:**
    *   **Critical Path:** Likely in the issue selection (priority encoder) or result forwarding logic, as these involve iterating through RS entries.
    *   **Max Frequency:** TBD
*   **Area:** TBD (highly dependent on `RS_SIZE` and the width of stored data).
*   **Verification Coverage:**
    *   Code Coverage: N/A
    *   Functional Coverage: N/A
    *   Branch Coverage: N/A

## 9. Synthesis

*   **Target Technology:** ASIC/FPGA
*   **Synthesis Tool:** N/A
*   **Clock Domains:** 1 (`clk_i`)
*   **Constraints File:** N/A

## 10. Testing

*   **Testbench:** TBD
*   **Test Vectors:** N/A

## 11. Revision History

| Version | Date       | Author     | Description                                             |
| :------ | :--------- | :--------- | :------------------------------------------------------ |
| 1.0.0   | 2025-07-06 | DesignAI   | Initial comprehensive documentation.                    |
| 1.0.0   | 2025-06-28 | DesignAI   | Initial fleshed-out implementation with robust entry management. |
| 0.1.0   | 2025-06-27 | DesignAI   | Initial skeleton release.                               |
