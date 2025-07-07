# Register Renaming Architecture

## 1. Overview

The `register_renaming` module is a critical component in the out-of-order execution pipeline of the RISC-V RV32IM core. Its primary function is to eliminate Write-After-Read (WAR) and Write-After-Write (WAW) hazards by mapping architectural registers to unique physical tags (ROB tags). This mechanism enables instructions to execute as soon as their operands are available, rather than waiting for previous instructions to write their results to the architectural register file, thereby improving pipeline utilization and overall performance.

The module provides either the physical tag of an operand (if it's still speculative and not yet computed) or the actual data value (if it's already available in the Physical Register File). It continuously snoops the Common Data Bus (CDB) to update its internal Physical Register File with computed results.

## 2. Features

*   **Hazard Elimination:** Effectively removes WAR and WAW hazards, facilitating out-of-order execution.
*   **Operand Forwarding:** Provides immediate operand values if they are ready, bypassing potential stalls.
*   **Architectural to Physical Mapping:** Maintains a dynamic mapping between architectural registers and their corresponding Reorder Buffer (ROB) tags.
*   **Speculative State Management:** Manages speculative register values in the Physical Register File (PRF).

## 3. Internal Blocks

The `register_renaming` module comprises the following key internal blocks:

### 3.1. Map Table (`map_table_r`, `map_table_ns`)

*   **Description:** This block stores the current mapping from architectural registers to their corresponding physical (ROB) tags. Each entry in the map table indicates whether an architectural register has a pending write (i.e., is "busy") and, if so, which ROB tag holds its speculative value.
*   **Structure:** An array of `map_table_entry_t` structs, indexed by architectural register address.
    ```systemverilog
    typedef struct packed {
        logic [ROB_ADDR_WIDTH-1:0] tag; // ROB tag
        logic busy; // Is there an instruction in flight writing to this reg?
    } map_table_entry_t;
    map_table_entry_t [ARCH_REG_COUNT-1:0] map_table_r, map_table_ns;
    ```
*   **Functionality:**
    *   **Allocation:** When a new instruction is dispatched that writes to a destination register, a new entry is allocated in the map table, linking the architectural register to the new ROB tag assigned to that instruction.
    *   **Deallocation/Invalidation:** When an instruction commits, if the map table entry for its destination register still points to its ROB tag, the `busy` bit for that entry is cleared, indicating that the architectural register now holds the committed value.

### 3.2. Physical Register File (PRF) (`prf_r`, `prf_ns`, `prf_ready_r`, `prf_ready_ns`)

*   **Description:** The PRF stores the speculative values of registers, indexed by their ROB tags. It acts as a temporary storage for results of in-flight instructions before they are committed to the architectural register file.
*   **Structure:**
    ```systemverilog
    logic [DATA_WIDTH-1:0] [ROB_SIZE-1:0] prf_r, prf_ns; // Stores the actual data values
    logic [ROB_SIZE-1:0]                  prf_ready_r, prf_ready_ns; // Bitmask indicating if a PRF entry is ready (written by CDB)
    ```
*   **Functionality:**
    *   **Update:** The PRF is updated by snooping the Common Data Bus (CDB). When a result is broadcast on the CDB, the corresponding PRF entry (identified by the ROB tag) is updated with the result data, and its `ready` bit is set.
    *   **Read:** When an operand is requested, the PRF is checked. If the corresponding PRF entry is `ready`, its value is forwarded directly.

### 3.3. Operand Fetch Logic

*   **Description:** This combinational logic determines whether source operands (rs1, rs2) are available as immediate data or if they require a ROB tag to be resolved later.
*   **Functionality:**
    *   For each source operand (rs1, rs2):
        1.  It queries the `map_table_r` using the architectural register address.
        2.  If the architectural register is mapped (`busy` bit is set) and not `x0` (zero register), it checks the `prf_ready_r` for the corresponding ROB tag.
        3.  If the PRF entry is `ready`, the actual data value from `prf_r` is provided (`dispatch_v_rsX_o`).
        4.  If the PRF entry is not `ready`, the ROB tag is provided (`dispatch_q_rsX_o`), and `dispatch_q_rsX_valid_o` is asserted, indicating that the operand is waiting for a future result.

## 4. Interfaces

| Port Name                 | Direction | Description                                                               | Clock Domain |
| :------------------------ | :-------- | :------------------------------------------------------------------------ | :----------- |
| `clk_i`                   | Input     | System clock                                                              | `clk_i`      |
| `rst_ni`                  | Input     | Asynchronous active-low reset                                             | `clk_i` (async assert) |
| `flush_i`                 | Input     | High to flush all speculative state (map table and PRF ready bits).       | `clk_i`      |
| `decode_valid_i`          | Input     | Valid instruction from decode stage.                                      | `clk_i`      |
| `decode_rs1_addr_i`       | Input     | Address of source register 1.                                             | `clk_i`      |
| `decode_rs2_addr_i`       | Input     | Address of source register 2.                                             | `clk_i`      |
| `decode_rd_addr_i`        | Input     | Address of destination register.                                          | `clk_i`      |
| `decode_rd_write_en_i`    | Input     | Indicates if the instruction writes to a destination register.            | `clk_i`      |
| `dispatch_valid_o`        | Output    | Renamed instruction is valid for dispatch to the Reservation Station.     | `clk_i`      |
| `dispatch_v_rs1_o`        | Output    | Value of operand 1 if ready.                                              | `clk_i`      |
| `dispatch_q_rs1_valid_o`  | Output    | Is operand 1 not ready (i.e., waiting for a tag)?                         | `clk_i`      |
| `dispatch_q_rs1_o`        | Output    | ROB tag for operand 1.                                                    | `clk_i`      |
| `dispatch_v_rs2_o`        | Output    | Value of operand 2 if ready.                                              | `clk_i`      |
| `dispatch_q_rs2_valid_o`  | Output    | Is operand 2 not ready?                                                   | `clk_i`      |
| `dispatch_q_rs2_o`        | Output    | ROB tag for operand 2.                                                    | `clk_i`      |
| `rob_new_tag_i`           | Input     | The new ROB tag allocated for this instruction.                           | `clk_i`      |
| `rob_ready_i`             | Input     | Is the ROB ready to accept a new entry?                                   | `clk_i`      |
| `result_valid_i`          | Input     | A valid result is on the Common Data Bus (CDB).                           | `clk_i`      |
| `result_rob_tag_i`        | Input     | The ROB tag of the result on the CDB.                                     | `clk_i`      |
| `result_data_i`           | Input     | The result value on the CDB.                                              | `clk_i`      |
| `commit_valid_i`          | Input     | An instruction is committing.                                             | `clk_i`      |
| `commit_rd_addr_i`        | Input     | The destination register of the committing instruction.                   | `clk_i`      |
| `commit_rob_tag_i`        | Input     | The ROB tag of the committing instruction.                                | `clk_i`      |

## 5. Parameters

| Parameter Name   | Type    | Description                                    | Default Value |
| :--------------- | :------ | :--------------------------------------------- | :------------ |
| `DATA_WIDTH`     | `integer` | Width of the data path and registers.          | `XLEN`        |
| `ARCH_REG_COUNT` | `integer` | Number of architectural registers.             | `REG_COUNT`   |
| `ROB_SIZE`       | `integer` | Number of entries in the Reorder Buffer (ROB). | `DEFAULT_ROB_SIZE` |
| `REG_ADDR_WIDTH` | `integer` | Width of the architectural register file address. | `REG_ADDR_WIDTH` |

## 6. State Machine (Implicit)

The `register_renaming` module operates primarily through combinational logic and sequential updates to its internal state (map table and PRF). While there isn't an explicit FSM, the state transitions are governed by the following logic:

*   **Reset/Flush:** On reset (`rst_ni` de-asserted) or flush (`flush_i` asserted), the `map_table_r` and `prf_ready_r` are cleared, effectively invalidating all speculative state.
*   **Dispatch:** When a new instruction is dispatched (`dispatch_valid_o` is high), and it writes to a destination register (`decode_rd_write_en_i` and `decode_rd_addr_i != 0`), the `map_table_ns` is updated to link the `decode_rd_addr_i` to the `rob_new_tag_i`. The `prf_ready_ns` for this new tag is set to `0` (not ready).
*   **Result Broadcast (CDB Snooping):** When a valid result appears on the CDB (`result_valid_i`), the `prf_ns` is updated with `result_data_i` at the `result_rob_tag_i` index, and `prf_ready_ns` for that tag is set to `1` (ready).
*   **Commit:** When an instruction commits (`commit_valid_i`), if the `map_table_r` entry for `commit_rd_addr_i` still points to `commit_rob_tag_i`, the `busy` bit in `map_table_ns` for that architectural register is cleared. This signifies that the architectural register now holds the committed value, and the speculative mapping is no longer needed.

**Priority:** The dispatch logic for updating the map table has higher priority than the commit logic for clearing map table entries, ensuring correct handling of back-to-back dependencies where an instruction might be dispatched and then immediately committed.

## 7. Dependencies

*   `riscv_config_pkg`: Used for `XLEN`, `REG_COUNT`, `DEFAULT_ROB_SIZE`, and `REG_ADDR_WIDTH` parameters.

## 8. Performance, Area, and Verification

*   **Performance:**
    *   **Critical Path:** Likely in the map table lookup and operand fetch logic, as these are combinational paths directly impacting dispatch latency.
    *   **Max Frequency:** TBD
*   **Area:** TBD (highly dependent on `ROB_SIZE` and `ARCH_REG_COUNT`).
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
| 1.0.0   | 2025-06-28 | DesignAI   | Initial fleshed-out implementation with PRF and bypass logic. |
| 0.1.0   | 2025-06-27 | DesignAI   | Initial skeleton release.                               |
