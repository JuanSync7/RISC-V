# Reorder Buffer (ROB) Architecture

## 1. Overview

The `reorder_buffer` module is a fundamental component of the out-of-order execution engine in the RISC-V RV32IM core. Its primary role is to track all in-flight instructions, allowing them to execute out of program order while ensuring they commit (retire) in strict program order. This in-order retirement capability is crucial for maintaining precise exception handling and enabling correct state recovery in the event of mispredictions or exceptions.

The ROB acts as a temporary storage for instruction results and state until they are ready to be written to the architectural register file or memory. It manages a circular buffer of entries, each representing an instruction, and orchestrates their dispatch, execution result update, and eventual commitment.

## 2. Features

*   **In-Order Retirement:** Guarantees that instructions commit in their original program order, regardless of their execution order.
*   **Precise Exception Handling:** Enables the processor to accurately identify the instruction that caused an exception and recover the architectural state to that point.
*   **Misprediction Recovery:** Facilitates flushing of speculative state upon branch mispredictions, ensuring correct program flow.
*   **Result Management:** Stores execution results and exception information for in-flight instructions.
*   **Circular Buffer:** Efficiently manages a fixed number of in-flight instructions using head and tail pointers.

## 3. Internal Blocks

The `reorder_buffer` module comprises the following key internal blocks:

### 3.1. ROB Entries (`rob_r`, `rob_ns`)

*   **Description:** This is the core storage of the ROB, implemented as a circular buffer. Each entry (`rob_entry_t`) holds the state and results for a single in-flight instruction.
*   **Structure:** An array of `rob_entry_t` structs, indexed by the ROB tag.
    ```systemverilog
    typedef struct packed {
        logic [PC_WIDTH-1:0]       pc;         // Program Counter of the instruction
        logic [REG_ADDR_WIDTH-1:0] rd_addr;    // Destination register address
        logic [DATA_WIDTH-1:0]     result;     // Execution result
        exception_info_t           exception;  // Exception details (valid and cause)
        logic                      is_ready;   // Flag indicating if execution is complete
    } rob_entry_t;
    rob_entry_t [ROB_SIZE-1:0] rob_r, rob_ns;
    ```
*   **Functionality:**
    *   **Allocation:** When an instruction is dispatched, a new entry is allocated at the `tail_ptr` and initialized with the instruction's PC, destination register, and marked as not ready.
    *   **Update:** When an instruction completes execution, its result and any exception information are written back to its corresponding ROB entry (identified by its ROB tag), and the `is_ready` flag is set.

### 3.2. Pointer Logic (`head_ptr_r`, `tail_ptr_r`, `entry_count_r`)

*   **Description:** This logic manages the `head` and `tail` pointers of the circular buffer, along with a counter for the number of valid entries. These pointers dictate where new instructions are added and which instruction is next to commit.
*   **Functionality:**
    *   **`head_ptr`:** Points to the oldest instruction in the ROB, which is the next candidate for commitment.
    *   **`tail_ptr`:** Points to the next available empty slot where a newly dispatched instruction will be placed.
    *   **`entry_count`:** Tracks the number of active instructions in the ROB. Used to determine if the ROB is full or empty.
    *   **Increment/Decrement:** Pointers and count are updated on dispatch and commit operations, wrapping around the `ROB_SIZE` for circular buffer behavior.

### 3.3. Commit Logic

*   **Description:** This logic determines when the instruction at the head of the ROB is ready to commit and orchestrates its retirement.
*   **Functionality:**
    *   An instruction at the `head_ptr` is eligible for commitment if its `is_ready` flag is set (meaning it has completed execution) and the `commit_ready_i` signal is asserted (meaning the architectural state is ready to accept the update).
    *   Upon commitment, the instruction's result is provided to the writeback stage, and the `head_ptr` is advanced.
    *   If the committing instruction has an exception, the exception details are propagated.

## 4. Interfaces

| Port Name                 | Direction | Description                                                               | Clock Domain |
| :------------------------ | :-------- | :------------------------------------------------------------------------ | :----------- |
| `clk_i`                   | Input     | System clock                                                              | `clk_i`      |
| `rst_ni`                  | Input     | Asynchronous active-low reset                                             | `clk_i` (async assert) |
| `flush_i`                 | Input     | High to flush all entries in the ROB (on exceptions/mispredictions).      | `clk_i`      |
| `dispatch_valid_i`        | Input     | A new instruction is being dispatched from the Decode/Rename stage.       | `clk_i`      |
| `dispatch_ready_o`        | Output    | ROB is ready to accept a new instruction (not full).                      | `clk_i`      |
| `dispatch_pc_i`           | Input     | Program Counter of the dispatched instruction.                            | `clk_i`      |
| `dispatch_rd_addr_i`      | Input     | Destination register address of the dispatched instruction.               | `clk_i`      |
| `dispatch_rob_tag_o`      | Output    | The unique ROB tag assigned to this new instruction.                      | `clk_i`      |
| `execute_valid_i`         | Input     | A valid result is on the Common Data Bus (CDB) from a functional unit.    | `clk_i`      |
| `execute_rob_tag_i`       | Input     | The ROB tag of the instruction that finished execution.                   | `clk_i`      |
| `execute_result_i`        | Input     | The result data from the functional unit.                                 | `clk_i`      |
| `execute_exception_valid_i` | Input     | Indicates if the instruction resulted in an exception.                    | `clk_i`      |
| `execute_exception_cause_i` | Input     | The cause of the exception.                                               | `clk_i`      |
| `commit_valid_o`          | Output    | The instruction at the head of the ROB is ready to commit.                | `clk_i`      |
| `commit_ready_i`          | Input     | The architectural state (e.g., architectural register file) is ready to be updated. | `clk_i`      |
| `commit_pc_o`             | Output    | PC of the committing instruction.                                         | `clk_i`      |
| `commit_rd_addr_o`        | Output    | Destination register of the committing instruction.                       | `clk_i`      |
| `commit_result_o`         | Output    | Result value to write to the register file.                               | `clk_i`      |
| `commit_exception_valid_o`| Output    | Indicates if the committing instruction has an exception.                 | `clk_i`      |
| `commit_exception_cause_o`| Output    | The cause of the exception for the committing instruction.                | `clk_i`      |

## 5. Parameters

| Parameter Name   | Type    | Description                                    | Default Value |
| :--------------- | :------ | :--------------------------------------------- | :------------ |
| `DATA_WIDTH`     | `integer` | Width of the data path and result values.      | `XLEN`        |
| `ROB_SIZE`       | `integer` | Number of entries in the ROB. Must be a power of 2. | `DEFAULT_ROB_SIZE` |
| `PC_WIDTH`       | `integer` | Width of the program counter.                  | `ADDR_WIDTH`  |
| `REG_ADDR_WIDTH` | `integer` | Width of the architectural register file address. | `REG_ADDR_WIDTH` |

## 6. State Machine (Implicit)

The `reorder_buffer` module operates as a circular buffer with implicit state transitions driven by dispatch, execution completion, and commit events.

*   **Reset/Flush:** On reset (`rst_ni` de-asserted) or flush (`flush_i` asserted), the `head_ptr_r`, `tail_ptr_r`, and `entry_count_r` are all reset to `0`, effectively emptying the ROB and clearing all in-flight state.

*   **Dispatch:**
    *   When `dispatch_valid_i` is asserted and `dispatch_ready_o` is high (ROB is not full), a new entry is allocated at `tail_ptr_r`.
    *   The `pc`, `rd_addr` are stored, and `is_ready` is set to `0`. Exception info is cleared.
    *   `tail_ptr_ns` is incremented (modulo `ROB_SIZE`), and `entry_count_ns` is incremented.

*   **Execution Result Update:**
    *   When `execute_valid_i` is asserted, the `rob_r` entry corresponding to `execute_rob_tag_i` is updated.
    *   `result` and `exception` fields are written, and `is_ready` is set to `1`.

*   **Commit:**
    *   When `commit_valid_o` is high (instruction at head is ready) and `commit_ready_i` is asserted, the instruction at `head_ptr_r` is retired.
    *   `head_ptr_ns` is incremented (modulo `ROB_SIZE`), and `entry_count_ns` is decremented.

*   **Entry Count Logic:**
    *   `entry_count_ns` is incremented if only a dispatch occurs.
    *   `entry_count_ns` is decremented if only a commit occurs.
    *   `entry_count_ns` remains unchanged if both a dispatch and a commit occur simultaneously (assuming `ROB_SIZE` allows).

## 7. Dependencies

*   `riscv_config_pkg`: Used for `XLEN`, `ADDR_WIDTH`, `REG_ADDR_WIDTH`, and `DEFAULT_ROB_SIZE` parameters.

## 8. Performance, Area, and Verification

*   **Performance:**
    *   **Critical Path:** TBD
    *   **Max Frequency:** TBD
*   **Area:** TBD (highly dependent on `ROB_SIZE` and the width of stored data).
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
| 1.0.0   | 2025-06-28 | DesignAI   | Initial fleshed-out implementation with robust pointer/counter logic. |
| 0.1.0   | 2025-06-27 | DesignAI   | Initial skeleton release.                               |
