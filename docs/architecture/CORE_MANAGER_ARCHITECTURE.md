# Core Manager Architecture

## 1. Overview

The `core_manager` module is a central component responsible for managing the operations within a multi-core RISC-V system. It orchestrates core startup and shutdown, facilitates inter-core communication, and handles hardware synchronization primitives such as barriers. This module acts as the central hub for all multi-core coordination activities, ensuring efficient and synchronized operation of the individual cores.

## 2. Features

*   **Inter-Core Communication Arbitration and Routing:** Arbitrates requests from multiple cores to send messages and routes these messages to their intended destination cores.
*   **Hardware Barrier Synchronization:** Implements stateful hardware barriers, allowing multiple cores to synchronize their execution at specific points.
*   **Core Status Management:** Monitors and indicates the readiness and active status of individual cores within the system.

## 3. Internal Blocks

The `core_manager` module comprises the following key internal blocks:

### 3.1. Communication Arbiter (`CommArbiter`)

*   **Description:** This block is responsible for arbitrating access to the inter-core communication bus. It uses a round-robin scheme to ensure fair access among all requesting cores.
*   **Functionality:**
    *   Receives `send_valid_w` requests from each core via the `inter_core_comm_if`.
    *   Selects one requesting core per cycle based on a round-robin priority (`rr_arbiter_ptr_r`).
    *   Asserts `send_ready_w` to the granted core, indicating that its message can be transmitted.

### 3.2. Communication Router (`CommRouter`)

*   **Description:** This block takes the message from the granted core and routes it to the specified destination core.
*   **Functionality:**
    *   Receives the message (`send_message_w`) and destination ID (`send_dest_id_w`) from the granted core.
    *   Checks if the destination core is ready to receive (`recv_ready_w`).
    *   If ready, it drives `recv_valid_w`, `recv_source_id_w`, and `recv_message_w` to the destination core.

### 3.3. Barrier Synchronization (`BarrierSync`)

*   **Description:** This block manages hardware barriers, allowing a group of cores to wait until all members have reached a specific point before proceeding. It maintains the arrival and release status for multiple barriers.
*   **Internal Storage:**
    *   `barrier_arrival_mask_r`: A bitmask for each barrier, where each bit indicates if a specific core has arrived at that barrier.
    *   `barrier_release_mask_r`: A bitmask for each barrier, indicating if a specific core has acknowledged release from that barrier.
*   **Functionality:**
    *   **Arrival:** When a core asserts `arrive_valid_w` for a specific barrier ID, its corresponding bit in `barrier_arrival_mask_ns` is set, and `arrive_ready_w` is asserted back to the core.
    *   **Release Condition:** Once all cores designated for a barrier have arrived (all bits in `barrier_arrival_mask_r` for that barrier are set), the `release_valid_w` signal is asserted to all participating cores.
    *   **Release Acknowledgment:** Cores acknowledge release by asserting `release_ready_w`. Their corresponding bits in `barrier_release_mask_ns` are set.
    *   **Reset:** Once all cores have arrived and acknowledged release, the barrier's `arrival_mask` and `release_mask` are reset, making the barrier available for reuse.

## 4. Interfaces

| Port Name                 | Direction | Description                                                               | Clock Domain         |
| :------------------------ | :-------- | :------------------------------------------------------------------------ | :------------------- |
| `clk_i`                   | Input     | System clock                                                              | `clk_i`              |
| `rst_ni`                  | Input     | Asynchronous active-low reset                                             | `clk_i` (async assert) |
| `core_active_i`           | Input     | Bitmask indicating which cores are active and running.                    | `clk_i`              |
| `core_ready_o`            | Output    | Bitmask indicating manager is ready for core operations.                  | `clk_i`              |
| `comm_if`                 | Interface | Custom Inter-Core Communication interface. Handles routing messages between cores. | `clk_i`              |
| `sync_if`                 | Interface | Custom Synchronization Primitives interface. Handles hardware barrier synchronization. | `clk_i`              |

## 5. Parameters

| Parameter Name   | Type      | Description                                                               | Default Value      | Constraints |
| :--------------- | :-------- | :------------------------------------------------------------------------ | :----------------- | :---------- |
| `NUM_CORES`      | `integer` | The total number of cores in the system.                                  | `DEFAULT_NUM_CORES`| Must be > 1 |
| `CORE_ID_WIDTH`  | `integer` | Width of the core ID. Derived from `NUM_CORES`.                           | `$clog2(NUM_CORES)`| N/A         |

## 6. State Machine (Implicit)

While there isn't a single top-level FSM, the `core_manager` module's behavior is governed by the state of its internal components, particularly the round-robin arbiter and the barrier synchronization logic.

*   **Round-Robin Arbiter:** The `rr_arbiter_ptr_r` state register cycles through core IDs, determining the priority for message arbitration. It advances upon a successful grant.
*   **Barrier Synchronization:** Each barrier instance implicitly operates as a two-phase state machine (arrival and release) managed by `barrier_arrival_mask_r` and `barrier_release_mask_r`. A barrier transitions from idle to arrival phase when cores start arriving, then to release phase once all cores have arrived, and finally back to idle after all cores have acknowledged release.

## 7. Dependencies

*   `riscv_config_pkg`: Used for `DEFAULT_NUM_CORES` parameter.
*   `rtl/interfaces/inter_core_comm_if.sv`: Defines the interface for inter-core communication.
*   `rtl/interfaces/sync_primitives_if.sv`: Defines the interface for synchronization primitives.

## 8. Performance, Area, and Verification

*   **Performance:**
    *   **Critical Path:** Likely in the arbiter's priority encoding logic or the barrier's arrival/release checking logic, especially as `NUM_CORES` and `NUM_BARRIERS` increase.
    *   **Max Frequency:** TBD
*   **Area:** TBD (highly dependent on `NUM_CORES` and `NUM_BARRIERS`, as these directly impact the size of the masks and arbiter logic).
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

*   **Testbench:** `riscv_core_integration_tb` (needs update for this module)
*   **Test Vectors:** N/A

## 11. Revision History

| Version | Date       | Author     | Description                                             |
| :------ | :--------- | :--------- | :------------------------------------------------------ |
| 1.0.0   | 2025-07-06 | DesignAI   | Initial comprehensive documentation.                    |
| 1.0.0   | 2025-06-28 | DesignAI   | Initial fleshed-out implementation with arbiter and barrier logic. |
| 0.1.0   | 2025-06-27 | DesignAI   | Initial skeleton release.                               |
