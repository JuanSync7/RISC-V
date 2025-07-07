# Multi-Core System Architecture

## 1. Overview

The `multi_core_system` module represents the top-level integration of the refactored multi-core RISC-V system. It orchestrates the interaction between multiple RISC-V cores, memory subsystems, and various management and monitoring units to form a complete and functional multi-core processor. This module is designed to be highly configurable, allowing for flexible deployment across different application requirements.

## 2. Features

- **Scalable Multi-Core Integration**: Supports configurable number of RISC-V cores.
- **Comprehensive Interconnect**: Manages communication between cores, caches, and external memory interfaces (AXI4, CHI, TileLink).
- **Advanced Cache Hierarchy**: Integrates L1 I/D caches, L2, and L3 caches with coherency mechanisms.
- **Performance Monitoring**: Provides detailed performance metrics such as instruction retired count, cycle count, cache miss rates, and IPC.
- **System Management**: Includes functionalities for system configuration, power management, and inter-core communication.
- **Debug Support**: Offers debug request and acknowledgment signals for system-level debugging.

## 3. Internal Blocks

The `multi_core_system` module is composed of the following key sub-modules:

- **`multi_core_cluster`**:
    - **Description**: Encapsulates the individual RISC-V cores and their associated L1 I/D caches. It handles core-specific interrupts, debug requests, and provides per-core performance metrics.
    - **Key Responsibilities**: Core instantiation, L1 cache integration, interrupt handling, debug interface, and per-core performance data collection.

- **`multi_core_interconnect`**:
    - **Description**: Manages the data flow and communication between the core cluster, memory hierarchy, and external interfaces. It supports multiple memory protocols (AXI4, CHI, TileLink) and ensures cache coherency.
    - **Key Responsibilities**: Inter-core communication, memory access arbitration, protocol conversion, and cache coherency enforcement.

- **`multi_core_management`**:
    - **Description**: Provides system-level management functionalities, including configuration, power management, and synchronization primitives. It interacts with the interconnect to control system-wide behavior.
    - **Key Responsibilities**: System configuration, power state management, inter-core synchronization (barriers), and overall system status reporting.

- **`multi_core_monitoring`**:
    - **Description**: Collects and aggregates performance and status information from various parts of the multi-core system. It calculates system-wide metrics like total instructions, total cycles, and overall performance status.
    - **Key Responsibilities**: Performance data aggregation, IPC calculation, cache hit rate monitoring, and identification of performance bottlenecks.

## 4. Interfaces and Ports

| Port Name                 | Direction | Width (bits) | Description                                                              |
| :------------------------ | :-------- | :----------- | :----------------------------------------------------------------------- |
| `clk_i`                   | Input     | 1            | System clock.                                                            |
| `rst_ni`                  | Input     | 1            | Asynchronous reset (active low).                                         |
| `external_irq_i`          | Input     | `NUM_CORES`  | External interrupt requests for each core.                               |
| `timer_irq_i`             | Input     | 1            | Timer interrupt request.                                                 |
| `software_irq_i`          | Input     | 1            | Software interrupt request.                                              |
| `debug_req_i`             | Input     | 1            | Debug request signal.                                                    |
| `debug_ack_o`             | Output    | `NUM_CORES`  | Debug acknowledgment for each core.                                      |
| `total_instructions_o`    | Output    | 32           | Total instructions retired across all cores.                             |
| `total_cycles_o`          | Output    | 32           | Total cycles elapsed.                                                    |
| `cache_miss_count_o`      | Output    | 32           | Total cache miss count across all caches.                                |
| `performance_status_o`    | Output    | 32           | Overall system performance status.                                       |
| `core_active_o`           | Output    | `NUM_CORES`  | Indicates if each core is active.                                        |
| `sys_config_i`            | Input     | 32           | System configuration input.                                              |
| `sys_status_o`            | Output    | 32           | System status output.                                                    |
| `axi4_if`                 | Inout     | -            | AXI4 master interface for external memory access.                        |
| `chi_if`                  | Inout     | -            | CHI interface for cache coherency.                                       |
| `tl_if`                   | Inout     | -            | TileLink master interface for external memory access.                    |

## 5. Parameters

| Parameter Name          | Type    | Default Value             | Description                                                              |
| :---------------------- | :------ | :------------------------ | :----------------------------------------------------------------------- |
| `NUM_CORES`             | `integer` | `DEFAULT_NUM_CORES`       | Number of RISC-V cores in the system.                                    |
| `EXECUTION_MODE`        | `string`  | `DEFAULT_EXECUTION_MODE`  | Execution mode (e.g., in-order, out-of-order).                           |
| `BRANCH_PREDICTOR_TYPE` | `string`  | `DEFAULT_BRANCH_PREDICTOR_TYPE` | Type of branch predictor used.                                           |
| `DEFAULT_PROTOCOL`      | `string`  | `DEFAULT_MEMORY_PROTOCOL` | Default memory protocol (e.g., AXI4, CHI, TileLink).                     |
| `L1_ICACHE_SIZE`        | `integer` | `DEFAULT_L1_ICACHE_SIZE`  | Size of L1 instruction cache.                                            |
| `L1_DCACHE_SIZE`        | `integer` | `DEFAULT_L1_DCACHE_SIZE`  | Size of L1 data cache.                                                   |
| `L2_CACHE_SIZE`         | `integer` | `DEFAULT_L2_CACHE_SIZE`   | Size of L2 cache.                                                        |
| `L3_CACHE_SIZE`         | `integer` | `DEFAULT_L3_CACHE_SIZE`   | Size of L3 cache.                                                        |
| `MSG_WIDTH`             | `integer` | `DEFAULT_MSG_WIDTH`       | Width of inter-core communication messages.                              |
| `NUM_BARRIERS`          | `integer` | `DEFAULT_NUM_BARRIERS`    | Number of synchronization barriers supported.                            |
| `MAX_OUTSTANDING`       | `integer` | `DEFAULT_AXI4_MAX_OUTSTANDING` | Maximum outstanding AXI4 transactions.                                   |

## 6. Dependencies

- `riscv_core_pkg` (from `rtl/pkg/riscv_core_pkg.sv`): Provides core-related types and configurations.
- `riscv_memory_config_pkg` (from `rtl/pkg/riscv_memory_config_pkg.sv`): Provides memory-related configurations.
- `multi_core_cluster.sv` (from `rtl/core/multi_core_system/components/multi_core_cluster.sv`): Core cluster module.
- `multi_core_interconnect.sv` (from `rtl/core/multi_core_system/components/multi_core_interconnect.sv`): Interconnect module.
- `multi_core_management.sv` (from `rtl/core/multi_core_system/components/multi_core_management.sv`): Management module.
- `multi_core_monitoring.sv` (from `rtl/core/multi_core_system/components/multi_core_monitoring.sv`): Monitoring module.
- `memory_req_rsp_if` (from `rtl/interfaces/memory_req_rsp_if.sv`): Memory request/response interface.
- `cache_coherency_if` (from `rtl/interfaces/cache_coherency_if.sv`): Cache coherency interface.
- `inter_core_comm_if` (from `rtl/interfaces/inter_core_comm_if.sv`): Inter-core communication interface.
- `sync_primitives_if` (from `rtl/interfaces/sync_primitives_if.sv`): Synchronization primitives interface.
- `axi4_if` (from `rtl/interfaces/axi4_if.sv`): AXI4 interface.
- `chi_if` (from `rtl/interfaces/chi_if.sv`): CHI interface.
- `tilelink_if` (from `rtl/interfaces/tilelink_if.sv`): TileLink interface.

## 7. Design Details

The `multi_core_system` module instantiates and connects the four main sub-modules: `u_multi_core_cluster`, `u_multi_core_interconnect`, `u_multi_core_management`, and `u_multi_core_monitoring`. It defines internal interfaces and wires to facilitate communication between these blocks. The system's configurability is achieved through a set of parameters that control the number of cores, cache sizes, execution modes, and memory protocols.

## 8. Verification and Testing

The `multi_core_system` is a critical component and is subject to extensive verification. This includes:
- **Unit Testing**: Each sub-module (`multi_core_cluster`, `multi_core_interconnect`, etc.) is individually tested.
- **Integration Testing**: The integrated system is tested to ensure correct interaction between sub-modules.
- **System-Level Verification**: Comprehensive testbenches simulate real-world scenarios, including multi-threaded execution, cache coherency, and interrupt handling.
- **Performance Validation**: Performance metrics are collected and analyzed to ensure the system meets performance targets.

## 9. Future Enhancements

- **Dynamic Core Management**: Implement dynamic enabling/disabling of cores for power optimization.
- **Advanced QoS**: Further enhance QoS mechanisms for more granular control over resource allocation.
- **Fault Tolerance**: Incorporate error detection and correction mechanisms for increased reliability.
- **Virtualization Support**: Add hardware support for virtualization.
