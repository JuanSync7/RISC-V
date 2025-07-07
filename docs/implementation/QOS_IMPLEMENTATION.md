# Quality of Service (QoS) Management Unit Implementation

**Location:** `docs/implementation/`
**Purpose:** Detailed implementation notes for the `qos_management_unit.sv` module and its sub-components.

---

## Overview

The QoS Management Unit is implemented as a modular and parameterized SystemVerilog component, designed to enhance the RISC-V core's ability to manage and prioritize memory and resource access. The implementation adheres to the principles of clear separation of concerns, with distinct modules for policy generation, arbitration, and monitoring.

## Module Breakdown

### `qos_pkg.sv`

This package defines the core data types and parameters used throughout the QoS unit. Key definitions include:

-   `qos_level_t`: Enumerated type for defining different QoS priority levels (e.g., `CRITICAL`, `HIGH`, `MEDIUM_HIGH`, `MEDIUM`).
-   `qos_weight_t`: Enumerated type for assigning weights to different QoS levels, used in arbitration.
-   `qos_transaction_type_t`: Enumerated type to distinguish between instruction fetch and data access transactions.
-   `qos_config_t`: A packed struct that encapsulates all QoS-related parameters for a given transaction, including level, type, urgency, bandwidth guarantees, latency cycles, and core ID.

### `qos_policy_engine.sv`

This module is responsible for generating the `qos_config_t` structure for instruction and data access requests. It contains two `automatic` functions:

-   `get_instruction_qos_config()`: Determines the QoS parameters for instruction fetches. It prioritizes instruction fetches when an exception is pending, setting the QoS level to `QOS_LEVEL_CRITICAL` and enabling urgent and real-time flags. Otherwise, it defaults to `QOS_LEVEL_HIGH`.
-   `get_data_qos_config(input logic is_store, input logic is_critical)`: Determines the QoS parameters for data accesses (loads or stores). Critical accesses (e.g., debug, exception-related) are assigned `QOS_LEVEL_CRITICAL`. Normal stores and loads are assigned `QOS_LEVEL_MEDIUM` and `QOS_LEVEL_MEDIUM_HIGH` respectively. It also sets urgency, real-time, and preemptable flags based on criticality.

The module uses `always_comb` block to continuously update the output `instr_qos_config_o` and `data_qos_config_o` based on the current inputs and the logic within these functions. When `qos_enable_i` is deasserted, all QoS outputs are tied off to zero.

### `qos_arbiter.sv`

This module implements a parameterized arbitration logic for multiple requesters. It takes an array of `qos_config_t` and `req_valid_i` signals from `NUM_REQUESTERS` and outputs `req_ready_o` and a one-hot `grant_o` signal, along with the `granted_qos_config_o`.

-   **Priority Encoding**: Each requester's `qos_level` is mapped to an internal `priority` signal. Currently, a simple mapping from `qos_level_t` to a 2-bit priority value is used.
-   **Arbitration Logic**: A fixed-priority arbitration scheme is implemented. It iterates through priority levels (from critical to medium) and then through requesters. The first active requester found at the highest priority level is granted. If multiple requests have the same highest priority, the one with the lowest index (e.g., instruction fetch over data access) wins.
-   **Ready Signal Generation**: A requester's `req_ready_o` is asserted if it receives a grant (`grant_o`).

### `qos_monitor.sv`

This module is responsible for monitoring QoS violations and providing a `qos_violations_o` counter. It currently tracks a basic violation scenario:

-   **Memory Request Stall**: If `mem_req_valid_i` is asserted but `mem_req_ready_i` is deasserted, it indicates that a memory request is pending but the memory system is not ready to accept it. This increments the `qos_violation_counter`.

Future enhancements for this module include more advanced monitoring capabilities, such as tracking latency deadlines, bandwidth utilization, and preemption events.

### `qos_management_unit.sv` (Top-Level)

This is the top-level module that integrates `qos_policy_engine.sv`, `qos_arbiter.sv`, and `qos_monitor.sv`. It acts as the interface between the core subsystem and the internal QoS logic.

-   **Instantiation**: It instantiates the three sub-modules and connects their respective ports.
-   **Parameter Propagation**: Parameters like `CORE_ID` and `NUM_REQUESTERS` are propagated to the sub-modules.
-   **Signal Connections**: It manages the internal signals that connect the outputs of one sub-module to the inputs of another (e.g., `instr_qos_config` and `data_qos_config` from the policy engine are fed into the arbiter).
-   **Conditional Instantiation**: The entire QoS unit is conditionally instantiated using a `generate` block based on the `ENABLE_QOS` parameter from `core_subsystem.sv`. If `ENABLE_QOS` is `0`, the QoS-related outputs are tied off to default values.

## Integration with `core_subsystem.sv`

-   **Parameter**: The `ENABLE_QOS` parameter is added to `core_subsystem.sv` to control the instantiation of the QoS unit.
-   **Inputs**: `debug_access_pending_i`, `is_store_i`, `is_critical_data_access_i`, and `qos_enable_i` are added as inputs to `core_subsystem.sv` and connected to the `qos_management_unit`.
-   **Outputs**: `qos_violations_o` is an output from `core_subsystem.sv`.
-   **Memory Request Handling**: The `icache_if.req_valid` and `dcache_if.req_valid` signals are connected to the `qos_req_valid` input of the `qos_management_unit`. The `qos_req_ready` output from the QoS unit is connected back to `icache_if.req_ready` and `dcache_if.req_ready`.
-   **Memory Request Muxing**: The `mem_req_o` (memory request) and `mem_qos_config_o` (QoS config for memory request) are now driven by the `qos_granted_config` and a mux based on `qos_granted_req` from the `qos_management_unit`. This replaces the direct connection from `memory_arbitration_unit`.

## Error Handling and Parameterization

-   The `ENABLE_QOS` parameter allows for flexible inclusion or exclusion of the QoS unit. When disabled, QoS-related outputs are set to default values, ensuring the core functions correctly without QoS overhead.
-   The `qos_arbiter` is parameterized by `NUM_REQUESTERS`, allowing it to be easily adapted for different numbers of competing requests.

---

**Document Version:** 1.0
**Last Updated:** 2025-07-06
**Maintainer:** RISC-V RTL Team
**Status:** Draft