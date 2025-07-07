# RISC-V QoS Management Unit Architecture

**Location:** `docs/architecture/`
**Purpose:** Detailed architectural documentation of the Quality of Service (QoS) Management Unit.
**Module:** `rtl/qos/qos_management_unit.sv`

---

## Overview

The `qos_management_unit` is a modular component responsible for handling Quality of Service (QoS) configurations, arbitrating access to shared resources based on QoS policies, and monitoring QoS violations within the RISC-V core. It dynamically generates QoS parameters for instruction fetches and data accesses, prioritizing critical operations like exceptions and debug accesses.

This unit is composed of the following sub-modules:

-   **`qos_policy_engine.sv`**: Generates QoS configurations (`qos_config_t`) based on system state (e.g., exception pending, debug access) and transaction type (instruction fetch, data access). It determines QoS levels, weights, and other parameters.
-   **`qos_arbiter.sv`**: Arbitrates between competing requests for shared resources (e.g., memory bus) based on the QoS configurations provided by the policy engine. It grants access to the highest priority requester.
-   **`qos_monitor.sv`**: Tracks resource utilization and detects QoS violations, such as memory request stalls or latency issues. It provides a counter for detected violations.

## Integration

The QoS Management Unit is instantiated within the `core_subsystem.sv` module. It receives inputs related to system state (e.g., `exception_pending_i`, `debug_access_pending_i`, `is_store_i`, `is_critical_data_access_i`) and provides QoS configurations for instruction and data accesses. The `qos_arbiter` within the unit manages requests from the instruction and data caches, and the `qos_monitor` observes memory request/ready signals to detect violations.

## Module Parameters

| Parameter Name   | Type      | Description                                                              | Default Value |
|------------------|-----------|--------------------------------------------------------------------------|---------------|
| `CORE_ID`        | `integer` | Unique identifier for the core, used in QoS configurations.              | `0`           |
| `NUM_REQUESTERS` | `integer` | Number of requesters for the QoS arbiter (e.g., 2 for instruction and data). | `2`           |

## Ports

| Port Name                     | Direction | Type                               | Description                                                              |
|-------------------------------|-----------|------------------------------------|--------------------------------------------------------------------------|
| `clk_i`                       | Input     | `logic`                            | System clock input.                                                      |
| `rst_ni`                      | Input     | `logic`                            | Asynchronous reset, active low.                                          |
| `qos_enable_i`                | Input     | `logic`                            | Global enable signal for QoS functionality.                              |
| `exception_pending_i`         | Input     | `logic`                            | Indicates if an exception is currently pending.                          |
| `debug_access_pending_i`      | Input     | `logic`                            | Indicates if a debug access is currently pending.                        |
| `is_store_i`                  | Input     | `logic`                            | Indicates if the current data access is a store operation.               |
| `is_critical_data_access_i`   | Input     | `logic`                            | Indicates if the current data access is critical (e.g., debug, exception-related). |
| `req_qos_config_i`            | Input     | `qos_config_t [NUM_REQUESTERS-1:0]` | Array of QoS configurations for each requester.                          |
| `req_valid_i`                 | Input     | `logic [NUM_REQUESTERS-1:0]`       | Valid signals for each requester.                                        |
| `req_ready_o`                 | Output    | `logic [NUM_REQUESTERS-1:0]`       | Ready signals for each requester.                                        |
| `mem_req_valid_i`             | Input     | `logic`                            | Valid signal for a memory request from the arbitration unit.             |
| `mem_req_ready_i`             | Input     | `logic`                            | Ready signal from the external memory system.                            |
| `granted_req_o`               | Output    | `logic [NUM_REQUESTERS-1:0]`       | One-hot encoded grant signal indicating which requester was granted.     |
| `granted_qos_config_o`        | Output    | `qos_config_t`                     | QoS configuration of the granted request.                                |
| `qos_violations_o`            | Output    | `logic [31:0]`                     | Counter for detected QoS violations.                                     |

## Internal Logic

### QoS Policy Engine (`qos_policy_engine.sv`)

This module contains the logic to generate `qos_config_t` structures for instruction fetches and data accesses. It uses inputs like `exception_pending_i`, `debug_access_pending_i`, `is_store_i`, and `is_critical_data_access_i` to determine the appropriate QoS level, transaction type, urgency, bandwidth guarantees, and latency requirements.

### QoS Arbiter (`qos_arbiter.sv`)

This module implements the arbitration logic. It takes an array of `qos_config_t` and `req_valid_i` signals from multiple requesters and determines which requester is granted access based on their QoS parameters. A simple fixed-priority scheme (critical > high > medium-high > medium) is currently implemented, with a tie-breaking mechanism (lowest index wins).

### QoS Monitor (`qos_monitor.sv`)

This module monitors for QoS violations. Currently, it increments a `qos_violation_counter` if a memory request is valid but the memory system is not ready. This indicates a potential stall or latency issue. Future enhancements will include more sophisticated monitoring for latency deadlines, bandwidth violations, and preemption issues.

## Configuration

The QoS unit's behavior is configurable through parameters defined in `qos_pkg.sv` and the top-level `qos_management_unit.sv` module. The `ENABLE_QOS` parameter in `core_subsystem.sv` allows for enabling or disabling the entire QoS functionality.

## Future Enhancements

-   More sophisticated arbitration algorithms (e.g., weighted round-robin, deficit round-robin).
-   Advanced QoS violation detection and reporting mechanisms.
-   Integration with a more comprehensive CSR management unit for dynamic QoS parameter updates.
-   Support for different QoS classes and service level agreements.

---

**Document Version:** 1.1
**Last Updated:** 2025-07-06
**Maintainer:** RISC-V RTL Team
**Status:** Draft