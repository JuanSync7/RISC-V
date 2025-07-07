# Quality of Service (QoS) Module Structure

This directory contains the SystemVerilog modules for the RISC-V Quality of Service (QoS) Management Unit.

## Overview

The QoS Management Unit is responsible for handling Quality of Service (QoS) configurations, arbitrating access to shared resources based on QoS policies, and monitoring QoS violations within the RISC-V core. It dynamically generates QoS parameters for instruction fetches and data accesses, prioritizing critical operations like exceptions and debug accesses.

It consists of the following sub-modules:

- **`qos_management_unit.sv`**: The top-level QoS module that integrates the policy engine, arbiter, and monitor.
- **`qos_policy_engine.sv`**: Generates QoS configurations based on system state and transaction type.
- **`qos_arbiter.sv`**: Arbitrates access to shared resources based on the QoS configurations of competing requests.
- **`qos_monitor.sv`**: Tracks resource utilization and detects QoS violations.
- **`qos_pkg.sv`**: A package defining common data types and parameters used across the QoS modules.

## Integration

The QoS Management Unit is instantiated within the `core_subsystem.sv` module. It receives inputs related to system state (e.g., exception pending, debug access) and provides QoS configurations for instruction and data accesses. It also arbitrates requests from different functional units and monitors for QoS violations.

## Configuration

The QoS Management Unit's behavior is configurable through parameters, including:

- `CORE_ID`: Unique identifier for the core.
- `NUM_REQUESTERS`: Number of requesters for the QoS arbiter.

## Future Enhancements

- More sophisticated arbitration algorithms (e.g., weighted round-robin, deficit round-robin).
- Advanced QoS violation detection and reporting mechanisms.
- Integration with a more comprehensive CSR management unit for dynamic QoS parameter updates.
- Support for different QoS classes and service level agreements.
