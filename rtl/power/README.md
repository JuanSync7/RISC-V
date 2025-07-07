
# Power Management Unit (PMU)

## Overview

This directory contains the implementation of the Power Management Unit (PMU) for the RISC-V core. The PMU is responsible for managing the power consumption of the core through various techniques such as clock gating, power gating, and dynamic voltage and frequency scaling (DVFS).

## Modules

- **`power_management_unit.sv`**: The top-level module that integrates all the PMU sub-modules.
- **`power_state_machine.sv`**: Implements the main power state machine (FSM) that controls the power states of the core.
- **`dvfs_controller.sv`**: Manages the Dynamic Voltage and Frequency Scaling (DVFS) of the core.
- **`clock_gating_control.sv`**: Generates the clock enable signals for various parts of the core.
- **`power_domain_control.sv`**: Manages the power-on/off and retention states of the different power domains.
- **`pmu_csr.sv`**: Implements the Control and Status Registers (CSRs) for the PMU, allowing software to configure the power management policies.

## Integration

The PMU is integrated into the `riscv_core.sv` module. It is enabled by the `ENABLE_PMU` parameter. When enabled, the PMU monitors the core's activity and adjusts the power consumption accordingly.

## Configuration

The PMU is configured through the CSRs implemented in the `pmu_csr.sv` module. The following CSRs are available:

- **`PMU_ENABLE_ADDR`**: Enables or disables the PMU.
- **`PMU_CONFIG_ADDR`**: Configures the power management policies, such as aggressive clock gating, cache gating, retention mode, and power gating.
- **`IDLE_TIMEOUT_ADDR`**: Configures the idle timeout value.
- **`SLEEP_TIMEOUT_ADDR`**: Configures the sleep timeout value.
