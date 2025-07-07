# Bus Watchdog Module

## Overview

This directory contains the modular components of the bus watchdog timer for the RISC-V core. The watchdog is designed to prevent system hangs by detecting bus timeouts.

## Modular Architecture

The bus watchdog is broken down into the following modules:

-   `bus_watchdog.sv`: The top-level module that integrates all the watchdog components.
-   `watchdog_timer.sv`: The core countdown timer. It is enabled when a bus transaction is active and resets when the transaction completes or a timeout occurs.
-   `watchdog_csr.sv`: The Control and Status Registers (CSR) for the watchdog. This allows for runtime configuration of the watchdog, including enabling/disabling the watchdog and setting the timeout value.
-   `watchdog_monitor.sv`: This module monitors the bus for activity. It signals the timer to start counting when a bus request is made and there is no grant.

## Integration

The `bus_watchdog` module is instantiated in the `riscv_core` module. It is connected to the CSR bus for configuration and the main bus to be monitored.
