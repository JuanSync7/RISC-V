# RISC-V Core Configuration Guide

This document provides a comprehensive guide to configuring the RISC-V core. A flexible configuration system allows you to tailor the core's features and performance to meet the specific requirements of your application.

## Table of Contents

- [Introduction](#introduction)
- [Configuration Files](#configuration-files)
- [Core Parameters](#core-parameters)
- [Memory System Parameters](#memory-system-parameters)
- [Pipeline Parameters](#pipeline-parameters)
- [SoC Parameters](#soc-parameters)
- [Verification Parameters](#verification-parameters)

## Introduction

The RISC-V core is highly configurable through a set of SystemVerilog packages. These packages contain parameters that control various aspects of the core, such as the instruction set architecture (ISA), memory subsystem, pipeline stages, and more. By modifying these parameters, you can create a customized RISC-V core that is optimized for your target application, whether it's a high-performance system-on-chip (SoC) or a low-power embedded device.

This guide will walk you through the available configuration options and explain how to modify them to achieve your desired core configuration.

## Configuration Files

The primary configuration files are located in the `rtl/config/core/` directory. These files are:

-   `riscv_config_pkg.sv`: General project-wide configuration.
-   `riscv_core_config_pkg.sv`: Core-specific parameters.
-   `riscv_memory_config_pkg.sv`: Memory subsystem configuration.
-   `riscv_pipeline_config_pkg.sv`: Pipeline configuration.
-   `riscv_soc_config_pkg.sv`: SoC-level configuration.
-   `riscv_verification_config_pkg.sv`: Verification-related parameters.

We will explore the key parameters within these files in the following sections.

### Core Parameters (`riscv_core_config_pkg.sv`)

This package contains the fundamental configuration for the RISC-V core architecture.

| Parameter              | Description                               | Default Value |
| ---------------------- | ----------------------------------------- | ------------- |
| `XLEN`                 | Data width of the core (32 for RV32)      | `32`          |
| `ADDR_WIDTH`           | Address width of the core                 | `32`          |
| `REG_COUNT`            | Number of architectural registers         | `32`          |
| `DEFAULT_RESET_VECTOR` | The default reset vector address          | `32'h0`       |

### Memory System Parameters (`riscv_memory_config_pkg.sv`)

This package centralizes all memory-related configurations for the RISC-V processor.

#### Cache Configuration

| Parameter                | Description                                        | Default Value    |
| ------------------------ | -------------------------------------------------- | ---------------- |
| `ENABLE_L2_CACHE`        | Enables the L2 cache                               | `1`              |
| `ENABLE_L3_CACHE`        | Enables the L3 cache                               | `1`              |
| `DEFAULT_L1_ICACHE_SIZE` | Size of the L1 instruction cache in bytes          | `16KB`           |
| `DEFAULT_L1_DCACHE_SIZE` | Size of the L1 data cache in bytes                 | `16KB`           |
| `DEFAULT_L2_CACHE_SIZE`  | Size of the L2 cache in bytes                      | `256KB`          |
| `DEFAULT_L3_CACHE_SIZE`  | Size of the L3 cache in bytes                      | `2MB`            |
| `DEFAULT_CACHE_LINE_SIZE`| Cache line size in bytes                           | `64`             |
| `DEFAULT_MEMORY_PROTOCOL`| Default memory protocol (e.g., "AXI4")             | `"AXI4"`         |

### Pipeline Parameters (`riscv_pipeline_config_pkg.sv`)

This package defines the configuration for the processor's pipeline.

| Parameter                     | Description                                    | Default Value      |
| ----------------------------- | ---------------------------------------------- | ------------------ |
| `DEFAULT_EXECUTION_MODE`      | "IN_ORDER" or "OUT_OF_ORDER"                   | `"OUT_OF_ORDER"`   |
| `DEFAULT_BRANCH_PREDICTOR_TYPE` | "STATIC", "DYNAMIC", or "TOURNAMENT"           | `"TOURNAMENT"`     |
| `DEFAULT_BTB_ENTRIES`         | Number of entries in the Branch Target Buffer  | `512`              |
| `DEFAULT_ROB_SIZE`            | Size of the Re-order Buffer                    | `32`               |
| `DEFAULT_RS_SIZE`             | Size of the Reservation Stations               | `16`               |
| `DEFAULT_NUM_ALU_UNITS`       | Number of ALU units in the execution stage     | `2`                |
| `DEFAULT_PIPELINE_STAGES`     | Number of pipeline stages                      | `5`                |

### SoC Parameters (`riscv_soc_config_pkg.sv`)

This package contains System-on-Chip (SoC) level configurations.

| Parameter           | Description                               | Default Value |
| ------------------- | ----------------------------------------- | ------------- |
| `MAX_CORES`         | Maximum number of cores supported         | `4`           |
| `DEFAULT_NUM_CORES` | Default number of cores in the SoC        | `1`           |
| `DEFAULT_QOS_LEVELS`| Number of QoS priority levels             | `8`           |

### Verification Parameters (`riscv_verification_config_pkg.sv`)

This package provides configurations specifically for the verification environment.

| Parameter               | Description                               | Default Value |
| ----------------------- | ----------------------------------------- | ------------- |
| `CLOCK_PERIOD`          | Default clock period for testbenches      | `10ns`        |
| `TIMEOUT_CYCLES`        | Default test timeout in cycles            | `100000`      |
| `TARGET_FREQ_ASIC`      | Target frequency for ASIC synthesis (MHz) | `1000`        |
| `TARGET_FREQ_FPGA`      | Target frequency for FPGA synthesis (MHz) | `100`         | 