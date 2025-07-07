# Key Packages and Types

## 1. Overview

This document describes the core SystemVerilog packages used in the RISC-V project. A clear separation between configuration and internal types is maintained to ensure modularity and ease of integration.

## 2. Package Hierarchy

The package hierarchy follows the rules defined in `risc-v-package-hierarchy.mdc`. The `riscv_config_pkg` is the base package, and `riscv_types_pkg` imports it.

## 3. `riscv_config_pkg`

*   **Location:** `rtl/config/riscv_config_pkg.sv`
*   **Purpose:** This package contains all the user-configurable parameters for the RISC-V system. System integrators can modify this file to customize the core for their specific needs.

## 4. `riscv_types_pkg`

*   **Location:** `rtl/pkg/riscv_types_pkg.sv`
*   **Purpose:** This package contains all the fixed, internal type definitions for the RISC-V core. These types are fundamental to the core's operation and should not be modified by the user.