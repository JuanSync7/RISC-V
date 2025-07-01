# Core Configuration Packages

## Overview
This directory contains SystemVerilog packages that define configuration parameters and constants for the RISC-V processor core components. These packages provide centralized configuration management for all core subsystems.

## Purpose
- Centralize core configuration parameters
- Provide compile-time customization options
- Ensure consistent parameter usage across modules
- Enable easy reconfiguration for different implementations

## Contents

### Configuration Package Files
- `riscv_config_pkg.sv` - Global RISC-V configuration parameters
- `riscv_core_config_pkg.sv` - Core-specific configuration settings
- `riscv_memory_config_pkg.sv` - Memory subsystem configuration
- `riscv_pipeline_config_pkg.sv` - Pipeline stage configuration
- `riscv_soc_config_pkg.sv` - System-on-Chip integration parameters
- `riscv_verification_config_pkg.sv` - Verification environment configuration

## Configuration Categories

### Core Parameters
- Instruction set architecture options
- Pipeline depth and stage configurations
- Register file specifications
- Execution unit configurations

### Memory Configuration
- Cache sizes and associativity
- Memory interface parameters
- Address space definitions
- Coherency protocol settings

### Performance Settings
- Out-of-order execution parameters
- Branch predictor configurations
- Prefetch and speculation settings
- Quality of Service (QoS) parameters

## Usage
These packages are imported by RTL modules throughout the design:

```systemverilog
import riscv_core_config_pkg::*;
import riscv_memory_config_pkg::*;
```

## Dependencies
- SystemVerilog package system
- RTL modules in core, memory, and pipeline directories
- Verification environments in tb/ directory

---
**Document Version:** 1.0  
**Last Updated:** 2024-12-19  
**Status:** Active 