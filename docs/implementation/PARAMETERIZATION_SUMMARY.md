# RISC-V Parameterization Summary

## Overview

This document summarizes the comprehensive parameterization work completed for the RISC-V processor design. All hard-coded values have been centralized into a configuration package system that provides complete flexibility for different design targets and requirements.

## Parameterization Strategy

### 1. Centralized Configuration Package (`riscv_config_pkg.sv`)

The `riscv_config_pkg.sv` serves as the single source of truth for all configurable parameters in the design. This package is imported by all other packages and modules, ensuring consistency and maintainability.

#### Key Benefits:
- **Single Source of Truth**: All parameters defined in one location
- **Complete Flexibility**: Easy to switch between different configurations
- **Type Safety**: Parameters are properly typed and validated
- **Documentation**: Each parameter includes detailed descriptions and constraints

### 2. Configuration Categories

The configuration package organizes parameters into logical categories:

#### Core Architecture Configuration
```systemverilog
parameter integer XLEN = 32;                    // Data width
parameter integer ADDR_WIDTH = 32;              // Address width
parameter integer REG_COUNT = 32;               // Number of registers
parameter logic [ADDR_WIDTH-1:0] DEFAULT_RESET_VECTOR = 32'h0000_0000;
```

#### RISC-V Instruction Encoding Constants
```systemverilog
parameter logic [6:0] OPCODE_LUI    = 7'b0110111;
parameter logic [6:0] OPCODE_AUIPC  = 7'b0010111;
parameter logic [6:0] OPCODE_JAL    = 7'b1101111;
// ... all RISC-V opcodes and function codes
```

#### Exception and Interrupt Configuration
```systemverilog
parameter logic [31:0] CAUSE_MISALIGNED_FETCH = 32'h0;
parameter logic [31:0] CAUSE_ILLEGAL_INSTRUCTION = 32'h2;
parameter logic [31:0] CAUSE_INTERRUPT = 32'h80000000;
// ... all exception causes and CSR addresses
```

#### Multi-Core Configuration
```systemverilog
parameter integer MAX_CORES = 4;
parameter integer CORE_ID_WIDTH = $clog2(MAX_CORES);
parameter integer DEFAULT_NUM_CORES = 1;
```

#### Cache System Configuration
```systemverilog
parameter integer DEFAULT_L1_CACHE_SIZE = 32*1024;     // 32KB
parameter integer DEFAULT_L2_CACHE_SIZE = 256*1024;    // 256KB
parameter integer DEFAULT_L3_CACHE_SIZE = 2*1024*1024; // 2MB
parameter integer DEFAULT_CACHE_LINE_SIZE = 64;        // 64 bytes
```

#### Branch Predictor Configuration
```systemverilog
parameter integer DEFAULT_BTB_ENTRIES = 64;
parameter integer DEFAULT_BHT_ENTRIES = 256;
parameter integer DEFAULT_PHT_ENTRIES = 1024;
parameter integer DEFAULT_GLOBAL_HISTORY_WIDTH = 8;
```

#### Out-of-Order Engine Configuration
```systemverilog
parameter integer DEFAULT_ROB_SIZE = 32;
parameter integer DEFAULT_RS_SIZE = 16;
parameter integer DEFAULT_PHYS_REGS = 64;
parameter integer DEFAULT_NUM_ALU_UNITS = 2;
parameter integer DEFAULT_NUM_MULT_UNITS = 1;
parameter integer DEFAULT_NUM_DIV_UNITS = 1;
```

#### Memory System Configuration
```systemverilog
parameter integer DEFAULT_STRIDE_TABLE_SIZE = 64;
parameter integer DEFAULT_AXI4_ID_WIDTH = 4;
parameter integer DEFAULT_AXI4_DATA_WIDTH = 32;
```

#### Verification Configuration
```systemverilog
parameter integer DEFAULT_CLK_PERIOD = 10;             // 100MHz
parameter integer DEFAULT_TIMEOUT_CYCLES = 1000;
parameter integer DEFAULT_MAX_TEST_ITERATIONS = 100;
```

### 3. Configuration Presets

The configuration package includes predefined presets for different design targets:

#### Small Configuration (Area-Constrained)
```systemverilog
parameter integer SMALL_L1_CACHE_SIZE = 8*1024;        // 8KB
parameter integer SMALL_ROB_SIZE = 16;
parameter integer SMALL_RS_SIZE = 8;
parameter integer SMALL_BTB_ENTRIES = 32;
```

#### Large Configuration (High-Performance)
```systemverilog
parameter integer LARGE_L1_CACHE_SIZE = 64*1024;       // 64KB
parameter integer LARGE_ROB_SIZE = 64;
parameter integer LARGE_RS_SIZE = 32;
parameter integer LARGE_BTB_ENTRIES = 128;
```

### 4. Package Dependencies

The package system follows a clear dependency hierarchy:

```
riscv_config_pkg.sv (Base - no dependencies)
    ↓
riscv_exception_pkg.sv (depends on config)
    ↓
riscv_types_pkg.sv (depends on config + exception)
    ↓
riscv_mem_types_pkg.sv (depends on core types)
riscv_cache_types_pkg.sv (depends on memory types)
riscv_bp_types_pkg.sv (depends on core types)
riscv_protocol_types_pkg.sv (depends on core types)
riscv_ooo_types_pkg.sv (depends on exception types)
riscv_verif_types_pkg.sv (depends on core types)
    ↓
riscv_core_pkg.sv (depends on all others)
```

### 5. Updated Packages

All specialized packages have been updated to use the configuration package:

#### `riscv_types_pkg.sv`
- Removed hard-coded architectural parameters
- Now imports `riscv_config_pkg::*`
- Uses `XLEN`, `ADDR_WIDTH`, `REG_COUNT` from config
- Uses `OPCODE_*` constants from config

#### `riscv_exception_pkg.sv`
- Removed hard-coded exception cause codes
- Now imports `riscv_config_pkg::*`
- Uses `CAUSE_*` constants from config
- Uses `MSTATUS_ADDR`, `MTVEC_ADDR` etc. from config

#### `riscv_cache_types_pkg.sv`
- Removed hard-coded cache sizes and parameters
- Now imports `riscv_config_pkg::*`
- Uses `DEFAULT_L1_CACHE_SIZE`, `DEFAULT_CACHE_LINE_SIZE` etc.
- Added configuration validation functions

#### `riscv_bp_types_pkg.sv`
- Removed hard-coded branch predictor parameters
- Now imports `riscv_config_pkg::*`
- Uses `DEFAULT_BTB_ENTRIES`, `DEFAULT_BHT_ENTRIES` etc.
- Added branch classification functions

#### `riscv_ooo_types_pkg.sv`
- Removed hard-coded OoO engine parameters
- Now imports `riscv_config_pkg::*`
- Uses `DEFAULT_ROB_SIZE`, `DEFAULT_RS_SIZE` etc.
- Added instruction classification functions

#### `riscv_core_pkg.sv`
- Now imports `riscv_config_pkg::*` first
- Provides configuration presets (`SMALL_OOO_CONFIG`, `LARGE_OOO_CONFIG`)
- Includes configuration validation functions
- Includes performance estimation functions

### 6. Configuration Validation

The configuration package includes validation functions:

```systemverilog
function automatic logic validate_cache_config(
    input integer cache_size,
    input integer line_size,
    input integer ways
);
    // Validates cache configuration parameters
    if ((cache_size & (cache_size - 1)) != 0) return 1'b0; // Must be power of 2
    if ((line_size & (line_size - 1)) != 0 || line_size < 4) return 1'b0;
    if ((ways & (ways - 1)) != 0) return 1'b0;
    if (cache_size < (line_size * ways)) return 1'b0;
    return 1'b1;
endfunction
```

### 7. Performance Estimation

The core package includes performance estimation functions:

```systemverilog
function automatic real calculate_estimated_area(
    input ooo_config_t ooo_cfg,
    input bp_config_t bp_cfg
);
    // Estimates area based on configuration
    real area = 0.0;
    area += ooo_cfg.rob_size * 100.0; // 100 gates per ROB entry
    area += ooo_cfg.rs_size * 150.0;  // 150 gates per RS entry
    // ... more calculations
    return area;
endfunction
```

### 8. Compilation Order

The test runner has been updated with the correct compilation order:

```python
self.rtl_sources = [
    # Configuration package (must be compiled first)
    str(self.rtl_dir / "core" / "riscv_config_pkg.sv"),
    # Exception package (depends on config)
    str(self.rtl_dir / "core" / "riscv_exception_pkg.sv"),
    # Core types package (depends on config and exception)
    str(self.rtl_dir / "core" / "riscv_types_pkg.sv"),
    # ... other packages in dependency order
    str(self.rtl_dir / "core" / "riscv_core_pkg.sv"),
]
```

## Benefits Achieved

### 1. Complete Flexibility
- Easy to switch between different configurations
- Support for multiple design targets (ASIC/FPGA)
- Configurable for different performance requirements

### 2. Maintainability
- Single source of truth for all parameters
- Clear dependency relationships
- Consistent parameter naming and documentation

### 3. Type Safety
- All parameters properly typed
- Validation functions prevent invalid configurations
- Compile-time parameter checking

### 4. Scalability
- Easy to add new parameters
- Support for configuration presets
- Performance estimation capabilities

### 5. Verification Support
- Configurable test parameters
- Support for different simulation scenarios
- Performance monitoring capabilities

## Usage Examples

### 1. Using Default Configuration
```systemverilog
import riscv_core_pkg::*;

module my_core (
    // Uses all default parameters from riscv_config_pkg
);
```

### 2. Using Small Configuration
```systemverilog
import riscv_core_pkg::*;

module small_core (
    // Override with small configuration
    parameter ooo_config_t OOO_CONFIG = SMALL_OOO_CONFIG,
    parameter bp_config_t BP_CONFIG = SMALL_BP_CONFIG
);
```

### 3. Custom Configuration
```systemverilog
import riscv_core_pkg::*;

module custom_core (
    // Define custom configuration
    parameter ooo_config_t OOO_CONFIG = '{
        rob_size: 48,
        rs_size: 24,
        phys_regs: 96,
        num_alu_units: 3,
        num_mult_units: 2,
        num_div_units: 1,
        div_latency: 32
    }
);
```

## Future Enhancements

### 1. Configuration Files
- Support for external configuration files
- Runtime configuration loading
- Configuration validation at startup

### 2. Advanced Validation
- Cross-parameter validation
- Performance constraint checking
- Power budget validation

### 3. Configuration Profiles
- Predefined profiles for common use cases
- Profile switching at runtime
- Profile inheritance and overriding

### 4. Documentation Generation
- Automatic parameter documentation
- Configuration dependency graphs
- Performance analysis reports

## Conclusion

The parameterization work provides a solid foundation for a flexible, maintainable, and scalable RISC-V processor design. The centralized configuration system eliminates hard-coded values and provides complete flexibility for different design targets and requirements.

The package hierarchy ensures proper dependencies and the validation functions prevent invalid configurations. The performance estimation capabilities help with design space exploration and optimization.

This parameterization system will be essential as the codebase grows and supports multiple design variants and target technologies.

---

**Document Version:** 1.0  
**Last Updated:** 2025-06-28  
**Author:** DesignAI  
**Status:** Complete 