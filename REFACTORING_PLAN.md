# RISC-V Core Refactoring Plan

## Executive Summary
This document outlines a comprehensive refactoring plan to improve the flexibility, modularity, and scalability of the 32MI RISC-V project through enhanced parameterization and package organization.

## Current State Analysis

### Issues Identified
1. **Monolithic Configuration**: All configuration parameters are in a single large package (`riscv_config_pkg.sv`)
2. **Limited Flexibility**: Difficult to create different configurations for various use cases
3. **Parameter Coupling**: Many parameters are interdependent without clear relationships
4. **No Configuration Profiles**: No easy way to switch between small/large or FPGA/ASIC configurations
5. **Interface Proliferation**: Multiple interface types without clear hierarchy

## Proposed Refactoring Strategy

### 1. Hierarchical Configuration Architecture

```
Configuration Hierarchy:
├── Base Configuration Layer
│   ├── riscv_base_pkg.sv          # RISC-V ISA constants
│   ├── riscv_types_pkg.sv         # Basic type definitions
│   └── riscv_constants_pkg.sv     # Architecture constants
├── Domain Configuration Layer
│   ├── riscv_core_config_pkg.sv   # Core-specific parameters
│   ├── riscv_cache_config_pkg.sv  # Cache system parameters
│   ├── riscv_memory_config_pkg.sv # Memory subsystem parameters
│   ├── riscv_ooo_config_pkg.sv    # Out-of-order parameters
│   └── riscv_debug_config_pkg.sv  # Debug/verification parameters
├── Profile Configuration Layer
│   ├── riscv_profile_small.sv     # Small FPGA configuration
│   ├── riscv_profile_medium.sv    # Medium configuration
│   ├── riscv_profile_large.sv     # Large ASIC configuration
│   └── riscv_profile_custom.sv    # User-defined configuration
└── Top-Level Configuration
    └── riscv_system_config_pkg.sv # System-wide configuration selection
```

### 2. Parameter Classification

#### A. Static Parameters (Compile-time constants)
- ISA encoding constants
- Architectural limits
- Protocol constants

#### B. Configurable Parameters (Design-time configurable)
- Cache sizes and associativity
- Pipeline depth
- Number of cores
- Feature enables

#### C. Derived Parameters (Calculated from configurable)
- Address width calculations
- Index/tag bit calculations
- Buffer sizes based on latency

### 3. Configuration Profiles

#### Small Profile (FPGA/Embedded)
```systemverilog
package riscv_profile_small;
    parameter int unsigned CONFIG_NUM_CORES = 1;
    parameter int unsigned CONFIG_L1_CACHE_SIZE = 8*1024;  // 8KB
    parameter int unsigned CONFIG_L2_CACHE_SIZE = 64*1024; // 64KB
    parameter string CONFIG_EXECUTION_MODE = "IN_ORDER";
    parameter string CONFIG_BRANCH_PREDICTOR = "BIMODAL";
endpackage
```

#### Large Profile (High-Performance ASIC)
```systemverilog
package riscv_profile_large;
    parameter int unsigned CONFIG_NUM_CORES = 4;
    parameter int unsigned CONFIG_L1_CACHE_SIZE = 64*1024;   // 64KB
    parameter int unsigned CONFIG_L2_CACHE_SIZE = 512*1024;  // 512KB
    parameter int unsigned CONFIG_L3_CACHE_SIZE = 8*1024*1024; // 8MB
    parameter string CONFIG_EXECUTION_MODE = "OUT_OF_ORDER";
    parameter string CONFIG_BRANCH_PREDICTOR = "TOURNAMENT";
endpackage
```

### 4. Interface Standardization

Create a unified interface hierarchy:
```systemverilog
// Base memory interface
interface memory_if #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
);

// Specialized interfaces inherit from base
interface axi4_if #(...) extends memory_if;
interface chi_if #(...) extends memory_if;
interface tilelink_if #(...) extends memory_if;
```

### 5. Module Parameterization Enhancement

Example of improved module parameterization:
```systemverilog
module riscv_core_flexible
import riscv_base_pkg::*;
import riscv_system_config_pkg::*;
#(
    // Override system defaults if needed
    parameter int unsigned CORE_ID = 0,
    parameter core_config_t CORE_CONFIG = DEFAULT_CORE_CONFIG,
    parameter cache_config_t CACHE_CONFIG = DEFAULT_CACHE_CONFIG,
    parameter debug_config_t DEBUG_CONFIG = DEFAULT_DEBUG_CONFIG
)
```

### 6. Configuration Validation

Add compile-time validation:
```systemverilog
// In riscv_system_config_pkg
initial begin
    assert(validate_cache_config(CACHE_CONFIG)) 
        else $fatal("Invalid cache configuration");
    assert(validate_core_config(CORE_CONFIG)) 
        else $fatal("Invalid core configuration");
end
```

## Implementation Steps

### Phase 1: Package Restructuring (Week 1)
1. Create new package hierarchy
2. Move constants to appropriate packages
3. Define configuration structures
4. Create profile packages

### Phase 2: Module Updates (Week 2-3)
1. Update module parameters to use new packages
2. Replace hardcoded values with parameters
3. Add configuration validation
4. Update instantiation templates

### Phase 3: Interface Refactoring (Week 4)
1. Create base interface definitions
2. Update existing interfaces
3. Add interface adapters where needed
4. Update module ports

### Phase 4: Testing and Validation (Week 5-6)
1. Create configuration test suite
2. Validate all profiles
3. Performance regression testing
4. Documentation updates

## Benefits

1. **Flexibility**: Easy to create new configurations
2. **Maintainability**: Clear parameter organization
3. **Scalability**: Support for various system sizes
4. **Reusability**: Modular configuration approach
5. **Validation**: Built-in configuration checking

## Migration Guide

For existing users:
1. Current parameters remain available through compatibility layer
2. Gradual migration path provided
3. Automated script to convert old configurations
4. Comprehensive documentation and examples

## Risk Mitigation

1. **Backward Compatibility**: Maintain wrapper packages
2. **Testing**: Comprehensive regression suite
3. **Documentation**: Detailed migration guides
4. **Phased Rollout**: Gradual implementation

## Success Metrics

1. Reduced configuration time for new designs
2. Increased parameter reuse across projects
3. Fewer configuration-related bugs
4. Improved synthesis results through better parameterization

## Next Steps

1. Review and approve this plan
2. Set up new package structure
3. Begin Phase 1 implementation
4. Create migration documentation