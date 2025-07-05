# RISC-V Configuration Packages

**Location:** `rtl/config/`  
**Purpose:** Centralized configuration parameters and constants  
**Files:** 6 SystemVerilog packages  
**Total Lines:** 2,756 lines of configuration code  
**Last Updated:** 2025-07-05

---

## Overview

This directory contains all configuration packages that define parameters, constants, and settings for the RISC-V processor implementation. These packages provide centralized configuration management across all subsystems, enabling easy customization and scaling of the processor design.

## Directory Structure

```
config/
└── core/
    ├── riscv_config_pkg.sv                 # Core configuration parameters
    ├── riscv_core_config_pkg.sv            # Core-specific settings
    ├── riscv_memory_config_pkg.sv          # Memory subsystem configuration
    ├── riscv_pipeline_config_pkg.sv        # Pipeline configuration
    ├── riscv_soc_config_pkg.sv             # SoC-level configuration
    └── riscv_verification_config_pkg.sv    # Verification configuration
```

---

## Configuration Packages

### **Core Configuration (`riscv_config_pkg.sv`)**
**Size:** 72 lines | **Purpose:** Global processor settings

**Key Parameters:**
- `XLEN`: Data width (32-bit)
- `RESET_VECTOR`: Boot address (0x80000000)
- `ISA_EXTENSIONS`: Supported extensions (RV32IM)
- `VENDOR_ID`: Implementation identifier

```systemverilog
// Core architecture parameters
parameter int XLEN = 32;
parameter logic [31:0] RESET_VECTOR = 32'h80000000;
parameter string ISA_STRING = "RV32IM";
```

### **Core-Specific Configuration (`riscv_core_config_pkg.sv`)**
**Size:** 67 lines | **Purpose:** Core implementation details

**Key Parameters:**
- `NUM_CORES`: Multi-core configuration
- `HART_ID_WIDTH`: Hardware thread ID width
- `PRIVILEGE_LEVELS`: Supported privilege modes
- `DEBUG_SUPPORT`: Debug interface enable

### **Memory Configuration (`riscv_memory_config_pkg.sv`)**
**Size:** 192 lines | **Purpose:** Memory subsystem parameters

**Key Parameters:**
- `L1_ICACHE_SIZE`: L1 instruction cache size (32KB)
- `L1_DCACHE_SIZE`: L1 data cache size (32KB)
- `L2_CACHE_SIZE`: L2 shared cache size (256KB)
- `L3_CACHE_SIZE`: L3 last-level cache size (2MB)
- `CACHE_LINE_SIZE`: Cache line width (64 bytes)
- `TLB_ENTRIES`: Translation lookaside buffer size

```systemverilog
// Cache hierarchy configuration
parameter int L1_ICACHE_SIZE = 32 * 1024;    // 32KB
parameter int L1_DCACHE_SIZE = 32 * 1024;    // 32KB
parameter int L2_CACHE_SIZE = 256 * 1024;    // 256KB
parameter int L3_CACHE_SIZE = 2 * 1024 * 1024; // 2MB
parameter int CACHE_LINE_SIZE = 64;          // 64 bytes
```

### **Pipeline Configuration (`riscv_pipeline_config_pkg.sv`)**
**Size:** 108 lines | **Purpose:** Pipeline behavior settings

**Key Parameters:**
- `PIPELINE_STAGES`: Number of pipeline stages (5)
- `FETCH_WIDTH`: Instructions fetched per cycle
- `DISPATCH_WIDTH`: Instructions dispatched per cycle
- `ROB_ENTRIES`: Reorder buffer depth (32)
- `RESERVATION_STATIONS`: Issue queue sizes

### **SoC Configuration (`riscv_soc_config_pkg.sv`)**
**Size:** 206 lines | **Purpose:** System-on-Chip integration

**Key Parameters:**
- `NUM_MASTERS`: Number of bus masters
- `NUM_SLAVES`: Number of bus slaves
- `INTERCONNECT_TYPE`: Bus interconnect selection
- `PERIPHERAL_BASE`: Peripheral address range
- `MEMORY_MAP`: System memory layout

```systemverilog
// SoC integration parameters
parameter int NUM_MASTERS = 4;
parameter int NUM_SLAVES = 8;
parameter logic [31:0] PERIPHERAL_BASE = 32'h40000000;
parameter logic [31:0] MEMORY_BASE = 32'h80000000;
```

### **Verification Configuration (`riscv_verification_config_pkg.sv`)**
**Size:** 119 lines | **Purpose:** Testbench and verification settings

**Key Parameters:**
- `TEST_VECTORS`: Number of test cases
- `COVERAGE_TARGETS`: Coverage thresholds
- `ASSERTION_LEVELS`: Assertion verbosity
- `RANDOM_SEED`: Simulation randomization

---

## Configuration Categories

### **Performance Parameters**
- Pipeline depth and width
- Cache sizes and associativity
- Branch predictor configuration
- Out-of-order execution limits

### **Memory System**
- Cache hierarchy definition
- Memory interface protocols
- Coherency protocol settings
- QoS parameter ranges

### **System Integration**
- Multi-core topology
- Interconnect configuration
- Peripheral interfaces
- Debug and trace settings

### **Verification Support**
- Test environment parameters
- Coverage collection settings
- Assertion configuration
- Debug visibility controls

---

## Usage Guidelines

### **Parameter Override**
Configuration parameters can be overridden at compile time:

```bash
# Override cache size during synthesis
vcs +define+L1_ICACHE_SIZE=16384 +define+L2_CACHE_SIZE=131072
```

### **Build-Time Configuration**
Different configurations for different targets:

```systemverilog
`ifdef FPGA_TARGET
    parameter int L2_CACHE_SIZE = 128 * 1024;  // Smaller for FPGA
`else
    parameter int L2_CACHE_SIZE = 256 * 1024;  // Full size for ASIC
`endif
```

### **Runtime Configuration**
Some parameters support runtime modification via CSRs:
- Performance monitoring enables
- Cache replacement policies
- Power management settings
- QoS parameters

---

## Configuration Validation

### **Parameter Checking**
Built-in parameter validation ensures consistent configuration:

```systemverilog
// Validate cache line alignment
initial begin
    assert (CACHE_LINE_SIZE inside {32, 64, 128})
        else $fatal(1, "Invalid cache line size");
    assert ($clog2(L1_ICACHE_SIZE) >= $clog2(CACHE_LINE_SIZE))
        else $fatal(1, "Cache size must be >= cache line size");
end
```

### **Configuration Reports**
Generate configuration summary during elaboration:
- Parameter values used
- Derived parameters calculated
- Resource requirements estimated
- Performance projections

---

## Integration Notes

### **Package Dependencies**
Configuration packages are imported by:
- All RTL modules requiring parameters
- Verification testbenches
- Synthesis scripts
- Documentation generators

### **Build System Integration**
- Makefile targets for different configurations
- CI/CD parameter validation
- Configuration-specific regression tests
- Performance benchmarking per configuration

---

## Customization Guide

### **Creating New Configurations**
1. **Copy Base Package**: Start from similar existing package
2. **Modify Parameters**: Update parameters for target requirements
3. **Validate Settings**: Run parameter validation checks
4. **Update Documentation**: Document configuration purpose and usage
5. **Test Configuration**: Run regression tests with new settings

### **Configuration Best Practices**
- Use meaningful parameter names
- Include parameter validation
- Document parameter interactions
- Provide usage examples
- Test parameter boundary conditions

---

## Future Enhancements

### **Planned Features**
- [ ] Dynamic configuration loading
- [ ] Configuration file parsing (JSON/YAML)
- [ ] Runtime parameter modification
- [ ] Configuration optimization automation
- [ ] Cross-configuration validation

### **Scalability Improvements**
- [ ] Multi-cluster configuration support
- [ ] Heterogeneous core configurations
- [ ] Advanced memory topologies
- [ ] Custom ISA extension configuration

---

**Document Version:** 1.0  
**Last Updated:** 2025-01-28  
**Maintainer:** RISC-V RTL Team  
**Status:** Complete 