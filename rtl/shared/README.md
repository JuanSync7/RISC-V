# RISC-V Shared Components

**Location:** `rtl/shared/`  
**Purpose:** Common interfaces and packages for system-wide reuse  
**Subdirectories:** 2 (interfaces, packages)  
**Total Files:** 19 SystemVerilog files  
**Total Lines:** 4,842 lines of shared code  
**Last Updated:** 2025-01-28

---

## Overview

This directory contains shared SystemVerilog components that are used throughout the RISC-V system implementation. It includes common interfaces for modular design and comprehensive type definition packages that ensure consistency across all modules.

## Directory Structure

```
shared/
├── interfaces/         # SystemVerilog interfaces (6 files)
│   ├── axi4_if.sv                     # AXI4 interface definition
│   ├── cache_coherency_if.sv          # Cache coherency interface
│   ├── chi_if.sv                      # CHI interface definition
│   ├── inter_core_comm_if.sv          # Inter-core communication
│   ├── memory_req_rsp_if.sv           # Memory request/response
│   ├── sync_primitives_if.sv          # Synchronization primitives
│   ├── tilelink_if.sv                 # TileLink interface
│   └── README.md                      # Interface documentation
├── packages/           # Type definition packages (13 files)
│   ├── riscv_bp_types_pkg.sv          # Branch predictor types
│   ├── riscv_cache_topology_pkg.sv    # Cache hierarchy types
│   ├── riscv_core_pkg.sv              # Core-specific types
│   ├── riscv_core_types_pkg.sv        # Core data types
│   ├── riscv_exception_pkg.sv         # Exception handling types
│   ├── riscv_inter_core_types_pkg.sv  # Inter-core communication
│   ├── riscv_memory_types_pkg.sv      # Memory subsystem types
│   ├── riscv_ooo_types_pkg.sv         # Out-of-order execution
│   ├── riscv_pipeline_types_pkg.sv    # Pipeline data types
│   ├── riscv_protocol_constants_pkg.sv # Protocol constants
│   ├── riscv_protocol_types_pkg.sv    # Protocol interface types
│   ├── riscv_qos_pkg.sv               # Quality of Service types
│   └── riscv_verif_types_pkg.sv       # Verification types
└── README.md           # This file
```

---

## SystemVerilog Interfaces (`interfaces/`)

### **Protocol Interfaces**

| Interface | Signals | Purpose | Features |
|-----------|---------|---------|----------|
| `axi4_if.sv` | 23 | AXI4 protocol abstraction | Full AXI4 compliance |
| `chi_if.sv` | 34 | CHI coherent interface | MOESI coherency support |
| `tilelink_if.sv` | 16 | TileLink protocol | Credit-based flow control |

### **Memory System Interfaces**

| Interface | Signals | Purpose | Features |
|-----------|---------|---------|----------|
| `memory_req_rsp_if.sv` | 12 | Generic memory abstraction | Protocol-agnostic design |
| `cache_coherency_if.sv` | 18 | Cache coherency operations | Snoop and invalidate support |

### **System Interfaces**

| Interface | Signals | Purpose | Features |
|-----------|---------|---------|----------|
| `inter_core_comm_if.sv` | 8 | Inter-core communication | Message passing, barriers |
| `sync_primitives_if.sv` | 6 | Synchronization support | Mutexes, semaphores |

---

## Type Definition Packages (`packages/`)

### **Core System Types**

| Package | Lines | Purpose | Key Types |
|---------|-------|---------|-----------|
| `riscv_core_pkg.sv` | 195 | Core definitions | Instructions, registers, opcodes |
| `riscv_core_types_pkg.sv` | 118 | Core data types | Pipeline registers, control signals |
| `riscv_pipeline_types_pkg.sv` | 174 | Pipeline structures | Stage interfaces, hazard types |

### **Memory System Types**

| Package | Lines | Purpose | Key Types |
|---------|-------|---------|-----------|
| `riscv_memory_types_pkg.sv` | 213 | Memory interfaces | Cache requests, memory commands |
| `riscv_cache_topology_pkg.sv` | 250 | Cache hierarchies | Cache configurations, topologies |
| `riscv_qos_pkg.sv` | 320 | Quality of Service | Priority levels, QoS policies |

### **Advanced Feature Types**

| Package | Lines | Purpose | Key Types |
|---------|-------|---------|-----------|
| `riscv_ooo_types_pkg.sv` | 240 | Out-of-order execution | ROB entries, reservation stations |
| `riscv_bp_types_pkg.sv` | 257 | Branch prediction | Predictor states, history tables |
| `riscv_exception_pkg.sv` | 163 | Exception handling | Exception codes, handler states |

### **Protocol and Communication Types**

| Package | Lines | Purpose | Key Types |
|---------|-------|---------|-----------|
| `riscv_protocol_types_pkg.sv` | 143 | Protocol interfaces | AXI, CHI, TileLink types |
| `riscv_protocol_constants_pkg.sv` | 339 | Protocol constants | Opcodes, response codes |
| `riscv_inter_core_types_pkg.sv` | 317 | Multi-core communication | Message types, barriers |

---

## Design Principles

### **Interface Design Philosophy**
- **Modular Interfaces:** Clean separation of concerns
- **Protocol Abstraction:** Hide protocol complexity from modules
- **Parameterizable:** Configurable widths and features
- **Verification Friendly:** Built-in assertions and checkers

### **Package Organization**
- **Hierarchical Structure:** Logical grouping of related types
- **Minimal Dependencies:** Reduced compilation dependencies
- **Consistent Naming:** Standardized naming conventions
- **Documentation:** Comprehensive inline documentation

---

## Usage Guidelines

### **Interface Usage**
```systemverilog
// Import interface package
import riscv_memory_types_pkg::*;

// Use interface in module
module memory_controller (
    memory_req_rsp_if.slave mem_if,
    axi4_if.master axi_if
);
    // Module implementation
endmodule
```

### **Package Import Strategy**
```systemverilog
// Import only required packages
import riscv_core_types_pkg::*;
import riscv_pipeline_types_pkg::*;

// Use imported types
pipeline_reg_t if_id_reg;
control_signals_t ctrl_signals;
```

---

## Interface Verification

### **Built-in Assertions**
- **Protocol Compliance:** Interface protocol checking
- **Timing Verification:** Setup/hold time validation
- **Data Integrity:** End-to-end data checking

### **SVA Properties**
```systemverilog
// Example assertion in memory interface
property valid_request;
    @(posedge clk) req_valid |-> ##[1:10] req_ready;
endproperty

assert property (valid_request) 
    else $error("Request not acknowledged within timeout");
```

---

## Package Dependencies

### **Dependency Graph**
```
riscv_core_pkg
    ├── riscv_core_types_pkg
    ├── riscv_pipeline_types_pkg
    └── riscv_exception_pkg

riscv_memory_types_pkg
    ├── riscv_cache_topology_pkg
    └── riscv_qos_pkg

riscv_protocol_types_pkg
    ├── riscv_protocol_constants_pkg
    └── riscv_qos_pkg
```

---

## Integration Benefits

### **Code Reuse**
- **Common Interfaces:** Consistent interfaces across modules
- **Type Safety:** Strong typing prevents integration errors
- **Parameterization:** Single interface supports multiple configurations

### **Maintenance**
- **Centralized Changes:** Interface changes propagate automatically
- **Version Control:** Controlled evolution of interfaces
- **Documentation:** Self-documenting interface definitions

### **Verification**
- **Consistent Checkers:** Reusable verification components
- **Protocol Monitors:** Built-in protocol checking
- **Coverage Collection:** Standardized coverage metrics

---

## Future Enhancements

### **Interface Extensions**
- [ ] Advanced debugging interfaces
- [ ] Power management interface extensions
- [ ] Performance monitoring interfaces
- [ ] Security and trust interface support

### **Package Improvements**
- [ ] Automated documentation generation
- [ ] Enhanced type checking capabilities
- [ ] Cross-package consistency validation
- [ ] Machine-readable interface specifications

---

**Document Version:** 1.0  
**Last Updated:** 2025-01-28  
**Maintainer:** RISC-V RTL Team  
**Status:** Complete 