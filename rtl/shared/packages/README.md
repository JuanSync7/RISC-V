# RISC-V SystemVerilog Packages

**Location:** `rtl/shared/packages/`  
**Purpose:** Comprehensive type definitions and constants  
**Files:** 13 SystemVerilog packages  
**Total Lines:** 2,486 lines of type definitions  
**Last Updated:** 2025-01-28

---

## Overview

This directory contains all SystemVerilog packages that define types, constants, and parameters used throughout the RISC-V implementation. These packages provide strong typing, consistent interfaces, and centralized parameter management across the entire system.

## Package Categories

### **Core System Packages**

| Package | Lines | Description |
|---------|-------|-------------|
| `riscv_core_pkg.sv` | 195 | Core instruction set, opcodes, register definitions |
| `riscv_core_types_pkg.sv` | 118 | Core pipeline data structures and control signals |
| `riscv_pipeline_types_pkg.sv` | 174 | Pipeline stage interfaces and control structures |
| `riscv_exception_pkg.sv` | 163 | Exception codes, handlers, and privilege levels |

### **Memory System Packages**

| Package | Lines | Description |
|---------|-------|-------------|
| `riscv_memory_types_pkg.sv` | 213 | Memory request/response types and cache interfaces |
| `riscv_cache_topology_pkg.sv` | 250 | Cache hierarchy configurations and replacement policies |
| `riscv_qos_pkg.sv` | 320 | Quality of Service types and priority management |

### **Advanced Features Packages**

| Package | Lines | Description |
|---------|-------|-------------|
| `riscv_ooo_types_pkg.sv` | 240 | Out-of-order execution structures (ROB, RS, PRF) |
| `riscv_bp_types_pkg.sv` | 257 | Branch predictor types and prediction structures |
| `riscv_inter_core_types_pkg.sv` | 317 | Multi-core communication and synchronization |

### **Protocol and Interface Packages**

| Package | Lines | Description |
|---------|-------|-------------|
| `riscv_protocol_types_pkg.sv` | 143 | Protocol interface types (AXI, CHI, TileLink) |
| `riscv_protocol_constants_pkg.sv` | 339 | Protocol constants, opcodes, and response codes |
| `riscv_verif_types_pkg.sv` | 117 | Verification and testbench support types |

---

## Key Package Details

### **Core Package (`riscv_core_pkg.sv`)**
**Purpose:** Fundamental RISC-V definitions

**Key Contents:**
```systemverilog
// RISC-V instruction formats
typedef enum logic [6:0] {
    OPCODE_LOAD     = 7'b0000011,
    OPCODE_STORE    = 7'b0100011,
    OPCODE_BRANCH   = 7'b1100011,
    OPCODE_JALR     = 7'b1100111,
    OPCODE_JAL      = 7'b1101111
} opcode_e;

// Register file definitions
typedef logic [4:0] reg_addr_t;
typedef logic [31:0] reg_data_t;
```

### **Memory Types Package (`riscv_memory_types_pkg.sv`)**
**Purpose:** Memory subsystem interface definitions

**Key Contents:**
```systemverilog
// Memory request structure
typedef struct packed {
    logic [31:0] addr;
    logic [63:0] wdata;
    logic [7:0]  be;
    logic        we;
    logic [2:0]  size;
    logic [3:0]  qos;
} memory_req_t;

// Cache line structure
typedef struct packed {
    logic [511:0] data;    // 64-byte cache line
    logic [2:0]   state;   // MOESI state
    logic [19:0]  tag;     // Address tag
    logic         valid;   // Valid bit
    logic         dirty;   // Dirty bit
} cache_line_t;
```

### **QoS Package (`riscv_qos_pkg.sv`)**
**Purpose:** Quality of Service management

**Key Contents:**
```systemverilog
// QoS priority levels
typedef enum logic [2:0] {
    QOS_CRITICAL = 3'b111,
    QOS_HIGH     = 3'b110,
    QOS_NORMAL   = 3'b100,
    QOS_LOW      = 3'b010,
    QOS_IDLE     = 3'b000
} qos_priority_e;

// QoS control structure
typedef struct packed {
    qos_priority_e priority;
    logic [7:0]    bandwidth_limit;
    logic [15:0]   latency_target;
    logic          bypass_enable;
} qos_control_t;
```

### **Out-of-Order Types (`riscv_ooo_types_pkg.sv`)**
**Purpose:** OoO execution support structures

**Key Contents:**
```systemverilog
// Reorder Buffer entry
typedef struct packed {
    logic [31:0] pc;
    logic [4:0]  rd_addr;
    logic [31:0] result;
    logic        ready;
    logic        exception;
    logic [4:0]  exception_code;
} rob_entry_t;

// Reservation Station entry
typedef struct packed {
    logic [31:0] operand_a;
    logic [31:0] operand_b;
    logic        operand_a_valid;
    logic        operand_b_valid;
    logic [3:0]  operation;
    logic [4:0]  dest_tag;
} rs_entry_t;
```

---

## Package Dependencies

### **Import Hierarchy**
```systemverilog
// Core system dependencies
riscv_core_pkg
    └── riscv_core_types_pkg
        └── riscv_pipeline_types_pkg
            └── riscv_exception_pkg

// Memory system dependencies
riscv_memory_types_pkg
    ├── riscv_cache_topology_pkg
    └── riscv_qos_pkg

// Advanced features
riscv_ooo_types_pkg
    ├── riscv_core_types_pkg
    └── riscv_bp_types_pkg

// Protocol system
riscv_protocol_types_pkg
    └── riscv_protocol_constants_pkg
```

### **Dependency Best Practices**
- **Minimal Dependencies:** Avoid circular dependencies
- **Layered Architecture:** Higher-level packages import lower-level ones
- **Explicit Imports:** Use explicit package imports in modules

---

## Usage Guidelines

### **Package Import Strategy**
```systemverilog
// Import only required packages
import riscv_core_pkg::*;
import riscv_memory_types_pkg::*;

module cache_controller (
    input  memory_req_t  mem_req,
    output cache_line_t  cache_line
);
    // Module implementation using imported types
endmodule
```

### **Type Safety Benefits**
```systemverilog
// Strong typing prevents errors
opcode_e current_opcode;
reg_addr_t source_reg, dest_reg;

// Compile-time type checking
always_comb begin
    case (current_opcode)
        OPCODE_LOAD:  // Handle load instruction
        OPCODE_STORE: // Handle store instruction
        default:      // Handle other instructions
    endcase
end
```

---

## Parameterization Strategy

### **Configurable Parameters**
```systemverilog
// Cache configuration parameters
parameter int CACHE_SIZE = 32 * 1024;    // 32KB
parameter int CACHE_WAYS = 4;            // 4-way associative
parameter int CACHE_LINE_SIZE = 64;      // 64-byte lines

// Derived parameters
localparam int CACHE_SETS = CACHE_SIZE / (CACHE_WAYS * CACHE_LINE_SIZE);
localparam int TAG_WIDTH = 32 - $clog2(CACHE_LINE_SIZE) - $clog2(CACHE_SETS);
```

### **Configuration Validation**
```systemverilog
// Parameter validation
initial begin
    assert (CACHE_SIZE > 0) 
        else $fatal("Cache size must be positive");
    assert ($onehot(CACHE_WAYS))
        else $fatal("Cache ways must be power of 2");
end
```

---

## Documentation Standards

### **Type Documentation**
```systemverilog
// Comprehensive type documentation
typedef struct packed {
    logic [31:0] addr;      // Memory address (word-aligned)
    logic [63:0] wdata;     // Write data (64-bit interface)
    logic [7:0]  be;        // Byte enable (active high)
    logic        we;        // Write enable (1=write, 0=read)
    logic [2:0]  size;      // Transfer size (0=byte, 1=half, 2=word, 3=double)
    logic [3:0]  qos;       // Quality of service (0=lowest, 15=highest)
} memory_req_t; // Memory request structure for cache interface
```

### **Enumeration Documentation**
```systemverilog
// Well-documented enumerations
typedef enum logic [2:0] {
    CACHE_INVALID  = 3'b000,  // Cache line is invalid
    CACHE_SHARED   = 3'b001,  // Cache line is shared (clean)
    CACHE_EXCLUSIVE = 3'b010, // Cache line is exclusive (clean)
    CACHE_OWNER    = 3'b011,  // Cache line is owned (possibly dirty)
    CACHE_MODIFIED = 3'b100   // Cache line is modified (dirty)
} cache_state_e; // MOESI cache coherency states
```

---

## Verification Support

### **Verification Types Package**
```systemverilog
// Testbench support structures
typedef struct packed {
    logic [31:0] test_vector_id;
    logic [63:0] expected_result;
    logic [63:0] actual_result;
    logic        pass;
    string       test_name;
} test_result_t;

// Coverage collection types
typedef struct packed {
    logic [31:0] instruction_count;
    logic [31:0] branch_count;
    logic [31:0] cache_hit_count;
    logic [31:0] cache_miss_count;
} coverage_stats_t;
```

---

## Future Enhancements

### **Package Evolution**
- [ ] Automated consistency checking across packages
- [ ] Enhanced documentation generation from types
- [ ] Machine-readable interface specifications
- [ ] Cross-package dependency analysis tools

### **Type System Extensions**
- [ ] Advanced constraint types for verification
- [ ] Configurable precision arithmetic types
- [ ] Enhanced debug information in types
- [ ] Formal verification friendly type definitions

---

**Document Version:** 1.0  
**Last Updated:** 2025-01-28  
**Maintainer:** RISC-V RTL Team  
**Status:** Complete 