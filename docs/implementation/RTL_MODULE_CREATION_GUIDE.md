# RTL Module Creation Guide

## Overview

This guide provides a comprehensive step-by-step approach for creating RTL modules within the RISC-V processor design. It covers package dependencies, interface usage, design patterns, and best practices based on the current codebase structure.

## Table of Contents

- [Package Dependency Management](#package-dependency-management)
- [Module Creation Checklist](#module-creation-checklist)
- [Interface Integration](#interface-integration)
- [Design Patterns](#design-patterns)
- [Code Quality Standards](#code-quality-standards)
- [Verification Considerations](#verification-considerations)
- [Examples](#examples)
- [Common Pitfalls](#common-pitfalls)
- [Configuration Parameter Usage](#configuration-parameter-usage)

## Package Dependency Management

### 1. Understanding the Package Hierarchy

The RISC-V design uses a hierarchical package system with clear dependencies:

```
riscv_config_pkg (Base Configuration)
    ↓
riscv_types_pkg (Core Types)
    ↓
Specialized Packages:
├── riscv_exception_pkg
├── riscv_cache_types_pkg
├── riscv_bp_types_pkg
├── riscv_mem_types_pkg
├── riscv_ooo_types_pkg
├── riscv_protocol_types_pkg
└── riscv_verif_types_pkg
    ↓
riscv_core_pkg (Top-level Package)
```

### 1.1. Configuration Package Contents

The `riscv_config_pkg` contains all centralized parameters including:

- **Execution Mode Configuration**: `DEFAULT_EXECUTION_MODE` ("IN_ORDER" or "OUT_OF_ORDER")
- **Branch Predictor Configuration**: `DEFAULT_BRANCH_PREDICTOR_TYPE` ("STATIC", "DYNAMIC", "TOURNAMENT")
- **Architectural Parameters**: `XLEN`, `ADDR_WIDTH`, `REG_COUNT`, etc.
- **Cache Configuration**: Cache sizes, associativity, line sizes
- **Multi-core Parameters**: `DEFAULT_NUM_CORES`, `MAX_CORES`
- **Performance Parameters**: Latencies, buffer sizes, etc.

**Important Note**: The `EXECUTION_MODE` and `BRANCH_PREDICTOR_TYPE` parameters have been centralized in the configuration package to ensure consistency across the design. Always use the defaults from the configuration package rather than defining them locally in individual modules.

### 1.2. Avoiding Interface Hardcoding

A common issue is hardcoding interface connections instead of using proper interface types and modports. Here's how to avoid this:

**❌ Wrong - Hardcoded Interface Signals:**
```systemverilog
module bad_example (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Hardcoded memory interface signals
    output logic        mem_req_valid,
    output logic [31:0] mem_req_addr,
    output logic        mem_req_write,
    output logic [31:0] mem_req_data,
    input  logic        mem_req_ready,
    input  logic        mem_rsp_valid,
    input  logic [31:0] mem_rsp_data
);
```

**✅ Correct - Using Interface:**
```systemverilog
module good_example (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Proper interface usage
    memory_req_rsp_if.master mem_if
);
```

**Benefits of Using Interfaces:**
- Type safety and consistency
- Easier to maintain and modify
- Clear protocol definition
- Better verification support
- Reduced connection errors

### 2. Package Import Rules

**Rule 1: Always import `riscv_config_pkg` first**
- Contains all parameterized values and constants
- Must be imported before any other package that uses these parameters

**Rule 2: Import packages in dependency order**
```systemverilog
import riscv_config_pkg::*;      // Always first
import riscv_types_pkg::*;       // Core types second
import riscv_exception_pkg::*;   // Specialized packages as needed
```

**Rule 3: Use selective imports when possible**
```systemverilog
// Preferred for large packages
import riscv_config_pkg::XLEN, DEFAULT_RESET_VECTOR;

// Use wildcard only when many symbols are needed
import riscv_types_pkg::*;
```

### 3. Package Dependency Verification

Before creating a module, verify package dependencies:

```bash
# Check package compilation order
grep -r "import.*pkg" rtl/ | sort
```

## Module Creation Checklist

### Phase 1: Planning and Design

- [ ] **Define Module Purpose**
  - [ ] Identify the specific function the module will perform
  - [ ] Determine if it's a pipeline stage, functional unit, or interface adapter
  - [ ] Document the problem it solves

- [ ] **Analyze Dependencies**
  - [ ] List required packages based on functionality
  - [ ] Identify interface requirements
  - [ ] Check for existing similar modules to reuse patterns

- [ ] **Parameter Planning**
  - [ ] Use existing parameters from `riscv_config_pkg` when possible
  - [ ] Define new parameters only if absolutely necessary
  - [ ] Ensure parameter names follow `UPPER_CASE_SNAKE_CASE` convention

### Phase 2: Interface Design

- [ ] **Port Definition**
  - [ ] Follow naming conventions (`_i`, `_o`, `_io` suffixes)
  - [ ] Use parameterized widths (e.g., `[XLEN-1:0]`)
  - [ ] Group related ports logically

- [ ] **Interface Usage**
  - [ ] Check if existing interfaces can be used
  - [ ] Use `memory_req_rsp_if` for memory operations
  - [ ] Use specialized interfaces for multi-core features

- [ ] **Clock and Reset**
  - [ ] Use standard `clk_i` and `rst_ni` naming
  - [ ] Document clock domain requirements
  - [ ] Plan CDC strategies if multiple domains

### Phase 3: Implementation

- [ ] **File Structure**
  - [ ] Use standard file header with all required fields
  - [ ] Include `AI_TAG` comments for documentation generation
  - [ ] Follow the established formatting style

- [ ] **Module Declaration**
  - [ ] Use ANSI-style port declarations
  - [ ] Parameter defaults from configuration package
  - [ ] Proper parameter typing (`integer`, `string`, etc.)

- [ ] **Internal Architecture**
  - [ ] Use `always_ff` for sequential logic
  - [ ] Use `always_comb` for combinational logic
  - [ ] Avoid latches through complete case coverage

### Phase 4: Integration and Testing

- [ ] **Module Instantiation**
  - [ ] Verify all sub-module packages are imported
  - [ ] Use proper instance naming (`u_module_name`)
  - [ ] Connect interfaces correctly with proper modports

- [ ] **Compilation Check**
  - [ ] Add to compilation order in testbench scripts
  - [ ] Verify no circular dependencies
  - [ ] Check for lint warnings

## Interface Integration

### 1. Memory Interface Usage

For modules that need memory access:

```systemverilog
module my_memory_module (
    input  logic clk_i,
    input  logic rst_ni,
    
    // Use standard memory interface
    memory_req_rsp_if.master mem_if,
    
    // Other ports...
);
```

**Key Points:**
- Always use `.master` modport for initiating requests
- Handle backpressure with `req_ready` and `rsp_valid`
- Use burst transactions for cache line operations

### 2. Multi-Core Interface Integration

For multi-core features:

```systemverilog
module multi_core_module #(
    parameter integer NUM_CORES = DEFAULT_NUM_CORES
) (
    input  logic clk_i,
    input  logic rst_ni,
    
    // Inter-core communication
    inter_core_comm_if.core comm_if [NUM_CORES],
    
    // Cache coherency
    cache_coherency_if.l1_cache_port coherency_if [NUM_CORES],
    
    // Synchronization primitives
    sync_primitives_if.manager sync_if
);
```

**Key Points:**
- Use array interfaces for per-core connections
- Choose correct modport based on module role
- Handle NUM_CORES parameterization consistently

### 3. Custom Interface Creation

When creating new interfaces:

```systemverilog
interface my_custom_if #(
    parameter integer DATA_WIDTH = XLEN
) (
    input logic clk,
    input logic rst_n
);
    
    // Signal declarations
    logic [DATA_WIDTH-1:0] data;
    logic                  valid;
    logic                  ready;
    
    // Modports
    modport master (
        output data, valid,
        input  ready,
        input  clk, rst_n
    );
    
    modport slave (
        input  data, valid,
        output ready,
        input  clk, rst_n
    );
    
endinterface : my_custom_if
```

## Design Patterns

### 1. Pipeline Stage Pattern

```systemverilog
module pipeline_stage #(
    parameter integer STAGE_ID = 0
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Pipeline control
    input  logic        stall_i,
    input  logic        flush_i,
    
    // Stage input/output registers
    input  stage_reg_t  prev_stage_reg_i,
    output stage_reg_t  next_stage_reg_o,
    
    // Stage-specific interfaces
    // ...
);

    // Stage register
    stage_reg_t stage_reg_q, stage_reg_d;
    
    // Sequential logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            stage_reg_q <= '0;
        end else if (flush_i) begin
            stage_reg_q <= '0;  // Clear on flush
        end else if (!stall_i) begin
            stage_reg_q <= stage_reg_d;
        end
        // Hold current value on stall
    end
    
    // Combinational logic
    always_comb begin
        stage_reg_d = prev_stage_reg_i;
        // Stage-specific processing...
    end
    
    assign next_stage_reg_o = stage_reg_q;

endmodule
```

### 2. Functional Unit Pattern

```systemverilog
module functional_unit #(
    parameter integer LATENCY = DEFAULT_LATENCY
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Control interface
    input  logic        start_i,
    input  logic [2:0]  op_type_i,
    input  word_t       operand_a_i,
    input  word_t       operand_b_i,
    
    // Result interface
    output word_t       result_o,
    output logic        done_o,
    output logic        exception_valid_o,
    output logic [31:0] exception_cause_o
);

    // Pipeline registers for latency
    logic [LATENCY-1:0] busy_q;
    
    // Operation pipeline
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            busy_q <= '0;
        end else begin
            busy_q <= {busy_q[LATENCY-2:0], start_i};
        end
    end
    
    assign done_o = busy_q[LATENCY-1];

endmodule
```

### 3. State Machine Pattern

```systemverilog
module state_machine (
    input  logic clk_i,
    input  logic rst_ni,
    // ...
);

    // State enumeration
    typedef enum logic [2:0] {
        S_IDLE    = 3'b000,
        S_ACTIVE  = 3'b001,
        S_WAIT    = 3'b010,
        S_DONE    = 3'b011
    } state_e;
    
    state_e current_state_q, next_state_c;
    
    // State register
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            current_state_q <= S_IDLE;
        end else begin
            current_state_q <= next_state_c;
        end
    end
    
    // Next state logic
    always_comb begin
        next_state_c = current_state_q;  // Default: hold state
        
        case (current_state_q)
            S_IDLE: begin
                if (start_condition) begin
                    next_state_c = S_ACTIVE;
                end
            end
            
            S_ACTIVE: begin
                if (completion_condition) begin
                    next_state_c = S_DONE;
                end else if (wait_condition) begin
                    next_state_c = S_WAIT;
                end
            end
            
            // ... other states
            
            default: begin
                next_state_c = S_IDLE;  // Safe default
            end
        endcase
    end
    
    // Output logic
    always_comb begin
        // Default outputs
        output_signal = 1'b0;
        
        case (current_state_q)
            S_ACTIVE: begin
                output_signal = 1'b1;
            end
            // ... other states
        endcase
    end

endmodule
```

## Code Quality Standards

### 1. Documentation Requirements

**File Header:**
```systemverilog
//=============================================================================
// Company: Sondrel Ltd
// Author: [Your Name] ([email])
// Created: YYYY-MM-DD
//
// File: module_name.sv
// Module: module_name
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   [Detailed description of module purpose and functionality]
//=============================================================================
```

**AI Tags for Documentation:**
```systemverilog
// AI_TAG: FEATURE - [Description of key feature]
// AI_TAG: PARAM_DESC - [Parameter description]
// AI_TAG: PORT_DESC - [Port description]
// AI_TAG: INTERNAL_BLOCK - [Internal block description]
```

### 2. Naming Conventions

**Signals:**
- `_i` for inputs
- `_o` for outputs
- `_io` for bidirectional
- `_q` for registered signals
- `_c` or `_ns` for combinational/next-state
- `clk_` prefix for clocks
- `rst_n` for active-low reset

**Parameters:**
- `UPPER_CASE_SNAKE_CASE`
- Use existing parameters from config package
- Type parameters explicitly: `parameter integer DATA_WIDTH = 32`

**Instances:**
- `u_module_name` for unique instances
- `gen_purpose[i].u_instance` for generated instances

### 3. Coding Standards

**Always Blocks:**
```systemverilog
// Sequential logic
always_ff @(posedge clk_i or negedge rst_ni) begin : proc_register_name
    if (!rst_ni) begin
        signal_q <= '0;
    end else begin
        signal_q <= signal_d;
    end
end

// Combinational logic
always_comb begin : proc_combinational_name
    signal_c = default_value;
    
    case (select_signal)
        VALUE1: signal_c = result1;
        VALUE2: signal_c = result2;
        default: signal_c = default_value;
    endcase
end
```

**Interface Connections:**
```systemverilog
// Correct interface instantiation
memory_req_rsp_if mem_if();

// Correct module connection
my_module u_my_module (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .mem_if(mem_if.master),  // Use proper modport
    .data_i(data_signal)
);
```

## Verification Considerations

### 1. Testability Features

- Add debug ports for internal state observation
- Include performance counters where appropriate
- Provide clear error signaling
- Support for assertion-based verification

### 2. Assertion Integration

```systemverilog
// Protocol compliance
assert property (@(posedge clk_i) disable iff (!rst_ni)
    req_valid && !req_ready |=> req_valid);

// Functional correctness
assert property (@(posedge clk_i) disable iff (!rst_ni)
    start_i |-> ##[1:MAX_LATENCY] done_o);
```

### 3. Coverage Points

- State machine state coverage
- Parameter value coverage
- Interface protocol coverage
- Error condition coverage

## Examples

### 1. Simple Functional Unit

```systemverilog
module simple_alu #(
    parameter integer DATA_WIDTH = XLEN
) (
    input  logic                    clk_i,
    input  logic                    rst_ni,
    
    input  logic [3:0]              alu_op_i,
    input  logic [DATA_WIDTH-1:0]   operand_a_i,
    input  logic [DATA_WIDTH-1:0]   operand_b_i,
    input  logic                    valid_i,
    
    output logic [DATA_WIDTH-1:0]   result_o,
    output logic                    valid_o,
    output logic                    overflow_o
);

import riscv_config_pkg::*;
import riscv_types_pkg::*;

// Implementation...

endmodule
```

### 2. Pipeline Stage with Interface

```systemverilog
module decode_stage #(
    parameter addr_t RESET_VECTOR = DEFAULT_RESET_VECTOR
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Pipeline control
    input  logic        stall_i,
    input  logic        flush_i,
    
    // Register file interface
    output logic [4:0]  rs1_addr_o,
    output logic [4:0]  rs2_addr_o,
    input  word_t       rs1_data_i,
    input  word_t       rs2_data_i,
    
    // Memory interface for instruction fetch
    memory_req_rsp_if.master imem_if
);

import riscv_config_pkg::*;
import riscv_types_pkg::*;
import riscv_core_pkg::*;

// Implementation...

endmodule
```

## Common Pitfalls

### 1. Package Import Issues

**❌ Wrong:**
```systemverilog
// Missing config package import
import riscv_types_pkg::*;
parameter integer WIDTH = 32;  // Hard-coded instead of XLEN
```

**✅ Correct:**
```systemverilog
import riscv_config_pkg::*;  // Import config first
import riscv_types_pkg::*;
parameter integer WIDTH = XLEN;  // Use parameterized value
```

### 2. Interface Connection Errors

**❌ Wrong:**
```systemverilog
// Missing modport specification
my_module u_module (
    .mem_if(mem_if)  // Ambiguous connection
);
```

**✅ Correct:**
```systemverilog
// Clear modport specification
my_module u_module (
    .mem_if(mem_if.master)  // Clear role
);
```

### 3. Parameter Override Issues

**❌ Wrong:**
```systemverilog
// Hard-coded parameter override
my_module #(.DATA_WIDTH(32)) u_module (...);
```

**✅ Correct:**
```systemverilog
// Use parameterized value
my_module #(.DATA_WIDTH(XLEN)) u_module (...);
```

### 4. Reset Logic Errors

**❌ Wrong:**
```systemverilog
always_ff @(posedge clk_i) begin
    if (rst_ni) begin  // Wrong polarity
        signal_q <= '0;
    end
    // Missing else clause
end
```

**✅ Correct:**
```systemverilog
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin  // Correct polarity
        signal_q <= '0;
    end else begin
        signal_q <= signal_d;
    end
end
```

### 5. Incomplete Case Statements

**❌ Wrong:**
```systemverilog
always_comb begin
    case (opcode)
        ADD: result = a + b;
        SUB: result = a - b;
        // Missing default case - creates latch
    endcase
end
```

**✅ Correct:**
```systemverilog
always_comb begin
    result = '0;  // Default assignment
    case (opcode)
        ADD: result = a + b;
        SUB: result = a - b;
        default: result = '0;  // Explicit default
    endcase
end
```

## Configuration Parameter Usage

### 1. EXECUTION_MODE and BRANCH_PREDICTOR_TYPE

These critical parameters have been centralized in `riscv_config_pkg` for consistency:

```systemverilog
// In riscv_config_pkg.sv
parameter string DEFAULT_EXECUTION_MODE = "IN_ORDER";        // "IN_ORDER" or "OUT_OF_ORDER"
parameter string DEFAULT_BRANCH_PREDICTOR_TYPE = "TOURNAMENT"; // "STATIC", "DYNAMIC", "TOURNAMENT"
```

**Usage in Modules:**
```systemverilog
module my_core_module #(
    parameter string EXECUTION_MODE = DEFAULT_EXECUTION_MODE,
    parameter string BRANCH_PREDICTOR_TYPE = DEFAULT_BRANCH_PREDICTOR_TYPE
) (
    // ports...
);

    // Use the parameters to configure behavior
    generate
        if (EXECUTION_MODE == "OUT_OF_ORDER") begin : gen_ooo
            // Out-of-order execution logic
            reorder_buffer #(...) u_rob (...);
            reservation_station #(...) u_rs (...);
        end else begin : gen_in_order
            // In-order execution logic
            // ...
        end
    endgenerate
    
    generate
        if (BRANCH_PREDICTOR_TYPE == "TOURNAMENT") begin : gen_tournament_bp
            tournament_predictor #(...) u_bp (...);
        end else if (BRANCH_PREDICTOR_TYPE == "DYNAMIC") begin : gen_dynamic_bp
            branch_predictor #(...) u_bp (...);
        end
        // ... other predictor types
    endgenerate

endmodule
```

### 2. Interface Usage Best Practices

#### 2.1. Avoiding Hardcoded Interface Connections

**Problem**: Many modules hardcode interface signals instead of using proper SystemVerilog interfaces.

**❌ Wrong - Hardcoded Signals:**
```systemverilog
module memory_controller (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Hardcoded AXI signals - BAD!
    output logic        axi_awvalid,
    input  logic        axi_awready,
    output logic [31:0] axi_awaddr,
    output logic [7:0]  axi_awlen,
    // ... many more signals
);
```

**✅ Correct - Using Interface:**
```systemverilog
module memory_controller (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Clean interface usage - GOOD!
    memory_req_rsp_if.master mem_if,
    
    // Or for AXI-specific needs:
    // axi4_if.master axi_if
);
```

#### 2.2. Interface Modport Selection Guide

Choose the correct modport based on your module's role:

| Interface | Modport | Use Case |
|-----------|---------|----------|
| `memory_req_rsp_if` | `.master` | Initiating memory requests (CPU, DMA) |
| `memory_req_rsp_if` | `.slave` | Responding to requests (Memory, Cache) |
| `memory_req_rsp_if` | `.monitor` | Observing transactions (Testbench) |
| `cache_coherency_if` | `.l1_cache_port` | L1 cache connecting to coherency controller |
| `cache_coherency_if` | `.coherency_controller_port` | L2/L3 cache managing coherency |
| `inter_core_comm_if` | `.core` | Individual core communication |
| `inter_core_comm_if` | `.manager` | Central communication manager |

#### 2.3. Interface Array Usage

For multi-core designs, use interface arrays:

```systemverilog
module multi_core_system #(
    parameter integer NUM_CORES = DEFAULT_NUM_CORES
) (
    input logic clk_i,
    input logic rst_ni,
    
    // Interface arrays for per-core connections
    cache_coherency_if.l1_cache_port l1_cache_if [NUM_CORES],
    inter_core_comm_if.core comm_if [NUM_CORES]
);

    // Generate cores with proper interface connections
    generate
        for (genvar i = 0; i < NUM_CORES; i++) begin : gen_cores
            riscv_core #(
                .CORE_ID(i)
            ) u_core (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .cache_if(l1_cache_if[i]),
                .comm_if(comm_if[i])
            );
        end
    endgenerate

endmodule
```

### 3. Module Instantiation Dependencies

When instantiating modules, always check for their package dependencies:

#### 3.1. Dependency Check Process

1. **Identify Required Packages**: Look at the module's import statements
2. **Check Package Hierarchy**: Ensure all dependencies are imported in correct order
3. **Verify Parameter Compatibility**: Use consistent parameter values

**Example Module with Dependencies:**
```systemverilog
// In my_execution_unit.sv
import riscv_config_pkg::*;    // Always first
import riscv_types_pkg::*;     // Core types
import riscv_ooo_types_pkg::*; // Out-of-order types if needed

module my_execution_unit #(
    parameter integer NUM_ALU_UNITS = DEFAULT_NUM_ALU_UNITS,
    parameter integer ROB_SIZE = DEFAULT_ROB_SIZE
) (
    // ports...
);
```

**When Instantiating:**
```systemverilog
// In parent module
import riscv_config_pkg::*;    // Must import same packages
import riscv_types_pkg::*;
import riscv_ooo_types_pkg::*;

module parent_module (
    // ports...
);

    // Instantiate with consistent parameters
    my_execution_unit #(
        .NUM_ALU_UNITS(DEFAULT_NUM_ALU_UNITS),  // Use config defaults
        .ROB_SIZE(DEFAULT_ROB_SIZE)
    ) u_execution_unit (
        // connections...
    );

endmodule
```

#### 3.2. Common Dependency Issues

**Issue 1: Missing Package Import**
```systemverilog
// ❌ Wrong - missing import
module bad_module (
    input word_t data_i  // word_t undefined without import
);
```

**Solution:**
```systemverilog
// ✅ Correct - proper import
import riscv_types_pkg::*;

module good_module (
    input word_t data_i  // word_t now defined
);
```

**Issue 2: Parameter Mismatch**
```systemverilog
// ❌ Wrong - hardcoded parameter
my_module #(.DATA_WIDTH(32)) u_module (...);  // Should use XLEN
```

**Solution:**
```systemverilog
// ✅ Correct - parameterized
my_module #(.DATA_WIDTH(XLEN)) u_module (...);  // Uses config parameter
```

**Issue 3: Interface Type Mismatch**
```systemverilog
// ❌ Wrong - generic interface
generic_bus_if bus_if();
my_module u_module (.bus_if(bus_if));  // Type unclear
```

**Solution:**
```systemverilog
// ✅ Correct - specific interface
memory_req_rsp_if mem_if();
my_module u_module (.mem_if(mem_if.master));  // Clear type and role
```

### 4. Compilation Order Management

Ensure proper compilation order for packages and modules:

1. **Configuration Package First**: `riscv_config_pkg.sv`
2. **Core Types**: `riscv_types_pkg.sv`
3. **Specialized Packages**: All other `*_pkg.sv` files
4. **Interfaces**: All `*_if.sv` files
5. **Modules**: RTL modules in dependency order

**Example Compilation Script:**
```bash
# Compile packages first
vlog rtl/core/riscv_config_pkg.sv
vlog rtl/core/riscv_types_pkg.sv
vlog rtl/core/riscv_*_pkg.sv

# Compile interfaces
vlog rtl/interfaces/*.sv

# Compile modules (order matters for dependencies)
vlog rtl/units/*.sv
vlog rtl/memory/*.sv
vlog rtl/core/*.sv
```

---

## Conclusion

Following this guide ensures:
- Consistent code quality across the project
- Proper integration with existing infrastructure
- Maintainable and scalable design
- Effective verification and debugging
- Compliance with project standards

Remember to always review existing similar modules for patterns and consult the package documentation before creating new modules.

---

**Document Version:** 1.0  
**Last Updated:** 2025-01-27  
**Author:** DesignAI  
**Status:** Draft