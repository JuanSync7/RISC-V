# RTL Module Creation Guide

## Overview

This guide provides a comprehensive step-by-step approach for creating RTL modules within the RISC-V processor design. It covers package dependencies, interface usage, design patterns, and best practices based on the current codebase structure.

## Fundamental Principles

### **CRITICAL: Always Use SystemVerilog Interfaces with Modports**

**The #1 rule for protocol signals**: Never hardcode protocol signals. Always use proper SystemVerilog interfaces with appropriate modports. This is not optional - it's a mandatory requirement for all protocol connections including AXI4, CHI, TileLink, memory interfaces, and inter-core communication.

**Why This Matters:**
- **Type Safety**: Prevents connection errors and protocol violations
- **Maintainability**: Changes to protocols only require interface updates
- **Verification**: Enables proper protocol checking and monitoring
- **Scalability**: Supports complex multi-core and multi-protocol designs
- **Tool Support**: Better synthesis and timing analysis

**❌ NEVER DO THIS - Hardcoded Protocol Signals:**
```systemverilog
module bad_protocol_module (
    // DON'T hardcode AXI signals
    output logic        axi_awvalid,
    input  logic        axi_awready,
    output logic [31:0] axi_awaddr,
    output logic [7:0]  axi_awlen,
    output logic [2:0]  axi_awsize,
    // ... 50+ more AXI signals
);
```

**✅ ALWAYS DO THIS - Use Interfaces with Modports:**
```systemverilog
module good_protocol_module (
    // Clean, type-safe interface usage
    axi4_if.master axi_if,
    // OR for memory operations:
    memory_req_rsp_if.master mem_if
);
```

## Table of Contents

- [Fundamental Principles](#fundamental-principles)
- [Package Dependency Management](#package-dependency-management)
- [Protocol Interface Requirements](#protocol-interface-requirements)
- [Module Creation Checklist](#module-creation-checklist)
- [Interface Integration](#interface-integration)
- [Design Patterns](#design-patterns)
- [Code Quality Standards](#code-quality-standards)
- [Verification Considerations](#verification-considerations)
- [Examples](#examples)
- [Common Pitfalls](#common-pitfalls)
- [Configuration Parameter Usage](#configuration-parameter-usage)

## Protocol Interface Requirements

### 1. **Mandatory Interface Usage**

All protocol communications MUST use SystemVerilog interfaces with proper modports:

| Protocol Type | Required Interface | Correct Modport |
|---------------|-------------------|-----------------|
| **Memory Operations** | `memory_req_rsp_if` | `.master` (initiator)<br/>`.slave` (responder) |
| **AXI4 Protocol** | `axi4_if` | `.master`<br/>`.slave` |
| **CHI Protocol** | `chi_if` | `.rn` (Request Node)<br/>`.sn` (Slave Node) |
| **TileLink Protocol** | `tilelink_if` | `.manager`<br/>`.client` |
| **Cache Coherency** | `cache_coherency_if` | `.l1_cache_port`<br/>`.coherency_controller_port` |
| **Inter-Core Comm** | `inter_core_comm_if` | `.core`<br/>`.manager` |

### 2. **Modport Selection Rules**

**Rule 1**: Choose modports based on your module's role in the protocol:
- **Master/Manager/Initiator**: Starts transactions (CPU cores, DMA controllers)
- **Slave/Client/Responder**: Responds to transactions (Memory controllers, peripherals)
- **Monitor**: Observes transactions (Testbench components, debug modules)

**Rule 2**: Never connect interfaces without specifying modports:
```systemverilog
// ❌ WRONG - Ambiguous connection
my_module u_module (.mem_if(mem_if));

// ✅ CORRECT - Clear role specification
my_module u_module (.mem_if(mem_if.master));
```

**Rule 3**: Use interface arrays for multi-port/multi-core designs:
```systemverilog
// Multi-core interface connections
cache_coherency_if.l1_cache_port l1_cache_if [NUM_CORES];
inter_core_comm_if.core comm_if [NUM_CORES];
```

### 3. **Interface Instance Naming**

Follow consistent naming conventions for interface instances:

```systemverilog
// Memory interfaces
memory_req_rsp_if imem_if();  // Instruction memory
memory_req_rsp_if dmem_if();  // Data memory

// Protocol interfaces
axi4_if axi_m_if();          // AXI master interface
axi4_if axi_s_if();          // AXI slave interface
chi_if  chi_rn_if();         // CHI Request Node interface
tilelink_if tl_mgr_if();     // TileLink Manager interface

// Multi-core interfaces
inter_core_comm_if comm_if [NUM_CORES]();
cache_coherency_if coherency_if [NUM_CORES]();
```

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
  - [ ] **CRITICAL**: Identify ALL protocol interface requirements
  - [ ] Check for existing similar modules to reuse patterns

- [ ] **Parameter Planning**
  - [ ] Use existing parameters from `riscv_config_pkg` when possible
  - [ ] Define new parameters only if absolutely necessary
  - [ ] Ensure parameter names follow `UPPER_CASE_SNAKE_CASE` convention

### Phase 2: Protocol Interface Design (MANDATORY)

- [ ] **Interface Selection**
  - [ ] **NEVER hardcode protocol signals** - use proper interfaces
  - [ ] Choose correct interface type for each protocol
  - [ ] Verify interface supports required protocol version

- [ ] **Modport Assignment**
  - [ ] Select appropriate modport based on module role
  - [ ] Document modport choice rationale
  - [ ] Verify modport compatibility with connected modules

- [ ] **Interface Arrays (if needed)**
  - [ ] Use interface arrays for multi-core/multi-port designs
  - [ ] Ensure proper indexing and parameterization
  - [ ] Verify generate block compatibility

- [ ] **Port Definition**
  - [ ] Follow naming conventions (`_i`, `_o`, `_io` suffixes)
  - [ ] Use parameterized widths (e.g., `[XLEN-1:0]`)
  - [ ] Group related ports logically
  - [ ] **Minimize individual signal ports** - prefer interfaces

### Phase 3: Implementation

- [ ] **File Structure**
  - [ ] Use standard file header with all required fields
  - [ ] Include `AI_TAG` comments for documentation generation
  - [ ] Follow the established formatting style

- [ ] **Module Declaration**
  - [ ] Use ANSI-style port declarations
  - [ ] Parameter defaults from configuration package
  - [ ] Proper parameter typing (`integer`, `string`, etc.)
  - [ ] **Interface ports MUST specify modports**

- [ ] **Internal Architecture**
  - [ ] Use `always_ff` for sequential logic
  - [ ] Use `always_comb` for combinational logic
  - [ ] Avoid latches through complete case coverage

### Phase 4: Integration and Testing

- [ ] **Module Instantiation**
  - [ ] Verify all sub-module packages are imported
  - [ ] Use proper instance naming (`u_module_name`)
  - [ ] **CRITICAL**: Connect interfaces with proper modports
  - [ ] Verify interface compatibility across hierarchy

- [ ] **Protocol Compliance**
  - [ ] Verify protocol timing requirements
  - [ ] Check for proper handshaking implementation
  - [ ] Validate burst and transaction handling

- [ ] **Compilation Check**
  - [ ] Add to compilation order in testbench scripts
  - [ ] Verify no circular dependencies
  - [ ] Check for lint warnings
  - [ ] **Verify interface type checking passes**

## Interface Integration

### 1. **MANDATORY: Protocol Interface Implementation**

**Every module that communicates via protocols MUST use proper SystemVerilog interfaces with modports.** This is not a suggestion - it's a requirement for maintainable, scalable, and verifiable RTL design.

#### 1.1. Memory Interface Usage (Required for all memory operations)

For modules that need memory access:

```systemverilog
module my_memory_module (
    input  logic clk_i,
    input  logic rst_ni,
    
    // ALWAYS use proper memory interface with modport
    memory_req_rsp_if.master mem_if,
    
    // Other ports...
);

    // Interface usage example
    always_comb begin
        // Request signals
        mem_if.req_valid = start_memory_op;
        mem_if.req_addr  = memory_address;
        mem_if.req_write = write_operation;
        mem_if.req_data  = write_data;
        
        // Response handling
        memory_data_ready = mem_if.rsp_valid;
        read_data = mem_if.rsp_data;
    end
    
    // Handle backpressure properly
    assign can_start_new_request = mem_if.req_ready;

endmodule
```

**Key Points:**
- Always use `.master` modport for initiating requests
- Always use `.slave` modport for responding to requests
- Handle backpressure with `req_ready` and `rsp_valid`
- Use burst transactions for cache line operations
- **NEVER hardcode the individual signals**

#### 1.2. AXI4 Protocol Integration

For modules requiring AXI4 protocol compliance:

```systemverilog
module axi4_compliant_module (
    input  logic clk_i,
    input  logic rst_ni,
    
    // Proper AXI4 interface usage
    axi4_if.master axi_m_if,  // For initiating AXI transactions
    axi4_if.slave  axi_s_if   // For responding to AXI transactions
);

    // AXI master logic
    always_comb begin
        // Write address channel
        axi_m_if.awvalid = start_write_transaction;
        axi_m_if.awaddr  = write_address;
        axi_m_if.awlen   = burst_length - 1;
        axi_m_if.awsize  = $clog2(DATA_WIDTH/8);
        
        // Write data channel
        axi_m_if.wvalid = write_data_valid;
        axi_m_if.wdata  = write_data;
        axi_m_if.wlast  = last_write_data;
        
        // Response handling
        write_response_ready = axi_m_if.bready;
    end

endmodule
```

**Critical Implementation Rules:**
- Use `.master` modport for AXI masters (initiators)
- Use `.slave` modport for AXI slaves (responders)
- Implement all required AXI handshaking
- Handle burst transactions correctly
- **Absolutely NO hardcoded AXI signal lists**

### 2. Multi-Core Interface Integration

For multi-core features, use interface arrays with proper modports:

```systemverilog
module multi_core_module #(
    parameter integer NUM_CORES = DEFAULT_NUM_CORES
) (
    input  logic clk_i,
    input  logic rst_ni,
    
    // Interface arrays with proper modports
    inter_core_comm_if.core comm_if [NUM_CORES],
    cache_coherency_if.l1_cache_port coherency_if [NUM_CORES],
    sync_primitives_if.manager sync_if
);

    // Generate per-core connections
    generate
        for (genvar i = 0; i < NUM_CORES; i++) begin : gen_core_connections
            // Each core gets its own interface instance
            assign coherency_if[i].cache_req_valid = core_cache_requests[i].valid;
            assign coherency_if[i].cache_req_addr  = core_cache_requests[i].addr;
            // ... other per-core connections
        end
    endgenerate

endmodule
```

**Key Points:**
- Use array interfaces for per-core connections: `interface_name [NUM_CORES]`
- Choose correct modport based on module role in the protocol
- Handle NUM_CORES parameterization consistently
- Use generate blocks for scalable connections

### 3. Protocol Factory Integration

When using the protocol factory for dynamic protocol switching:

```systemverilog
module protocol_aware_module (
    input  logic clk_i,
    input  logic rst_ni,
    
    // Clean interface connections to protocol factory
    memory_req_rsp_if.master mem_if,
    
    // Protocol selection
    input protocol_select_t protocol_select_i
);

    // Let the protocol factory handle the complexity
    protocol_factory u_protocol_factory (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .mem_if(mem_if.slave),          // Connect as slave to our master
        .protocol_select_i(protocol_select_i),
        
        // Protocol-specific interfaces handled internally
        .axi4_if(axi4_if.master),
        .chi_if(chi_if.master),
        .tilelink_if(tilelink_if.master)
    );

endmodule
```

### 4. **Interface Creation Guidelines**

When you must create new interfaces (rare - check existing interfaces first):

```systemverilog
interface my_custom_protocol_if #(
    parameter integer DATA_WIDTH = XLEN,
    parameter integer ADDR_WIDTH = ADDR_WIDTH
) (
    input logic clk,
    input logic rst_n
);
    
    // Signal declarations
    logic [ADDR_WIDTH-1:0] addr;
    logic [DATA_WIDTH-1:0] data;
    logic                  valid;
    logic                  ready;
    logic                  error;
    
    // ALWAYS define clear modports
    modport master (
        output addr, data, valid,
        input  ready, error,
        input  clk, rst_n
    );
    
    modport slave (
        input  addr, data, valid,
        output ready, error,
        input  clk, rst_n
    );
    
    modport monitor (
        input  addr, data, valid, ready, error,
        input  clk, rst_n
    );
    
    // Optional: Add protocol checking assertions
    // Assert protocol properties here
    
endinterface : my_custom_protocol_if
```

**Interface Creation Rules:**
1. **First check if existing interfaces can be used**
2. Define clear, descriptive signal names
3. **Always provide appropriate modports**
4. Include monitor modport for verification
5. Add protocol assertions where appropriate
6. Use consistent parameter naming from config package

## Design Patterns

### 1. Pipeline Stage Pattern with Interface

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
    
    // Memory interface (if needed)
    memory_req_rsp_if.master mem_if
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
    
    // Combinational logic with interface usage
    always_comb begin
        stage_reg_d = prev_stage_reg_i;
        
        // Memory interface usage
        mem_if.req_valid = stage_reg_q.memory_op_valid;
        mem_if.req_addr  = stage_reg_q.memory_address;
        mem_if.req_write = stage_reg_q.is_store_op;
        mem_if.req_data  = stage_reg_q.store_data;
        
        // Handle memory response
        if (mem_if.rsp_valid) begin
            stage_reg_d.memory_result = mem_if.rsp_data;
            stage_reg_d.memory_op_complete = 1'b1;
        end
    end
    
    assign next_stage_reg_o = stage_reg_q;

endmodule
```

### 2. Protocol Bridge Pattern

```systemverilog
module protocol_bridge (
    input  logic clk_i,
    input  logic rst_ni,
    
    // Input protocol interface
    memory_req_rsp_if.slave  input_if,
    
    // Output protocol interface  
    axi4_if.master output_if
);

    // Bridge state machine and conversion logic
    typedef enum logic [1:0] {
        S_IDLE,
        S_CONVERTING,
        S_RESPONDING
    } bridge_state_e;
    
    bridge_state_e state_q, state_d;
    
    // State machine for protocol conversion
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state_q <= S_IDLE;
        end else begin
            state_q <= state_d;
        end
    end
    
    // Protocol conversion logic
    always_comb begin
        state_d = state_q;
        
        // Default interface values
        input_if.req_ready = 1'b0;
        input_if.rsp_valid = 1'b0;
        input_if.rsp_data  = '0;
        
        output_if.awvalid = 1'b0;
        output_if.wvalid  = 1'b0;
        output_if.arvalid = 1'b0;
        
        case (state_q)
            S_IDLE: begin
                input_if.req_ready = 1'b1;
                if (input_if.req_valid) begin
                    state_d = S_CONVERTING;
                end
            end
            
            S_CONVERTING: begin
                // Convert memory_req_rsp to AXI4
                if (input_if.req_write) begin
                    output_if.awvalid = 1'b1;
                    output_if.awaddr  = input_if.req_addr;
                    output_if.wvalid  = 1'b1;
                    output_if.wdata   = input_if.req_data;
                end else begin
                    output_if.arvalid = 1'b1;
                    output_if.araddr  = input_if.req_addr;
                end
                
                if (/* AXI transaction accepted */) begin
                    state_d = S_RESPONDING;
                end
            end
            
            S_RESPONDING: begin
                // Wait for AXI response and convert back
                if (/* AXI response received */) begin
                    input_if.rsp_valid = 1'b1;
                    input_if.rsp_data  = /* converted AXI response */;
                    state_d = S_IDLE;
                end
            end
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
    input  logic clk_i,
    input  logic rst_ni,
    
    // ALWAYS use interfaces for protocol connections
    memory_req_rsp_if.master imem_if,
    memory_req_rsp_if.master dmem_if,
    cache_coherency_if.l1_cache_port coherency_if
);

    // Use the parameters to configure behavior
    generate
        if (EXECUTION_MODE == "OUT_OF_ORDER") begin : gen_ooo
            // Out-of-order execution logic
            reorder_buffer #(...) u_rob (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mem_if(dmem_if.master)  // Proper interface connection
            );
            reservation_station #(...) u_rs (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .coherency_if(coherency_if.l1_cache_port)
            );
        end else begin : gen_in_order
            // In-order execution logic with interfaces
            simple_execution_unit #(...) u_exec (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mem_if(dmem_if.master)
            );
        end
    endgenerate
    
    generate
        if (BRANCH_PREDICTOR_TYPE == "TOURNAMENT") begin : gen_tournament_bp
            tournament_predictor #(...) u_bp (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .imem_if(imem_if.master)  // Interface for instruction fetch
            );
        end else if (BRANCH_PREDICTOR_TYPE == "DYNAMIC") begin : gen_dynamic_bp
            branch_predictor #(...) u_bp (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .imem_if(imem_if.master)
            );
        end
        // ... other predictor types
    endgenerate

endmodule
```

### 2. **MANDATORY Interface Usage Best Practices**

#### 2.1. Interface Selection and Modport Usage

**RULE: Always choose the correct interface type and modport for your protocol:**

| Protocol Type | Interface | Correct Modport | Module Examples |
|---------------|-----------|-----------------|-----------------|
| **Memory Operations** | `memory_req_rsp_if` | `.master` | CPU cores, DMA, Prefetcher |
| **Memory Operations** | `memory_req_rsp_if` | `.slave` | Memory controller, Cache |
| **AXI4 Protocol** | `axi4_if` | `.master` | Memory controllers, Bridges |
| **AXI4 Protocol** | `axi4_if` | `.slave` | Peripherals, Memory |
| **CHI Protocol** | `chi_if` | `.rn` (Request Node) | CPU cores, Accelerators |
| **CHI Protocol** | `chi_if` | `.sn` (Slave Node) | Memory controllers |
| **TileLink** | `tilelink_if` | `.manager` | Interconnect, Bridges |
| **TileLink** | `tilelink_if` | `.client` | CPU cores, Peripherals |
| **Cache Coherency** | `cache_coherency_if` | `.l1_cache_port` | L1 caches |
| **Cache Coherency** | `cache_coherency_if` | `.coherency_controller_port` | L2/L3 controllers |

#### 2.2. Interface Array Usage (Multi-Core Designs)

For multi-core designs, ALWAYS use interface arrays:

```systemverilog
module multi_core_system #(
    parameter integer NUM_CORES = DEFAULT_NUM_CORES
) (
    input logic clk_i,
    input logic rst_ni,
    
    // Interface arrays for per-core connections
    cache_coherency_if.l1_cache_port l1_cache_if [NUM_CORES],
    inter_core_comm_if.core comm_if [NUM_CORES],
    
    // System-level interfaces
    memory_req_rsp_if.master system_mem_if,
    axi4_if.slave system_axi_if
);

    // Generate cores with proper interface connections
    generate
        for (genvar i = 0; i < NUM_CORES; i++) begin : gen_cores
            riscv_core #(
                .CORE_ID(i),
                .EXECUTION_MODE(DEFAULT_EXECUTION_MODE)
            ) u_core (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                // Proper interface connections with modports
                .cache_if(l1_cache_if[i]),      // L1 cache interface
                .comm_if(comm_if[i]),           // Inter-core communication
                .imem_if(/* connected to instruction memory */),
                .dmem_if(/* connected to data memory */)
            );
        end
    endgenerate

    // System-level interconnect with interface usage
    memory_interconnect u_interconnect (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .core_mem_if(l1_cache_if),           // Array of interfaces
        .system_mem_if(system_mem_if.slave), // System memory interface
        .axi_if(system_axi_if.master)        // External AXI interface
    );

endmodule
```

### 3. Module Instantiation with Interface Dependencies

#### 3.1. **Mandatory Dependency Check Process**

Before instantiating any module:

1. **Identify Required Packages**: Look at the module's import statements
2. **Check Package Hierarchy**: Ensure all dependencies are imported in correct order
3. **Verify Interface Compatibility**: Ensure interface types and modports match
4. **Verify Parameter Compatibility**: Use consistent parameter values

**Example Module with Interface Dependencies:**
```systemverilog
// In my_execution_unit.sv
import riscv_config_pkg::*;    // Always first
import riscv_types_pkg::*;     // Core types
import riscv_ooo_types_pkg::*; // Out-of-order types if needed

module my_execution_unit #(
    parameter integer NUM_ALU_UNITS = DEFAULT_NUM_ALU_UNITS,
    parameter integer ROB_SIZE = DEFAULT_ROB_SIZE
) (
    input logic clk_i,
    input logic rst_ni,
    
    // Interface connections - NOT individual signals
    memory_req_rsp_if.master dmem_if,
    cache_coherency_if.l1_cache_port coherency_if
);
```

**When Instantiating:**
```systemverilog
// In parent module
import riscv_config_pkg::*;    // Must import same packages
import riscv_types_pkg::*;
import riscv_ooo_types_pkg::*;

module parent_module (
    input logic clk_i,
    input logic rst_ni,
    
    // Parent module interfaces
    memory_req_rsp_if.slave parent_mem_if,
    cache_coherency_if.coherency_controller_port parent_coherency_if
);

    // Create interface instances for child modules
    memory_req_rsp_if child_dmem_if();
    cache_coherency_if child_coherency_if();

    // Instantiate with consistent parameters and proper interface connections
    my_execution_unit #(
        .NUM_ALU_UNITS(DEFAULT_NUM_ALU_UNITS),  // Use config defaults
        .ROB_SIZE(DEFAULT_ROB_SIZE)
    ) u_execution_unit (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        // Connect interfaces with proper modports
        .dmem_if(child_dmem_if.master),              // Child is master
        .coherency_if(child_coherency_if.l1_cache_port)
    );
    
    // Connect child interfaces to parent interfaces
    // This is where protocol bridging/routing occurs
    interface_bridge u_mem_bridge (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .child_if(child_dmem_if.slave),      // Connect as slave to child's master
        .parent_if(parent_mem_if.master)     // Connect as master to parent's slave
    );

endmodule
```

#### 3.2. Common Interface Dependency Issues

**Issue 1: Missing Interface Declaration**
```systemverilog
// ❌ Wrong - hardcoded signals instead of interface
module bad_module (
    input  logic        clk_i,
    input  logic        rst_ni,
    // Hardcoded memory signals - BAD!
    output logic        mem_req_valid,
    output logic [31:0] mem_req_addr,
    input  logic        mem_req_ready
);
```

**Solution:**
```systemverilog
// ✅ Correct - proper interface usage
module good_module (
    input  logic        clk_i,
    input  logic        rst_ni,
    // Clean interface usage - GOOD!
    memory_req_rsp_if.master mem_if
);
```

**Issue 2: Interface Type Mismatch**
```systemverilog
// ❌ Wrong - generic interface name, unclear protocol
generic_bus_if bus_if();
my_module u_module (.bus_if(bus_if));  // What protocol is this?
```

**Solution:**
```systemverilog
// ✅ Correct - specific interface type and clear modport
memory_req_rsp_if mem_if();
my_module u_module (.mem_if(mem_if.master));  // Clear protocol and role
```

**Issue 3: Wrong Modport Selection**
```systemverilog
// ❌ Wrong - memory controller using master modport
memory_controller u_mem_ctrl (
    .mem_if(mem_if.master)  // Memory controller should respond, not initiate!
);
```

**Solution:**
```systemverilog
// ✅ Correct - memory controller using slave modport
memory_controller u_mem_ctrl (
    .mem_if(mem_if.slave)   // Memory controller responds to requests
);
```

### 4. Compilation Order with Interface Dependencies

Ensure proper compilation order for packages, interfaces, and modules:

1. **Configuration Package First**: `riscv_config_pkg.sv`
2. **Core Types**: `riscv_types_pkg.sv`
3. **Specialized Packages**: All other `*_pkg.sv` files
4. **Interfaces**: All `*_if.sv` files (critical for interface-based modules)
5. **Modules**: RTL modules in dependency order

**Example Compilation Script:**
```bash
# Phase 1: Compile packages first
vlog rtl/core/riscv_config_pkg.sv
vlog rtl/core/riscv_types_pkg.sv
vlog rtl/core/riscv_*_pkg.sv

# Phase 2: Compile interfaces (CRITICAL for interface-based design)
vlog rtl/interfaces/memory_req_rsp_if.sv
vlog rtl/interfaces/axi4_if.sv
vlog rtl/interfaces/chi_if.sv
vlog rtl/interfaces/tilelink_if.sv
vlog rtl/interfaces/cache_coherency_if.sv
vlog rtl/interfaces/inter_core_comm_if.sv
vlog rtl/interfaces/sync_primitives_if.sv

# Phase 3: Compile modules (order matters for dependencies)
vlog rtl/units/*.sv              # Basic functional units
vlog rtl/memory/*.sv             # Memory subsystem
vlog rtl/protocols/*.sv          # Protocol adapters (use interfaces)
vlog rtl/core/*.sv               # Core modules
```

## Examples

### 1. **Interface-Based Functional Unit**

```systemverilog
module interface_based_alu #(
    parameter integer DATA_WIDTH = XLEN,
    parameter integer LATENCY = DEFAULT_ALU_LATENCY
) (
    input  logic                    clk_i,
    input  logic                    rst_ni,
    
    // Control signals (still individual signals for simple controls)
    input  logic [3:0]              alu_op_i,
    input  logic                    valid_i,
    output logic                    ready_o,
    
    // Data through interface for future extensibility
    input  logic [DATA_WIDTH-1:0]   operand_a_i,
    input  logic [DATA_WIDTH-1:0]   operand_b_i,
    output logic [DATA_WIDTH-1:0]   result_o,
    output logic                    valid_o,
    output logic                    overflow_o,
    
    // Memory interface for complex operations (if needed)
    memory_req_rsp_if.master mem_if
);

import riscv_config_pkg::*;
import riscv_types_pkg::*;

    // Pipeline registers for latency
    logic [LATENCY-1:0] busy_q;
    logic [DATA_WIDTH-1:0] result_pipe_q [LATENCY];
    
    // Operation pipeline
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            busy_q <= '0;
            for (int i = 0; i < LATENCY; i++) begin
                result_pipe_q[i] <= '0;
            end
        end else begin
            busy_q <= {busy_q[LATENCY-2:0], valid_i};
            
            // Pipeline the computation
            result_pipe_q[0] <= compute_result(alu_op_i, operand_a_i, operand_b_i);
            for (int i = 1; i < LATENCY; i++) begin
                result_pipe_q[i] <= result_pipe_q[i-1];
            end
        end
    end
    
    // Interface usage for memory operations (if ALU needs memory access)
    always_comb begin
        mem_if.req_valid = 1'b0;  // Default: no memory request
        mem_if.req_addr  = '0;
        mem_if.req_write = 1'b0;
        mem_if.req_data  = '0;
        
        // Example: Special ALU operation that needs memory lookup
        if (alu_op_i == ALU_MEM_LOOKUP && valid_i) begin
            mem_if.req_valid = 1'b1;
            mem_if.req_addr  = operand_a_i;  // Use operand as address
            mem_if.req_write = 1'b0;         // Read operation
        end
    end
    
    assign ready_o = !busy_q[0] || !valid_i;  // Ready when not busy
    assign valid_o = busy_q[LATENCY-1];
    assign result_o = result_pipe_q[LATENCY-1];

    // Helper function for computation
    function automatic logic [DATA_WIDTH-1:0] compute_result(
        input logic [3:0] op,
        input logic [DATA_WIDTH-1:0] a,
        input logic [DATA_WIDTH-1:0] b
    );
        case (op)
            ALU_ADD:  return a + b;
            ALU_SUB:  return a - b;
            ALU_AND:  return a & b;
            ALU_OR:   return a | b;
            ALU_XOR:  return a ^ b;
            default:  return '0;
        endcase
    endfunction

endmodule
```

### 2. **Multi-Interface Pipeline Stage**

```systemverilog
module interface_based_decode_stage #(
    parameter addr_t RESET_VECTOR = DEFAULT_RESET_VECTOR
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Pipeline control
    input  logic        stall_i,
    input  logic        flush_i,
    
    // Pipeline stage registers
    input  fetch_stage_reg_t   fetch_reg_i,
    output decode_stage_reg_t  decode_reg_o,
    
    // Register file interface (example of simple interface usage)
    output logic [4:0]  rs1_addr_o,
    output logic [4:0]  rs2_addr_o,
    input  word_t       rs1_data_i,
    input  word_t       rs2_data_i,
    
    // Memory interface for instruction fetch (if needed)
    memory_req_rsp_if.master imem_if,
    
    // Cache coherency interface for multi-core
    cache_coherency_if.l1_cache_port cache_coherency_if
);

import riscv_config_pkg::*;
import riscv_types_pkg::*;
import riscv_core_pkg::*;

    // Decode stage register
    decode_stage_reg_t decode_reg_q, decode_reg_d;
    
    // Instruction decode
    word_t instruction;
    logic [6:0] opcode;
    logic [4:0] rd, rs1, rs2;
    logic [2:0] funct3;
    logic [6:0] funct7;
    
    // Sequential logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            decode_reg_q <= '0;
        end else if (flush_i) begin
            decode_reg_q <= '0;
        end else if (!stall_i) begin
            decode_reg_q <= decode_reg_d;
        end
    end
    
    // Combinational decode logic
    always_comb begin
        // Default values
        decode_reg_d = '0;
        
        // Get instruction from fetch stage
        instruction = fetch_reg_i.instruction;
        
        // Decode instruction fields
        opcode = instruction[6:0];
        rd     = instruction[11:7];
        rs1    = instruction[19:15];
        rs2    = instruction[24:20];
        funct3 = instruction[14:12];
        funct7 = instruction[31:25];
        
        // Fill decode stage register
        decode_reg_d.pc = fetch_reg_i.pc;
        decode_reg_d.instruction = instruction;
        decode_reg_d.rd_addr = rd;
        decode_reg_d.rs1_addr = rs1;
        decode_reg_d.rs2_addr = rs2;
        decode_reg_d.rs1_data = rs1_data_i;
        decode_reg_d.rs2_data = rs2_data_i;
        
        // Decode control signals based on opcode
        case (opcode)
            OPCODE_LUI:   decode_reg_d.alu_op = ALU_LUI;
            OPCODE_AUIPC: decode_reg_d.alu_op = ALU_AUIPC;
            OPCODE_OP:    decode_reg_d.alu_op = decode_alu_op(funct3, funct7);
            // ... other opcodes
            default:      decode_reg_d.alu_op = ALU_NOP;
        endcase
        
        // Memory interface usage (if decode needs to access memory)
        imem_if.req_valid = 1'b0;  // Default: no memory request
        
        // Cache coherency interface usage
        cache_coherency_if.cache_req_valid = 1'b0;  // Default: no coherency request
        
        // Example: Instruction cache miss handling
        if (fetch_reg_i.cache_miss) begin
            cache_coherency_if.cache_req_valid = 1'b1;
            cache_coherency_if.cache_req_addr = fetch_reg_i.pc;
            cache_coherency_if.cache_req_type = CACHE_REQ_INSTRUCTION_FETCH;
        end
    end
    
    // Register file connections
    assign rs1_addr_o = rs1;
    assign rs2_addr_o = rs2;
    
    // Output to next stage
    assign decode_reg_o = decode_reg_q;
    
    // Helper function for ALU operation decode
    function automatic alu_op_t decode_alu_op(
        input logic [2:0] funct3,
        input logic [6:0] funct7
    );
        case (funct3)
            3'b000: return (funct7[5]) ? ALU_SUB : ALU_ADD;
            3'b001: return ALU_SLL;
            3'b010: return ALU_SLT;
            3'b011: return ALU_SLTU;
            3'b100: return ALU_XOR;
            3'b101: return (funct7[5]) ? ALU_SRA : ALU_SRL;
            3'b110: return ALU_OR;
            3'b111: return ALU_AND;
            default: return ALU_NOP;
        endcase
    endfunction

endmodule
```

## Verification Considerations

### 1. Interface-Based Testability Features

When designing modules with interfaces, include features that enhance verification:

```systemverilog
module verifiable_interface_module (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Primary interface
    memory_req_rsp_if.master mem_if,
    
    // Debug interface for verification
    `ifdef SIMULATION
    output logic [31:0] debug_state_o,
    output logic [31:0] debug_counters_o [4],
    output logic        debug_interface_busy_o
    `endif
);

    // Debug outputs for verification
    `ifdef SIMULATION
    assign debug_state_o = {28'b0, current_state};
    assign debug_counters_o[0] = request_count;
    assign debug_counters_o[1] = response_count;
    assign debug_counters_o[2] = error_count;
    assign debug_counters_o[3] = timeout_count;
    assign debug_interface_busy_o = mem_if.req_valid && !mem_if.req_ready;
    `endif

    // Performance counters
    logic [31:0] request_count, response_count, error_count, timeout_count;
    
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            request_count  <= '0;
            response_count <= '0;
            error_count    <= '0;
            timeout_count  <= '0;
        end else begin
            if (mem_if.req_valid && mem_if.req_ready) begin
                request_count <= request_count + 1;
            end
            if (mem_if.rsp_valid) begin
                response_count <= response_count + 1;
                if (mem_if.rsp_error) begin
                    error_count <= error_count + 1;
                end
            end
            // ... timeout detection logic
        end
    end

endmodule
```

### 2. Interface Protocol Assertions

Add assertions to verify interface protocol compliance:

```systemverilog
// Protocol compliance assertions
assert property (@(posedge clk_i) disable iff (!rst_ni)
    mem_if.req_valid && !mem_if.req_ready |=> mem_if.req_valid)
else $error("Memory request must remain valid until accepted");

assert property (@(posedge clk_i) disable iff (!rst_ni)
    mem_if.req_valid |-> mem_if.req_addr != 'x)
else $error("Memory request address must be defined when valid");

// Interface usage assertions
assert property (@(posedge clk_i) disable iff (!rst_ni)
    mem_if.req_valid |-> ##[1:MAX_RESPONSE_LATENCY] mem_if.rsp_valid)
else $error("Memory response must arrive within maximum latency");
```

---

## Conclusion

Following this guide ensures:
- **Protocol Compliance**: Proper interface usage prevents protocol violations
- **Maintainability**: Interface-based designs are easier to modify and extend
- **Type Safety**: SystemVerilog interfaces provide compile-time checking
- **Verification**: Clear interface boundaries enable better testability
- **Scalability**: Interface arrays support multi-core and complex system designs
- **Tool Support**: Better synthesis, timing analysis, and debugging

**Remember the #1 rule**: **NEVER hardcode protocol signals. ALWAYS use SystemVerilog interfaces with proper modports.**

This is not just a best practice - it's a mandatory requirement for professional RTL design.

---

**Document Version:** 2.0  
**Last Updated:** 2025-01-27  
**Author:** DesignAI  
**Status:** Updated with Interface Requirements

## Common Pitfalls

### **CRITICAL PITFALL #1: Hardcoding Protocol Signals (NEVER DO THIS)**

**This is the #1 most serious error in RTL design. Hardcoding protocol signals:**
- Creates unmaintainable code
- Violates type safety
- Makes protocol changes impossible
- Breaks verification flows
- Causes integration nightmares

**❌ ABSOLUTELY WRONG - The Worst Anti-Pattern:**
```systemverilog
module terrible_hardcoded_module (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // DON'T EVER DO THIS - Hardcoded AXI signals
    output logic        axi_awvalid,
    input  logic        axi_awready,
    output logic [31:0] axi_awaddr,
    output logic [7:0]  axi_awlen,
    output logic [2:0]  axi_awsize,
    output logic [1:0]  axi_awburst,
    output logic        axi_awlock,
    output logic [3:0]  axi_awcache,
    output logic [2:0]  axi_awprot,
    output logic [3:0]  axi_awqos,
    output logic [3:0]  axi_awregion,
    output logic [USER_WIDTH-1:0] axi_awuser,
    
    output logic        axi_wvalid,
    input  logic        axi_wready,
    output logic [31:0] axi_wdata,
    output logic [3:0]  axi_wstrb,
    output logic        axi_wlast,
    output logic [USER_WIDTH-1:0] axi_wuser,
    
    input  logic        axi_bvalid,
    output logic        axi_bready,
    input  logic [1:0]  axi_bresp,
    input  logic [USER_WIDTH-1:0] axi_buser,
    
    // ... 20+ more AXI read signals
    // This is IMPOSSIBLE to maintain!
);
```

**✅ ALWAYS CORRECT - Use Proper Interface:**
```systemverilog
module excellent_interface_module (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Clean, maintainable, type-safe interface
    axi4_if.master axi_if
);

    // Simple, clean interface usage
    always_comb begin
        axi_if.awvalid = start_write_transaction;
        axi_if.awaddr  = write_address;
        axi_if.awlen   = burst_length - 1;
        // ... clean, readable code
    end

endmodule
```

**Why This Matters:**
- **Maintainability**: Interface changes propagate automatically
- **Type Safety**: Compiler catches connection errors
- **Readability**: Clear, concise code
- **Verification**: Proper protocol monitoring
- **Tool Support**: Better synthesis and analysis

### 2. Interface Connection Errors

**❌ Wrong:**
```systemverilog
// Missing modport specification - ambiguous!
my_module u_module (
    .mem_if(mem_if)  // Which role does this module play?
);

// Wrong modport for module role
memory_controller u_mem_ctrl (
    .mem_if(mem_if.master)  // Memory controller should be slave!
);
```

**✅ Correct:**
```systemverilog
// Clear modport specification
cpu_module u_cpu (
    .mem_if(mem_if.master)  // CPU initiates memory requests
);

memory_controller u_mem_ctrl (
    .mem_if(mem_if.slave)   // Memory controller responds to requests
);
```

### 3. Package Import Issues

**❌ Wrong:**
```systemverilog
// Missing config package import - parameters undefined
import riscv_types_pkg::*;
parameter integer WIDTH = 32;  // Hard-coded instead of XLEN
```

**✅ Correct:**
```systemverilog
import riscv_config_pkg::*;  // Import config first
import riscv_types_pkg::*;
parameter integer WIDTH = XLEN;  // Use parameterized value
```

### 4. Parameter Override Issues

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

### 5. Reset Logic Errors

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

### 6. Incomplete Case Statements

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

## Verification Considerations