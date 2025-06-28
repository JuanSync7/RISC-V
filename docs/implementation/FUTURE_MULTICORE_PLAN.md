# Future Multi-Core Implementation Plan

## Overview

This document outlines the future implementation plan for transitioning from the current single-core design (Option 1: Memory Wrapper) to a full multi-core capable design (Option 2: Protocol-Agnostic Pipeline) with parameter-based switching between the two approaches.

## Current State (Option 1: Memory Wrapper)

### Architecture
- **Memory Wrapper**: Abstracts protocol details from pipeline stages
- **Pipeline Stages**: Fetch and Memory stages use memory wrapper interface
- **Protocol Adapters**: AXI4 adapter implemented, CHI/TileLink adapters planned
- **Single Core**: Optimized for single-core operation

### Benefits
- ✅ Minimal refactoring required
- ✅ Low risk and development effort
- ✅ Backward compatible with existing AXI4 interfaces
- ✅ Easy to understand and maintain

### Limitations
- ❌ Limited cache coherency support
- ❌ No multi-core scalability
- ❌ Protocol switching requires wrapper reconfiguration

## Future State (Option 2: Protocol-Agnostic Pipeline)

### Architecture
- **Protocol-Agnostic Pipeline**: All stages use protocol-agnostic interfaces
- **Cache Coherency**: Full cache coherency support across cores
- **Multi-Core Support**: Native support for multiple cores
- **Protocol Flexibility**: Easy switching between AXI4, CHI, and TileLink

### Benefits
- ✅ Full cache coherency support
- ✅ Native multi-core scalability
- ✅ Maximum protocol flexibility
- ✅ Future-proof architecture

### Challenges
- ❌ Higher complexity and development effort
- ❌ More extensive refactoring required
- ❌ Increased verification complexity

## Parameter-Based Design Switching

### Core Configuration Parameter

```systemverilog
module riscv_core #(
    parameter addr_t RESET_VECTOR = 32'h0000_0000,
    parameter string PROTOCOL_TYPE = "AXI4",
    // AI_TAG: PARAM_DESC - CORE_MODE - Core operation mode.
    // AI_TAG: PARAM_USAGE - Determines whether to use memory wrapper (SINGLE_CORE) 
    // AI_TAG: PARAM_USAGE - or protocol-agnostic pipeline (MULTI_CORE).
    // AI_TAG: PARAM_CONSTRAINTS - Must be "SINGLE_CORE" or "MULTI_CORE".
    parameter string CORE_MODE = "SINGLE_CORE",
    
    // Multi-core specific parameters
    parameter integer CORE_ID = 0,
    parameter integer NUM_CORES = 1,
    parameter integer CACHE_LINE_SIZE = 64,
    parameter integer CACHE_SIZE = 32*1024  // 32KB
) (
    // ... existing ports ...
    
    // Multi-core specific ports (when CORE_MODE == "MULTI_CORE")
    input  logic [NUM_CORES-1:0] core_active_i,
    output logic [NUM_CORES-1:0] core_ready_o,
    
    // Cache coherency interface (when CORE_MODE == "MULTI_CORE")
    cache_if.coherent cache_coherent_if,
    
    // Protocol-agnostic memory interface (when CORE_MODE == "MULTI_CORE")
    memory_req_rsp_if.master mem_if
);
```

### Implementation Strategy

#### Phase 1: Single-Core Mode (Current)
```systemverilog
generate
    if (CORE_MODE == "SINGLE_CORE") begin : single_core_gen
        // Current memory wrapper implementation
        memory_wrapper #(
            .PROTOCOL_TYPE(PROTOCOL_TYPE)
        ) u_memory_wrapper (
            // ... existing connections ...
        );
        
        // Current pipeline stages with memory wrapper interface
        fetch_stage #(.RESET_VECTOR(RESET_VECTOR)) u_fetch_stage (
            // ... existing connections ...
        );
        
        mem_stage u_mem_stage (
            // ... existing connections ...
        );
    end
endgenerate
```

#### Phase 2: Multi-Core Mode (Future)
```systemverilog
generate
    if (CORE_MODE == "MULTI_CORE") begin : multi_core_gen
        // Protocol-agnostic pipeline stages
        fetch_stage_multi #(
            .RESET_VECTOR(RESET_VECTOR),
            .CORE_ID(CORE_ID),
            .NUM_CORES(NUM_CORES)
        ) u_fetch_stage (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            // ... control signals ...
            .mem_if(mem_if.slave),
            .cache_if(cache_coherent_if.slave),
            .if_id_reg_o(if_id_reg),
            .pc_f_o(pc_f_o),
            .bp_prediction_o(bp_prediction_o)
        );
        
        decode_stage_multi #(
            .CORE_ID(CORE_ID),
            .NUM_CORES(NUM_CORES)
        ) u_decode_stage (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            // ... existing signals ...
            .cache_if(cache_coherent_if.slave),
            .id_ex_reg_o(id_ex_reg)
        );
        
        execute_stage_multi #(
            .CORE_ID(CORE_ID),
            .NUM_CORES(NUM_CORES)
        ) u_execute_stage (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            // ... existing signals ...
            .cache_if(cache_coherent_if.slave),
            .ex_mem_reg_o(ex_mem_reg)
        );
        
        mem_stage_multi #(
            .CORE_ID(CORE_ID),
            .NUM_CORES(NUM_CORES),
            .CACHE_LINE_SIZE(CACHE_LINE_SIZE)
        ) u_mem_stage (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            // ... existing signals ...
            .mem_if(mem_if.slave),
            .cache_if(cache_coherent_if.slave),
            .mem_wb_reg_o(mem_wb_reg)
        );
        
        writeback_stage_multi #(
            .CORE_ID(CORE_ID),
            .NUM_CORES(NUM_CORES)
        ) u_writeback_stage (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            // ... existing signals ...
            .cache_if(cache_coherent_if.slave)
        );
    end
endgenerate
```

## Implementation Roadmap

### Phase 1: Foundation (Current - Q1 2025)
- ✅ Memory wrapper implementation
- ✅ Protocol-agnostic interfaces
- ✅ AXI4 adapter
- ✅ Single-core optimization

### Phase 2: Multi-Core Preparation (Q2 2025)
- [ ] Enhanced cache interfaces
- [ ] Cache coherency protocols
- [ ] Multi-core synchronization primitives
- [ ] Protocol-agnostic pipeline stage templates

### Phase 3: Multi-Core Implementation (Q3 2025)
- [ ] Multi-core pipeline stages
- [ ] Cache coherency implementation
- [ ] Inter-core communication
- [ ] Multi-core testbench

### Phase 4: Integration and Optimization (Q4 2025)
- [ ] Parameter-based switching mechanism
- [ ] Performance optimization
- [ ] Verification and validation
- [ ] Documentation and examples

## Technical Details

### Cache Coherency Protocol

```systemverilog
// Cache coherency interface for multi-core mode
interface cache_if;
    // Cache line state
    typedef enum logic [1:0] {
        CACHE_INVALID = 2'b00,
        CACHE_SHARED  = 2'b01,
        CACHE_MODIFIED = 2'b10,
        CACHE_EXCLUSIVE = 2'b11
    } cache_state_t;
    
    // Coherency request
    logic [NUM_CORES-1:0] req_valid;
    logic [NUM_CORES-1:0] req_ready;
    addr_t [NUM_CORES-1:0] req_addr;
    logic [1:0] [NUM_CORES-1:0] req_type; // READ, WRITE, INVALIDATE
    logic [CORE_ID_WIDTH-1:0] [NUM_CORES-1:0] req_source;
    
    // Coherency response
    logic [NUM_CORES-1:0] rsp_valid;
    logic [NUM_CORES-1:0] rsp_ready;
    cache_state_t [NUM_CORES-1:0] rsp_state;
    word_t [CACHE_LINE_SIZE/4-1:0] [NUM_CORES-1:0] rsp_data;
    
    // Snoop interface
    logic [NUM_CORES-1:0] snoop_valid;
    addr_t [NUM_CORES-1:0] snoop_addr;
    logic [1:0] [NUM_CORES-1:0] snoop_type;
    
    modport master (input req_valid, req_addr, req_type, req_source,
                   output req_ready, rsp_valid, rsp_state, rsp_data, rsp_ready,
                   input snoop_valid, snoop_addr, snoop_type);
    
    modport slave (output req_valid, req_addr, req_type, req_source,
                  input req_ready, rsp_valid, rsp_state, rsp_data, rsp_ready,
                  output snoop_valid, snoop_addr, snoop_type);
endinterface
```

### Multi-Core Pipeline Stages

Each pipeline stage in multi-core mode will include:

1. **Cache Coherency Logic**: Handle cache line state transitions
2. **Inter-Core Synchronization**: Coordinate with other cores
3. **Protocol-Agnostic Memory Interface**: Use memory_req_rsp_if
4. **Core-Specific Configuration**: Core ID, cache parameters, etc.

### Configuration Examples

#### Single-Core AXI4 Configuration
```systemverilog
riscv_core #(
    .RESET_VECTOR(32'h0000_0000),
    .PROTOCOL_TYPE("AXI4"),
    .CORE_MODE("SINGLE_CORE")
) u_riscv_core (
    // ... connections ...
);
```

#### Multi-Core CHI Configuration
```systemverilog
riscv_core #(
    .RESET_VECTOR(32'h0000_0000),
    .PROTOCOL_TYPE("CHI"),
    .CORE_MODE("MULTI_CORE"),
    .CORE_ID(0),
    .NUM_CORES(4),
    .CACHE_LINE_SIZE(64),
    .CACHE_SIZE(32*1024)
) u_riscv_core_0 (
    // ... connections ...
    .cache_coherent_if(cache_coherent_if[0]),
    .mem_if(mem_if[0])
);
```

## Verification Strategy

### Single-Core Verification
- [ ] Memory wrapper testbench
- [ ] Protocol adapter verification
- [ ] Pipeline stage integration tests
- [ ] Performance benchmarks

### Multi-Core Verification
- [ ] Cache coherency protocol verification
- [ ] Multi-core synchronization tests
- [ ] Inter-core communication validation
- [ ] Scalability and performance tests

### Mixed-Mode Verification
- [ ] Parameter switching validation
- [ ] Backward compatibility tests
- [ ] Configuration validation
- [ ] Integration tests

## Conclusion

The parameter-based design approach provides a smooth migration path from single-core to multi-core operation while maintaining backward compatibility. The memory wrapper approach (Option 1) serves as an excellent foundation for the future protocol-agnostic pipeline (Option 2), enabling gradual adoption of multi-core capabilities as needed.

This plan ensures that the RISC-V core can evolve from a simple single-core design to a sophisticated multi-core system without requiring complete redesign, maximizing code reuse and minimizing development risk. 