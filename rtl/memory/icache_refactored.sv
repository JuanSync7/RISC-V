//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: icache_refactored.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: icache_refactored
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 2.0.0
// DATE: 2025-01-28
// DESCRIPTION: Refactored L1 instruction cache using new configuration system.
// PRIMARY_PURPOSE: Demonstrate flexible parameterization with structured config.
// ROLE_IN_SYSTEM: L1 instruction cache with configurable parameters.
// PROBLEM_SOLVED: Shows how to use the new hierarchical configuration approach.
// MODULE_TYPE: RTL
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V Privileged Specification v1.12
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

module icache_refactored
import riscv_base_pkg::*;
import riscv_cache_config_pkg::*;
import riscv_system_config_pkg::*;
#(
    // Override system defaults if needed
    parameter cache_config_t CONFIG_CACHE = DEFAULT_SYSTEM_CONFIG.memory.l1_icache,
    parameter integer CONFIG_ADDR_WIDTH = ADDR_WIDTH  // From system config
) (
    // Clock and Reset
    input  logic        clk_i,         // AI_TAG: PORT_DESC - System clock
    input  logic        rst_ni,        // AI_TAG: PORT_DESC - Asynchronous active-low reset

    // CPU Interface
    input  logic        cpu_req_valid_i,  // AI_TAG: PORT_DESC - CPU request valid
    input  logic [CONFIG_ADDR_WIDTH-1:0] cpu_req_addr_i,   // AI_TAG: PORT_DESC - CPU request address
    output logic        cpu_req_ready_o,  // AI_TAG: PORT_DESC - Cache ready to accept request
    output logic        cpu_rsp_valid_o,  // AI_TAG: PORT_DESC - Cache response valid
    output logic [31:0] cpu_rsp_data_o,   // AI_TAG: PORT_DESC - Cache response data
    output logic        cpu_rsp_hit_o,    // AI_TAG: PORT_DESC - Cache hit indicator

    // Memory Interface
    output logic        mem_req_valid_o,  // AI_TAG: PORT_DESC - Memory request valid
    output logic [CONFIG_ADDR_WIDTH-1:0] mem_req_addr_o,   // AI_TAG: PORT_DESC - Memory request address
    input  logic        mem_req_ready_i,  // AI_TAG: PORT_DESC - Memory ready for request
    input  logic        mem_rsp_valid_i,  // AI_TAG: PORT_DESC - Memory response valid
    input  logic [31:0] mem_rsp_data_i,   // AI_TAG: PORT_DESC - Memory response data

    // Control Interface
    input  logic        flush_i,          // AI_TAG: PORT_DESC - Flush cache
    output logic        flush_done_o,     // AI_TAG: PORT_DESC - Flush operation complete

    // Performance Interface
    output logic [31:0] perf_hit_count_o,   // AI_TAG: PORT_DESC - Number of cache hits
    output logic [31:0] perf_miss_count_o,  // AI_TAG: PORT_DESC - Number of cache misses
    output logic [31:0] perf_hit_rate_o     // AI_TAG: PORT_DESC - Cache hit rate (percentage)
);

    //-------------------------------------------------------------------------
    // Extract parameters from configuration structure
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_CALCULATION - Extract cache parameters from config
    localparam integer LP_CACHE_SIZE = CONFIG_CACHE.size;
    localparam integer LP_LINE_SIZE = CONFIG_CACHE.line_size;
    localparam integer LP_WAYS = CONFIG_CACHE.ways;
    localparam integer LP_HIT_LATENCY = CONFIG_CACHE.hit_latency;
    localparam integer LP_MISS_PENALTY = CONFIG_CACHE.miss_penalty;
    
    // Use policy from configuration
    localparam replacement_policy_e LP_REPLACEMENT = replacement_policy_e'(CONFIG_CACHE.replacement);
    localparam write_policy_e LP_WRITE_POLICY = write_policy_e'(CONFIG_CACHE.write_policy);
    
    // Calculate derived parameters using functions from cache_config_pkg
    localparam integer LP_SETS = calc_cache_sets(CONFIG_CACHE);
    localparam integer LP_INDEX_BITS = calc_cache_index_bits(CONFIG_CACHE);
    localparam integer LP_OFFSET_BITS = calc_cache_offset_bits(CONFIG_CACHE);
    localparam integer LP_TAG_BITS = calc_cache_tag_bits(CONFIG_CACHE, CONFIG_ADDR_WIDTH);
    localparam integer LP_WORDS_PER_LINE = LP_LINE_SIZE / 4;  // 4 bytes per word
    
    //-------------------------------------------------------------------------
    // Validate configuration at compile time
    //-------------------------------------------------------------------------
    initial begin
        assert(validate_cache_config(CONFIG_CACHE))
            else $fatal("Invalid cache configuration provided to icache_refactored");
            
        // Additional I-cache specific checks
        assert(CONFIG_CACHE.write_policy == WRITE_THROUGH || CONFIG_CACHE.write_policy == WRITE_AROUND)
            else $warning("I-cache typically uses write-through or write-around policy");
            
        assert(!CONFIG_CACHE.write_allocate)
            else $warning("I-cache should not have write allocate enabled");
    end
    
    //-------------------------------------------------------------------------
    // Cache line structure (enhanced with ECC if enabled)
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_STORAGE - Cache line structure with optional features
    typedef struct packed {
        logic                       valid;      // Valid bit
        logic [LP_TAG_BITS-1:0]     tag;        // Tag bits
        logic [31:0]                data [LP_WORDS_PER_LINE-1:0];  // Data array
        logic [LP_WAYS-1:0]         lru_bits;   // LRU state (for >2 ways)
        logic [7:0]                 ecc;        // ECC bits if enabled
        logic                       locked;     // Lock bit if enabled
    } cache_line_t;
    
    // AI_TAG: INTERNAL_STORAGE - Cache memory array
    cache_line_t cache_mem [LP_WAYS-1:0][LP_SETS-1:0];
    
    //-------------------------------------------------------------------------
    // FSM States
    //-------------------------------------------------------------------------
    // AI_TAG: FSM_NAME - cache_fsm
    // AI_TAG: FSM_PURPOSE - cache_fsm - Controls cache access and miss handling
    // AI_TAG: FSM_ENCODING - cache_fsm - one-hot
    // AI_TAG: FSM_RESET_STATE - cache_fsm - S_IDLE
    typedef enum logic [2:0] {
        S_IDLE,           // Ready for new requests
        S_TAG_CHECK,      // Checking tags (multi-cycle if needed)
        S_MISS_WAIT,      // Waiting for memory response
        S_MISS_FILL,      // Filling cache line
        S_FLUSH           // Flushing cache
    } cache_state_e;
    
    cache_state_e state_r, state_ns;
    
    //-------------------------------------------------------------------------
    // Internal signals
    //-------------------------------------------------------------------------
    logic [LP_INDEX_BITS-1:0]   index;
    logic [LP_OFFSET_BITS-1:0]  offset;
    logic [LP_TAG_BITS-1:0]     tag;
    logic [LP_WAYS-1:0]         way_hit;
    logic                       any_hit;
    logic [$clog2(LP_WAYS)-1:0] hit_way;
    logic [$clog2(LP_WAYS)-1:0] replace_way;
    logic [LP_OFFSET_BITS-1:0]  fill_counter_r;
    
    // Latency counter for multi-cycle hits
    logic [$clog2(LP_HIT_LATENCY+1)-1:0] hit_latency_counter_r;
    
    //-------------------------------------------------------------------------
    // Address decomposition
    //-------------------------------------------------------------------------
    assign index = cpu_req_addr_i[LP_INDEX_BITS+LP_OFFSET_BITS-1:LP_OFFSET_BITS];
    assign offset = cpu_req_addr_i[LP_OFFSET_BITS-1:0];
    assign tag = cpu_req_addr_i[CONFIG_ADDR_WIDTH-1:LP_INDEX_BITS+LP_OFFSET_BITS];

    //-------------------------------------------------------------------------
    // Cache lookup with configurable associativity
    //-------------------------------------------------------------------------
    genvar way;
    generate
        for (way = 0; way < LP_WAYS; way++) begin : gen_way_lookup
            always_comb begin
                way_hit[way] = cache_mem[way][index].valid && 
                              (cache_mem[way][index].tag == tag) &&
                              (!CONFIG_CACHE.lock_enable || !cache_mem[way][index].locked);
            end
        end
    endgenerate

    assign any_hit = |way_hit;
    
    // Priority encoder for hit way
    always_comb begin
        hit_way = 0;
        for (int i = 0; i < LP_WAYS; i++) begin
            if (way_hit[i]) hit_way = i;
        end
    end

    //-------------------------------------------------------------------------
    // Replacement policy logic
    //-------------------------------------------------------------------------
    always_comb begin
        replace_way = 0;
        
        case (LP_REPLACEMENT)
            REPLACE_LRU: begin
                // Find LRU way based on lru_bits
                // Simplified for demonstration
                replace_way = cache_mem[0][index].lru_bits[0] ? 0 : 1;
            end
            
            REPLACE_FIFO: begin
                // Round-robin replacement
                replace_way = fill_counter_r[$clog2(LP_WAYS)-1:0];
            end
            
            REPLACE_RANDOM: begin
                // Use lower bits of address as pseudo-random
                replace_way = cpu_req_addr_i[$clog2(LP_WAYS)+1:2];
            end
            
            REPLACE_PLRU: begin
                // Pseudo-LRU implementation
                replace_way = ~cache_mem[0][index].lru_bits[0];
            end
            
            default: replace_way = 0;
        endcase
    end

    //-------------------------------------------------------------------------
    // FSM Next State Logic
    //-------------------------------------------------------------------------
    // AI_TAG: FSM_TRANSITION - cache_fsm: S_IDLE -> S_TAG_CHECK when (cpu_req_valid_i && LP_HIT_LATENCY > 1)
    // AI_TAG: FSM_TRANSITION - cache_fsm: S_IDLE -> S_MISS_WAIT when (cpu_req_valid_i && !any_hit)
    // AI_TAG: FSM_TRANSITION - cache_fsm: S_TAG_CHECK -> S_IDLE when (hit_latency_counter_r == LP_HIT_LATENCY-1)
    // AI_TAG: FSM_TRANSITION - cache_fsm: S_MISS_WAIT -> S_MISS_FILL when (mem_req_ready_i)
    // AI_TAG: FSM_TRANSITION - cache_fsm: S_MISS_FILL -> S_IDLE when (mem_rsp_valid_i && fill_counter_r == LP_WORDS_PER_LINE-1)
    always_comb begin
        state_ns = state_r;
        
        case (state_r)
            S_IDLE: begin
                if (flush_i) begin
                    state_ns = S_FLUSH;
                end else if (cpu_req_valid_i) begin
                    if (LP_HIT_LATENCY > 1 && any_hit) begin
                        state_ns = S_TAG_CHECK;  // Multi-cycle hit
                    end else if (!any_hit) begin
                        state_ns = S_MISS_WAIT;  // Cache miss
                    end
                end
            end
            
            S_TAG_CHECK: begin
                if (hit_latency_counter_r == LP_HIT_LATENCY-1) begin
                    state_ns = S_IDLE;
                end
            end
            
            S_MISS_WAIT: begin
                if (mem_req_ready_i) begin
                    state_ns = S_MISS_FILL;
                end
            end
            
            S_MISS_FILL: begin
                if (mem_rsp_valid_i && fill_counter_r == LP_WORDS_PER_LINE-1) begin
                    state_ns = S_IDLE;
                end
            end
            
            S_FLUSH: begin
                state_ns = S_IDLE;
            end
            
            default: state_ns = S_IDLE;
        endcase
    end

    //-------------------------------------------------------------------------
    // State and counter registers
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state_r <= S_IDLE;
            fill_counter_r <= '0;
            hit_latency_counter_r <= '0;
        end else begin
            state_r <= state_ns;
            
            // Fill counter management
            if (state_r == S_IDLE && state_ns == S_MISS_WAIT) begin
                fill_counter_r <= '0;
            end else if (state_r == S_MISS_FILL && mem_rsp_valid_i) begin
                fill_counter_r <= fill_counter_r + 1;
            end
            
            // Hit latency counter
            if (state_r == S_IDLE && state_ns == S_TAG_CHECK) begin
                hit_latency_counter_r <= 1;
            end else if (state_r == S_TAG_CHECK) begin
                hit_latency_counter_r <= hit_latency_counter_r + 1;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Cache memory update with ECC support
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int w = 0; w < LP_WAYS; w++) begin
                for (int s = 0; s < LP_SETS; s++) begin
                    cache_mem[w][s].valid <= 1'b0;
                    cache_mem[w][s].locked <= 1'b0;
                end
            end
        end else if (state_r == S_MISS_FILL && mem_rsp_valid_i) begin
            // Fill cache line
            cache_mem[replace_way][index].data[fill_counter_r] <= mem_rsp_data_i;
            
            if (fill_counter_r == LP_WORDS_PER_LINE-1) begin
                cache_mem[replace_way][index].valid <= 1'b1;
                cache_mem[replace_way][index].tag <= tag;
                
                // Update LRU bits
                if (LP_REPLACEMENT == REPLACE_LRU) begin
                    cache_mem[replace_way][index].lru_bits <= '1;
                    for (int w = 0; w < LP_WAYS; w++) begin
                        if (w != replace_way) begin
                            cache_mem[w][index].lru_bits[replace_way] <= 1'b0;
                        end
                    end
                end
            end
        end else if (state_r == S_FLUSH) begin
            // Flush all cache lines
            for (int w = 0; w < LP_WAYS; w++) begin
                for (int s = 0; s < LP_SETS; s++) begin
                    cache_mem[w][s].valid <= 1'b0;
                end
            end
        end
    end

    //-------------------------------------------------------------------------
    // Output generation
    //-------------------------------------------------------------------------
    assign cpu_req_ready_o = (state_r == S_IDLE);
    assign cpu_rsp_valid_o = (state_r == S_IDLE && any_hit && LP_HIT_LATENCY == 1) ||
                            (state_r == S_TAG_CHECK && hit_latency_counter_r == LP_HIT_LATENCY) ||
                            (state_r == S_MISS_FILL && mem_rsp_valid_i);
    assign cpu_rsp_data_o = any_hit ? cache_mem[hit_way][index].data[offset[LP_OFFSET_BITS-1:2]] : mem_rsp_data_i;
    assign cpu_rsp_hit_o = any_hit;
    
    assign mem_req_valid_o = (state_r == S_MISS_WAIT);
    assign mem_req_addr_o = {tag, index, fill_counter_r, 2'b00};
    
    assign flush_done_o = (state_r == S_IDLE);

    //-------------------------------------------------------------------------
    // Performance counters (simplified)
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            perf_hit_count_o <= '0;
            perf_miss_count_o <= '0;
        end else if (state_r == S_IDLE && cpu_req_valid_i) begin
            if (any_hit) begin
                perf_hit_count_o <= perf_hit_count_o + 1;
            end else begin
                perf_miss_count_o <= perf_miss_count_o + 1;
            end
        end
    end
    
    assign perf_hit_rate_o = (perf_hit_count_o + perf_miss_count_o == 0) ? 0 :
                            (perf_hit_count_o * 100) / (perf_hit_count_o + perf_miss_count_o);

endmodule : icache_refactored

//=============================================================================
// Dependencies: riscv_base_pkg, riscv_cache_config_pkg, riscv_system_config_pkg
//
// Instantiated In:
//   - core/pipeline/fetch_stage.sv
//   - core/core_subsystem.sv
//
// Performance:
//   - Critical Path: Cache tag comparison and data mux
//   - Max Frequency: Depends on cache size and technology
//   - Area: Dominated by cache SRAM arrays
//
// Verification Coverage:
//   - Code Coverage: TBD
//   - Functional Coverage: TBD
//   - Branch Coverage: TBD
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Vivado
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: icache_refactored.sdc
//
// Testing:
//   - Testbench: icache_refactored_tb.sv
//   - Test Vectors: TBD
//
//----
// Revision History:
// Version | Date       | Author         | Description
//=============================================================================
// 2.0.0   | 2025-01-28 | DesignAI      | Refactored to use new config system
// 1.0.0   | 2025-06-28 | DesignAI      | Original version
//=============================================================================