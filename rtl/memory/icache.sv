//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: icache.sv
// Module: icache
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   L1 instruction cache with configurable size, associativity, and line size.
//   Supports write-through policy, LRU replacement, and performance monitoring.
//   Uses parameterized values from the configuration package for flexibility.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_config_pkg::*;
import riscv_types_pkg::*;
import riscv_cache_types_pkg::*;

module icache #(
    parameter integer CACHE_SIZE = DEFAULT_L1_CACHE_SIZE,    // AI_TAG: PARAM_DESC - Total cache size in bytes.
    parameter integer LINE_SIZE = DEFAULT_CACHE_LINE_SIZE,   // AI_TAG: PARAM_DESC - Cache line size in bytes.
    parameter integer WAYS = DEFAULT_L1_CACHE_WAYS,          // AI_TAG: PARAM_DESC - Number of ways (associativity).
    parameter integer ADDR_WIDTH = 32                        // AI_TAG: PARAM_DESC - Address width.
) (
    // Clock and Reset
    input  logic        clk_i,
    input  logic        rst_ni,

    // CPU Interface
    input  logic        cpu_req_valid_i,  // AI_TAG: PORT_DESC - cpu_req_valid_i - CPU request valid.
    input  addr_t       cpu_req_addr_i,   // AI_TAG: PORT_DESC - cpu_req_addr_i - CPU request address.
    output logic        cpu_req_ready_o,  // AI_TAG: PORT_DESC - cpu_req_ready_o - Cache ready to accept request.
    output logic        cpu_rsp_valid_o,  // AI_TAG: PORT_DESC - cpu_rsp_valid_o - Cache response valid.
    output word_t       cpu_rsp_data_o,   // AI_TAG: PORT_DESC - cpu_rsp_data_o - Cache response data.
    output logic        cpu_rsp_hit_o,    // AI_TAG: PORT_DESC - cpu_rsp_hit_o - Cache hit indicator.

    // Memory Interface
    output logic        mem_req_valid_o,  // AI_TAG: PORT_DESC - mem_req_valid_o - Memory request valid.
    output addr_t       mem_req_addr_o,   // AI_TAG: PORT_DESC - mem_req_addr_o - Memory request address.
    input  logic        mem_req_ready_i,  // AI_TAG: PORT_DESC - mem_req_ready_i - Memory ready for request.
    input  logic        mem_rsp_valid_i,  // AI_TAG: PORT_DESC - mem_rsp_valid_i - Memory response valid.
    input  word_t       mem_rsp_data_i,   // AI_TAG: PORT_DESC - mem_rsp_data_i - Memory response data.

    // Control Interface
    input  logic        flush_i,          // AI_TAG: PORT_DESC - flush_i - Flush cache.
    output logic        flush_done_o,     // AI_TAG: PORT_DESC - flush_done_o - Flush operation complete.

    // Performance Interface
    output logic [31:0] perf_hit_count_o,   // AI_TAG: PORT_DESC - perf_hit_count_o - Number of cache hits.
    output logic [31:0] perf_miss_count_o,  // AI_TAG: PORT_DESC - perf_miss_count_o - Number of cache misses.
    output logic [31:0] perf_hit_rate_o     // AI_TAG: PORT_DESC - perf_hit_rate_o - Cache hit rate (percentage).
);

    // AI_TAG: INTERNAL_CALCULATION - Cache parameters
    localparam integer SETS = CACHE_SIZE / (LINE_SIZE * WAYS);
    localparam integer INDEX_BITS = $clog2(SETS);
    localparam integer OFFSET_BITS = $clog2(LINE_SIZE);
    localparam integer TAG_BITS = ADDR_WIDTH - INDEX_BITS - OFFSET_BITS;
    localparam integer WORDS_PER_LINE = LINE_SIZE / 4;  // 4 bytes per word
    
    // AI_TAG: INTERNAL_STORAGE - Cache line structure
    typedef struct packed {
        logic                    valid;      // Valid bit
        logic [TAG_BITS-1:0]     tag;        // Tag bits
        word_t                   data [WORDS_PER_LINE-1:0];  // Data array
        logic                    lru;        // LRU bit (for 2-way cache)
    } cache_line_t;
    
    // AI_TAG: INTERNAL_STORAGE - Cache memory array (2-way set associative)
    cache_line_t cache_mem [WAYS-1:0][SETS-1:0];
    
    // AI_TAG: INTERNAL_LOGIC - Address decomposition
    logic [INDEX_BITS-1:0]   index;
    logic [OFFSET_BITS-1:0]  offset;
    logic [TAG_BITS-1:0]     tag;
    
    // AI_TAG: INTERNAL_LOGIC - Cache lookup signals
    logic [WAYS-1:0]         way_hit;
    logic [WAYS-1:0]         way_valid;
    logic [WAYS-1:0]         way_tag_match;
    logic                    any_hit;
    logic [$clog2(WAYS)-1:0] hit_way;
    
    // AI_TAG: INTERNAL_LOGIC - Cache state machine
    typedef enum logic [2:0] {
        IDLE,           // Ready for new requests
        MISS_WAIT,      // Waiting for memory response
        MISS_FILL,      // Filling cache line
        FLUSH_STATE     // Flushing cache
    } cache_state_e;
    
    cache_state_e cache_state_r, cache_state_next;
    
    // AI_TAG: INTERNAL_LOGIC - Miss handling signals
    logic                    miss_detected;
    logic [INDEX_BITS-1:0]   miss_index;
    logic [TAG_BITS-1:0]     miss_tag;
    logic [$clog2(WAYS)-1:0] replace_way;
    logic [OFFSET_BITS-1:0]  fill_offset;
    
    // AI_TAG: INTERNAL_STORAGE - Performance counters
    logic [31:0] hit_count_r;
    logic [31:0] miss_count_r;
    logic [31:0] flush_count_r;
    logic [31:0] total_requests_r;

    // AI_TAG: INTERNAL_LOGIC - Address decomposition
    assign index = cpu_req_addr_i[INDEX_BITS+OFFSET_BITS-1:OFFSET_BITS];
    assign offset = cpu_req_addr_i[OFFSET_BITS-1:0];
    assign tag = cpu_req_addr_i[ADDR_WIDTH-1:INDEX_BITS+OFFSET_BITS];

    // AI_TAG: INTERNAL_LOGIC - Cache lookup
    genvar way;
    generate
        for (way = 0; way < WAYS; way++) begin : gen_way_lookup
            assign way_valid[way] = cache_mem[way][index].valid;
            assign way_tag_match[way] = (cache_mem[way][index].tag == tag);
            assign way_hit[way] = way_valid[way] && way_tag_match[way];
        end
    endgenerate

    assign any_hit = |way_hit;
    assign hit_way = $clog2(way_hit); // Priority encoder

    // AI_TAG: INTERNAL_LOGIC - Cache state machine
    always_comb begin
        cache_state_next = cache_state_r;
        miss_detected = 1'b0;
        
        case (cache_state_r)
            IDLE: begin
                if (flush_i) begin
                    cache_state_next = FLUSH_STATE;
                end else if (cpu_req_valid_i && !any_hit) begin
                    cache_state_next = MISS_WAIT;
                    miss_detected = 1'b1;
                end
            end
            
            MISS_WAIT: begin
                if (mem_req_ready_i) begin
                    cache_state_next = MISS_FILL;
                end
            end
            
            MISS_FILL: begin
                if (mem_rsp_valid_i && fill_offset == WORDS_PER_LINE-1) begin
                    cache_state_next = IDLE;
                end
            end
            
            FLUSH_STATE: begin
                cache_state_next = IDLE;
            end
            
            default: cache_state_next = IDLE;
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Cache state register
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            cache_state_r <= IDLE;
        end else begin
            cache_state_r <= cache_state_next;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Cache response generation
    always_comb begin
        if (cache_state_r == IDLE && any_hit) begin
            hit_o = 1'b1;
            valid_o = 1'b1;
            data_o = cache_mem[hit_way][index].data[offset[OFFSET_BITS-1:2]];
        end else if (cache_state_r == MISS_FILL && mem_rsp_valid_i) begin
            hit_o = 1'b0;
            valid_o = 1'b1;
            data_o = mem_rsp_data_i;
        end else begin
            hit_o = 1'b0;
            valid_o = 1'b0;
            data_o = '0;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Memory request generation
    assign mem_req_valid_o = (cache_state_r == MISS_WAIT);
    assign mem_req_addr_o = {miss_tag, miss_index, fill_offset, 2'b00};  // Aligned to word boundary

    // AI_TAG: INTERNAL_LOGIC - Cache fill logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            fill_offset <= '0;
            miss_index <= '0;
            miss_tag <= '0;
            replace_way <= '0;
        end else if (cache_state_r == IDLE && miss_detected) begin
            miss_index <= index;
            miss_tag <= tag;
            fill_offset <= '0;
            // Simple round-robin replacement for 2-way cache
            replace_way <= cache_mem[0][index].lru ? 1'b0 : 1'b1;
        end else if (cache_state_r == MISS_FILL && mem_rsp_valid_i) begin
            cache_mem[replace_way][miss_index].data[fill_offset] <= mem_rsp_data_i;
            fill_offset <= fill_offset + 1;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Cache line update
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int way = 0; way < WAYS; way++) begin
                for (int set = 0; set < SETS; set++) begin
                    cache_mem[way][set].valid <= 1'b0;
                    cache_mem[way][set].lru <= 1'b0;
                end
            end
        end else if (cache_state_r == MISS_FILL && mem_rsp_valid_i && fill_offset == WORDS_PER_LINE-1) begin
            cache_mem[replace_way][miss_index].valid <= 1'b1;
            cache_mem[replace_way][miss_index].tag <= miss_tag;
            cache_mem[replace_way][miss_index].lru <= 1'b1;
            cache_mem[1-replace_way][miss_index].lru <= 1'b0;
        end else if (cache_state_r == FLUSH_STATE) begin
            for (int way = 0; way < WAYS; way++) begin
                for (int set = 0; set < SETS; set++) begin
                    cache_mem[way][set].valid <= 1'b0;
                    cache_mem[way][set].lru <= 1'b0;
                end
            end
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Performance counter update
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            hit_count_r <= '0;
            miss_count_r <= '0;
            flush_count_r <= '0;
            total_requests_r <= '0;
        end else begin
            if (cache_state_r == IDLE && cpu_req_valid_i) begin
                total_requests_r <= total_requests_r + 1;
                if (any_hit) begin
                    hit_count_r <= hit_count_r + 1;
                end else begin
                    miss_count_r <= miss_count_r + 1;
                end
            end
            if (cache_state_r == FLUSH_STATE) begin
                flush_count_r <= flush_count_r + 1;
            end
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Performance output
    assign perf_hit_count_o = hit_count_r;
    assign perf_miss_count_o = miss_count_r;
    assign perf_hit_rate_o = (total_requests_r == 0) ? '0 : (hit_count_r * 100) / total_requests_r;
    assign flush_done_o = (cache_state_r == IDLE);

    // AI_TAG: INTERNAL_LOGIC - CPU interface
    assign cpu_req_ready_o = (cache_state_r == IDLE);
    assign cpu_rsp_valid_o = valid_o;
    assign cpu_rsp_data_o = data_o;
    assign cpu_rsp_hit_o = hit_o;

    // AI_TAG: ASSERTION - Cache size should be power of 2
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - icache_coverage.cache_size_power2_cp
    CacheSizePower2: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        ((CACHE_SIZE & (CACHE_SIZE - 1)) == 0));

    // AI_TAG: ASSERTION - Line size should be power of 2
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - icache_coverage.line_size_power2_cp
    LineSizePower2: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        ((LINE_SIZE & (LINE_SIZE - 1)) == 0));

    // AI_TAG: ASSERTION - Ways should be power of 2
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - icache_coverage.ways_power2_cp
    WaysPower2: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        ((WAYS & (WAYS - 1)) == 0));

endmodule : icache

//=============================================================================
// Dependencies: riscv_config_pkg, riscv_types_pkg, riscv_cache_types_pkg
//
// Performance:
//   - Critical Path: Cache lookup to response
//   - Max Frequency: Depends on cache size and technology
//   - Area: Significant - includes cache memory array
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)
//
// Testing:
//   - Testbench: TBD
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//=============================================================================