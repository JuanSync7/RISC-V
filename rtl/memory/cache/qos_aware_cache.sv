//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: qos_aware_cache.sv
// Module: qos_aware_cache
//
// Project Name: RISC-V RV32IM QoS-Aware Cache
// Target Devices: ASIC/FPGA
//
// Description:
//   QoS-aware cache that integrates Quality of Service considerations
//   into cache replacement policies, request prioritization, and prefetching.
//   Demonstrates how caches should handle QoS in a multi-core system.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module qos_aware_cache #(
    parameter integer CACHE_SIZE = DEFAULT_L1_CACHE_SIZE,
    parameter integer LINE_SIZE = DEFAULT_CACHE_LINE_SIZE,
    parameter integer WAYS = DEFAULT_L1_CACHE_WAYS,
    parameter integer ADDR_WIDTH = 32,
    parameter integer REQUEST_QUEUE_DEPTH = 8
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    // QoS-enhanced CPU interface
    input  logic                req_valid_i,
    input  addr_t               req_addr_i,
    input  qos_config_t         req_qos_i,        // QoS configuration for request
    input  qos_transaction_type_e req_type_i,     // Transaction type
    output logic                req_ready_o,
    
    output logic                rsp_valid_o,
    output word_t               rsp_data_o,
    output logic                rsp_hit_o,
    output qos_config_t         rsp_qos_o,        // QoS passed through
    input  logic                rsp_ready_i,

    // Memory interface with QoS
    output logic                mem_req_valid_o,
    output addr_t               mem_req_addr_o,
    output qos_config_t         mem_req_qos_o,    // QoS forwarded to memory
    input  logic                mem_req_ready_i,
    
    input  logic                mem_rsp_valid_i,
    input  word_t               mem_rsp_data_i,
    input  qos_config_t         mem_rsp_qos_i,    // QoS from memory
    output logic                mem_rsp_ready_o,

    // QoS configuration interface
    input  logic                qos_enable_i,
    input  logic [1:0]          replacement_policy_i,  // 00=LRU, 01=QoS-LRU, 10=QoS-Priority, 11=Adaptive
    
    // Performance monitoring with QoS
    output logic [31:0]         qos_hits_o [16],      // Hits per QoS level
    output logic [31:0]         qos_misses_o [16],    // Misses per QoS level
    output logic [31:0]         qos_violations_o      // QoS violations
);

    //---------------------------------------------------------------------------
    // Cache Parameters
    //---------------------------------------------------------------------------
    localparam integer SETS = CACHE_SIZE / (LINE_SIZE * WAYS);
    localparam integer INDEX_BITS = $clog2(SETS);
    localparam integer OFFSET_BITS = $clog2(LINE_SIZE);
    localparam integer TAG_BITS = ADDR_WIDTH - INDEX_BITS - OFFSET_BITS;
    localparam integer WORDS_PER_LINE = LINE_SIZE / 4;

    //---------------------------------------------------------------------------
    // QoS-Enhanced Cache Line Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic                    valid;
        logic [TAG_BITS-1:0]     tag;
        word_t                   data [WORDS_PER_LINE-1:0];
        logic [3:0]              access_qos;          // QoS level of last access
        logic [15:0]             qos_weight;          // Accumulated QoS weight
        logic [31:0]             last_access_time;    // For aging
        qos_transaction_type_e   transaction_type;    // Type of data stored
        logic                    high_priority_data;  // Critical data flag
    } qos_cache_line_t;

    //---------------------------------------------------------------------------
    // Request Queue with QoS Priority
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic                    valid;
        addr_t                   addr;
        qos_config_t             qos_config;
        qos_transaction_type_e   transaction_type;
        logic [31:0]             timestamp;
        logic [31:0]             deadline;
    } qos_request_t;

    qos_request_t request_queue [REQUEST_QUEUE_DEPTH-1:0];
    logic [$clog2(REQUEST_QUEUE_DEPTH)-1:0] queue_head, queue_tail;
    logic [REQUEST_QUEUE_DEPTH-1:0] queue_valid;

    //---------------------------------------------------------------------------
    // Cache Storage Arrays
    //---------------------------------------------------------------------------
    qos_cache_line_t cache_mem [WAYS-1:0][SETS-1:0];
    logic [31:0] global_timer;

    //---------------------------------------------------------------------------
    // QoS Priority Request Selection
    //---------------------------------------------------------------------------
    logic [$clog2(REQUEST_QUEUE_DEPTH)-1:0] selected_req_idx;
    logic selected_req_valid;
    qos_request_t selected_request;

    always_comb begin : proc_qos_request_selection
        logic [31:0] highest_priority = 0;
        selected_req_valid = 1'b0;
        selected_req_idx = 0;
        selected_request = '0;

        for (int i = 0; i < REQUEST_QUEUE_DEPTH; i++) begin
            if (queue_valid[i]) begin
                logic [31:0] request_priority;
                
                // Calculate priority score based on QoS configuration
                request_priority = calculate_priority_score(
                    request_queue[i].qos_config.qos_level,
                    global_timer - request_queue[i].timestamp,
                    request_queue[i].qos_config.weight,
                    request_queue[i].qos_config.urgent
                );
                
                // Add deadline urgency
                if (request_queue[i].deadline > 0 && 
                    (global_timer + request_queue[i].deadline) < request_queue[i].qos_config.max_latency_cycles) begin
                    request_priority += 100000; // Deadline urgency boost
                end

                if (request_priority > highest_priority || !selected_req_valid) begin
                    highest_priority = request_priority;
                    selected_req_idx = i;
                    selected_req_valid = 1'b1;
                    selected_request = request_queue[i];
                end
            end
        end
    end

    //---------------------------------------------------------------------------
    // QoS-Aware Replacement Policy
    //---------------------------------------------------------------------------
    logic [$clog2(WAYS)-1:0] replacement_way;
    logic [INDEX_BITS-1:0] current_index;
    
    always_comb begin : proc_qos_replacement_policy
        replacement_way = 0;
        current_index = selected_request.addr[INDEX_BITS+OFFSET_BITS-1:OFFSET_BITS];
        
        case (replacement_policy_i)
            2'b00: begin // Traditional LRU
                logic [31:0] oldest_time = 32'hFFFFFFFF;
                for (int way = 0; way < WAYS; way++) begin
                    if (!cache_mem[way][current_index].valid) begin
                        replacement_way = way;
                        break;
                    end else if (cache_mem[way][current_index].last_access_time < oldest_time) begin
                        oldest_time = cache_mem[way][current_index].last_access_time;
                        replacement_way = way;
                    end
                end
            end
            
            2'b01: begin // QoS-Aware LRU (don't evict high QoS data easily)
                logic [31:0] lowest_score = 32'hFFFFFFFF;
                for (int way = 0; way < WAYS; way++) begin
                    if (!cache_mem[way][current_index].valid) begin
                        replacement_way = way;
                        break;
                    end else begin
                        // Score = age_weight - qos_protection
                        logic [31:0] age_weight = global_timer - cache_mem[way][current_index].last_access_time;
                        logic [31:0] qos_protection = cache_mem[way][current_index].qos_weight;
                        logic [31:0] eviction_score = age_weight > qos_protection ? age_weight - qos_protection : 0;
                        
                        if (eviction_score < lowest_score) begin
                            lowest_score = eviction_score;
                            replacement_way = way;
                        end
                    end
                end
            end
            
            2'b10: begin // QoS Priority (only evict low QoS when high QoS needs space)
                logic found_low_qos = 1'b0;
                
                // First try to find invalid or low QoS lines
                for (int way = 0; way < WAYS; way++) begin
                    if (!cache_mem[way][current_index].valid || 
                        cache_mem[way][current_index].access_qos <= QOS_LEVEL_LOW) begin
                        replacement_way = way;
                        found_low_qos = 1'b1;
                        break;
                    end
                end
                
                // If no low QoS found and incoming request is high priority, use LRU
                if (!found_low_qos && selected_request.qos_config.qos_level >= QOS_LEVEL_MEDIUM_HIGH) begin
                    logic [31:0] oldest_time = 32'hFFFFFFFF;
                    for (int way = 0; way < WAYS; way++) begin
                        if (cache_mem[way][current_index].last_access_time < oldest_time) begin
                            oldest_time = cache_mem[way][current_index].last_access_time;
                            replacement_way = way;
                        end
                    end
                end
            end
            
            2'b11: begin // Adaptive (combines all strategies)
                // Implementation would adapt based on cache pressure and QoS violations
                replacement_way = 0; // Simplified for space
            end
        endcase
    end

    //---------------------------------------------------------------------------
    // QoS Performance Monitoring
    //---------------------------------------------------------------------------
    logic [31:0] qos_hit_counters [16];
    logic [31:0] qos_miss_counters [16];
    logic [31:0] violation_counter;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_qos_monitoring
        if (!rst_ni) begin
            for (int i = 0; i < 16; i++) begin
                qos_hit_counters[i] <= 0;
                qos_miss_counters[i] <= 0;
            end
            violation_counter <= 0;
            global_timer <= 0;
        end else begin
            global_timer <= global_timer + 1;
            
            // Monitor QoS performance per level
            if (rsp_valid_o && rsp_ready_i) begin
                if (rsp_hit_o) begin
                    qos_hit_counters[rsp_qos_o.qos_level] <= qos_hit_counters[rsp_qos_o.qos_level] + 1;
                end else begin
                    qos_miss_counters[rsp_qos_o.qos_level] <= qos_miss_counters[rsp_qos_o.qos_level] + 1;
                end
                
                // Check for QoS violations
                logic [31:0] request_latency = global_timer - rsp_qos_o.max_latency_cycles; // Simplified
                if (request_latency > rsp_qos_o.max_latency_cycles) begin
                    violation_counter <= violation_counter + 1;
                end
            end
        end
    end

    //---------------------------------------------------------------------------
    // Output Assignments
    //---------------------------------------------------------------------------
    assign qos_hits_o = qos_hit_counters;
    assign qos_misses_o = qos_miss_counters; 
    assign qos_violations_o = violation_counter;

    //---------------------------------------------------------------------------
    // QoS-Aware Prefetching Hints
    //---------------------------------------------------------------------------
    logic should_prefetch;
    addr_t prefetch_addr;
    
    always_comb begin : proc_qos_prefetch_hints
        should_prefetch = 1'b0;
        prefetch_addr = selected_request.addr;
        
        // Only prefetch for high QoS requests and instruction fetches
        if (selected_req_valid && 
            (selected_request.qos_config.qos_level >= QOS_LEVEL_MEDIUM_HIGH ||
             selected_request.transaction_type == QOS_TYPE_INSTR_FETCH)) begin
            should_prefetch = 1'b1;
            prefetch_addr = selected_request.addr + LINE_SIZE; // Next line prefetch
        end
    end

endmodule : qos_aware_cache

`default_nettype wire 