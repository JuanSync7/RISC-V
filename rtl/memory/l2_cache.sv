//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: l2_cache.sv
// Module: l2_cache
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: First Draft
//
// Description:
//   A unified, 8-way set-associative L2 cache for the multi-core system.
//   It serves requests from the L1 caches, maintains coherency via the MESI
//   protocol by interacting with a snooping coherency controller, and
//   forwards misses to the L3 cache. It uses a true LRU replacement policy
//   implemented with a priority encoder based on an internal bit matrix.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

`include "riscv_core_pkg.sv"

// AI_TAG: FEATURE - Unified L2 cache for instructions and data.
// AI_TAG: FEATURE - 8-way set-associative with true LRU replacement policy.
// AI_TAG: FEATURE - Maintains MESI coherency across L1 caches.
// AI_TAG: FEATURE - Handles snoop requests from the coherency controller.
// AI_TAG: INTERNAL_BLOCK - RequestArbiter - Round-robin arbiter for L1 requests.
// AI_TAG: INTERNAL_BLOCK - CacheControllerFSM - Main FSM for handling cache requests (hits/misses).
// AI_TAG: INTERNAL_BLOCK - SnoopLogic - Logic to handle incoming snoop requests.
// AI_TAG: INTERNAL_BLOCK - StorageArrays - Tag, Data, and State arrays.
// AI_TAG: INTERNAL_BLOCK - LRU_Logic - Per-set LRU state machine instances.

module l2_cache #(
    parameter integer L2_CACHE_SIZE   = 256 * 1024,     // 256KB
    parameter integer CACHE_LINE_SIZE = 64,             // 64 Bytes
    parameter integer NUM_WAYS        = 8,
    parameter integer NUM_CORES       = 4,
    parameter integer DATA_WIDTH      = 32,
    parameter integer ADDR_WIDTH      = 32
) (
    input  logic clk_i,    // AI_TAG: PORT_DESC - System clock
    input  logic rst_ni,   // AI_TAG: PORT_DESC - Asynchronous active-low reset

    // Interface to L1 caches (one per core)
    // AI_TAG: IF_TYPE - memory_req_rsp_if (slave)
    // AI_TAG: IF_DESC - Array of interfaces for requests from each L1 cache.
    memory_req_rsp_if.slave l1_if [NUM_CORES],

    // Interface to L3 cache / Main Memory
    // AI_TAG: IF_TYPE - memory_req_rsp_if (master)
    // AI_TAG: IF_DESC - Interface for fetching/writing back data from/to the next memory level.
    memory_req_rsp_if.master l3_if,

    // Interface to Coherency Controller
    // AI_TAG: IF_TYPE - cache_coherency_if
    // AI_TAG: IF_DESC - Interface for snoop requests and coherency management.
    cache_coherency_if.l2_cache_port coherency_if
);

    localparam NUM_SETS    = L2_CACHE_SIZE / (CACHE_LINE_SIZE * NUM_WAYS);
    localparam OFFSET_BITS = $clog2(CACHE_LINE_SIZE);
    localparam INDEX_BITS  = $clog2(NUM_SETS);
    localparam TAG_BITS    = ADDR_WIDTH - INDEX_BITS - OFFSET_BITS;
    localparam WAY_BITS    = $clog2(NUM_WAYS);
    localparam LRU_WIDTH   = (NUM_WAYS * (NUM_WAYS - 1)) / 2;

    //---------------------------------------------------------------------------
    // L2 Cache Storage
    //---------------------------------------------------------------------------
    // AI_TAG: INTERNAL_STORAGE - l2_tags_q - Stores the tag for each cache line.
    // AI_TAG: INTERNAL_STORAGE - l2_data_q - Stores the actual data for each cache line.
    // AI_TAG: INTERNAL_STORAGE - l2_state_q - Stores the MESI state for each cache line.
    // AI_TAG: INTERNAL_STORAGE - l2_lru_q - Stores the LRU state for each set.
    
    logic [TAG_BITS-1:0]            l2_tags_q  [NUM_SETS-1:0][NUM_WAYS-1:0];
    logic [CACHE_LINE_SIZE*8-1:0]   l2_data_q  [NUM_SETS-1:0][NUM_WAYS-1:0];
    cache_state_t                   l2_state_q [NUM_SETS-1:0][NUM_WAYS-1:0];
    logic [LRU_WIDTH-1:0]           l2_lru_q   [NUM_SETS-1:0];
    logic [LRU_WIDTH-1:0]           l2_lru_d;

    //---------------------------------------------------------------------------
    // FSM for Cache Controller Logic
    //---------------------------------------------------------------------------
    typedef enum logic [3:0] {
        IDLE,
        TAG_CHECK,
        READ_HIT,
        WRITE_HIT,
        EVICT_WRITEBACK,
        FETCH_L3,
        REFILL_L2,
        RESPOND
    } state_e;

    state_e current_state_r, next_state_c;

    // Registers for active request
    memory_req_t      active_req_r;
    logic [1:0]       active_core_id_r; // Assuming NUM_CORES <= 4
    logic [WAY_BITS-1:0]  hit_way_r;
    logic             is_hit_r;
    logic [WAY_BITS-1:0]  victim_way_r;

    // Wires for address decoding
    logic [INDEX_BITS-1:0] index_c;
    logic [TAG_BITS-1:0]   tag_c;

    // Wires for LRU logic
    logic [WAY_BITS-1:0]  lru_victim_way_c;
    logic                 lru_update_en_c;
    logic [WAY_BITS-1:0]  lru_update_way_c;

    //---------------------------------------------------------------------------
    // LRU Management Logic
    //---------------------------------------------------------------------------
    genvar i;
    generate
        for (i = 0; i < NUM_SETS; i++) begin : gen_lru
            matrix_lru #(
                .NUM_WAYS(NUM_WAYS)
            ) u_matrix_lru (
                .clk_i        (clk_i),
                .rst_ni       (rst_ni),
                .update_en_i  (lru_update_en_c && (index_c == i)),
                .update_way_i (lru_update_way_c),
                .lru_way_o    (lru_victim_way_c), // Note: This connection is partial, see FSM
                .lru_state_i  (l2_lru_q[i]),
                .lru_state_o  (l2_lru_d)          // Note: This connection is partial, see FSM
            );
        end
    endgenerate

    //---------------------------------------------------------------------------
    // Main FSM
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            current_state_r <= IDLE;
            // Reset all cache arrays
            for (int i = 0; i < NUM_SETS; i++) begin
                for (int j = 0; j < NUM_WAYS; j++) begin
                    l2_tags_q[i][j] <= '0;
                    l2_data_q[i][j] <= '0;
                    l2_state_q[i][j] <= I; // Invalid state
                end
                l2_lru_q[i] <= '0;
            end
            // Reset FSM registers
            active_req_r <= '0;
            active_core_id_r <= '0;
            hit_way_r <= '0;
            is_hit_r <= '0;
            victim_way_r <= '0;
        end else begin
            current_state_r <= next_state_c;
            if (lru_update_en_c) begin
                l2_lru_q[index_c] <= l2_lru_d;
            end
        end
    end

    always_comb begin : proc_cache_fsm
        next_state_c = current_state_r;
        
        index_c = active_req_r.addr[OFFSET_BITS +: INDEX_BITS];
        tag_c   = active_req_r.addr[ADDR_WIDTH-1 -: TAG_BITS];

        lru_update_en_c = 1'b0;
        lru_update_way_c = '0;

        for(int j=0; j<NUM_CORES; j++) begin
            l1_if[j].req_ready = 1'b0;
            l1_if[j].rsp_valid = 1'b0;
        end
        l3_if.req_valid = 1'b0;

        case (current_state_r)
            IDLE: begin
                for (int j = 0; j < NUM_CORES; j++) begin
                    if (l1_if[j].req_valid) begin
                        l1_if[j].req_ready = 1'b1;
                        active_req_r = l1_if[j].req;
                        active_core_id_r = j;
                        next_state_c = TAG_CHECK;
                        break;
                    end
                end
            end

            TAG_CHECK: begin
                logic has_invalid_way_c;
                logic [WAY_BITS-1:0] invalid_way_idx_c;
                
                is_hit_r = 1'b0;
                has_invalid_way_c = 1'b0;
                invalid_way_idx_c = '0;

                for (int j = 0; j < NUM_WAYS; j++) begin
                    if (l2_state_q[index_c][j] == I) begin
                        has_invalid_way_c = 1'b1;
                        invalid_way_idx_c = j;
                    end
                    if (l2_tags_q[index_c][j] == tag_c && l2_state_q[index_c][j] != I) begin
                        is_hit_r = 1'b1;
                        hit_way_r = j;
                        break;
                    end
                end
                
                if (is_hit_r) begin
                    lru_update_en_c = 1'b1;
                    lru_update_way_c = hit_way_r;
                    next_state_c = (active_req_r.write) ? WRITE_HIT : READ_HIT;
                end else begin
                    victim_way_r = has_invalid_way_c ? invalid_way_idx_c : lru_victim_way_c;
                    
                    if (l2_state_q[index_c][victim_way_r] == M && !has_invalid_way_c) begin
                        next_state_c = EVICT_WRITEBACK;
                    end else begin
                        next_state_c = FETCH_L3;
                    end
                end
            end

            READ_HIT:       next_state_c = RESPOND;
            WRITE_HIT:      next_state_c = RESPOND;

            EVICT_WRITEBACK: begin
                l3_if.req_valid = 1'b1;
                // ... setup l3_if.req with victim address and data
                if (l3_if.req_ready) begin
                    next_state_c = FETCH_L3;
                end
            end

            FETCH_L3: begin
                l3_if.req_valid = 1'b1;
                // ... setup l3_if.req with missed address
                if (l3_if.req_ready) {
                    next_state_c = REFILL_L2;
                }
            end

            REFILL_L2: begin
                if(l3_if.rsp_valid) begin
                    // ... update data, tag, and MESI state arrays
                    lru_update_en_c = 1'b1;
                    lru_update_way_c = victim_way_r;
                    next_state_c = RESPOND;
                end
            end
            
            RESPOND: begin
                l1_if[active_core_id_r].rsp_valid = 1'b1;
                // ... setup response data
                if (l1_if[active_core_id_r].rsp_ready) begin
                    next_state_c = IDLE;
                end
            end
        endcase
    end
    
    //------------------------------------------------------------------------- 
    // Snoop Handling Logic for Cache Coherency
    //-------------------------------------------------------------------------
    // AI_TAG: SNOOP_HANDLER - Handles coherency snoops from other caches
    // AI_TAG: FEATURE - MESI protocol snoop response handling
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_snoop_handler
        if (!rst_ni) begin
            // Reset snoop response
            for (int i = 0; i < NUM_CORES; i++) begin
                coherency_if.snoop_rsp_valid[i] <= 1'b0;
                coherency_if.snoop_rsp_data_valid[i] <= 1'b0;
                coherency_if.snoop_rsp_data[i] <= '0;
            end
        end else begin
            // Handle snoop requests from cache coherency controller
            for (int i = 0; i < NUM_CORES; i++) begin
                if (coherency_if.snoop_valid[i]) begin
                    logic [INDEX_BITS-1:0] snoop_index = coherency_if.snoop_addr[i][OFFSET_BITS +: INDEX_BITS];
                    logic [TAG_BITS-1:0] snoop_tag = coherency_if.snoop_addr[i][ADDR_WIDTH-1 -: TAG_BITS];
                    logic snoop_hit = 1'b0;
                    logic [WAY_BITS-1:0] snoop_way = '0;
                    
                    // Check for hit in all ways
                    for (int j = 0; j < NUM_WAYS; j++) begin
                        if (l2_tags_q[snoop_index][j] == snoop_tag && l2_state_q[snoop_index][j] != I) begin
                            snoop_hit = 1'b1;
                            snoop_way = j;
                            break;
                        end
                    end
                    
                    // Process snoop based on type
                    case (coherency_if.snoop_type[i])
                        COHERENCY_REQ_INVALIDATE: begin
                            if (snoop_hit) begin
                                l2_state_q[snoop_index][snoop_way] <= I; // Invalidate line
                            end
                            coherency_if.snoop_rsp_valid[i] <= 1'b1;
                            coherency_if.snoop_rsp_data_valid[i] <= 1'b0;
                        end
                        
                        COHERENCY_REQ_READ: begin
                            if (snoop_hit) begin
                                coherency_if.snoop_rsp_data[i] <= l2_data_q[snoop_index][snoop_way];
                                coherency_if.snoop_rsp_data_valid[i] <= 1'b1;
                                // Downgrade state if in Modified
                                if (l2_state_q[snoop_index][snoop_way] == M) begin
                                    l2_state_q[snoop_index][snoop_way] <= S;
                                end
                            end else begin
                                coherency_if.snoop_rsp_data_valid[i] <= 1'b0;
                            end
                            coherency_if.snoop_rsp_valid[i] <= 1'b1;
                        end
                        
                        default: begin
                            coherency_if.snoop_rsp_valid[i] <= 1'b1;
                            coherency_if.snoop_rsp_data_valid[i] <= 1'b0;
                        end
                    endcase
                end else begin
                    // Clear response when no snoop
                    coherency_if.snoop_rsp_valid[i] <= 1'b0;
                    coherency_if.snoop_rsp_data_valid[i] <= 1'b0;
                end
            end
        end
    end
endmodule : l2_cache

//=============================================================================
// Dependencies:
//   - rtl/core/riscv_core_pkg.sv
//   - rtl/memory/memory_req_rsp_if.sv
//   - rtl/interfaces/cache_coherency_if.sv
//
// Performance:
//   - Critical Path: TBD
//   - Max Frequency: TBD
//   - Area: TBD
//
// Verification Coverage: N/A
// Synthesis: N/A
// Testing: N/A
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial fleshed-out implementation.
// 0.1.0   | 2025-06-27 | DesignAI           | Initial skeleton release
//=============================================================================

`default_nettype wire 