//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: l3_cache.sv
// Module: l3_cache
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   A unified L3 cache, acting as a large victim cache for the L2s. It is
//   the last level of cache before going to main memory. It is not expected
//   to be coherent with the L1s directly.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_cache_types_pkg::*;

module l3_cache #(
    parameter int unsigned L3_CACHE_SIZE = DEFAULT_L3_CACHE_SIZE,
    parameter int unsigned CACHE_LINE_SIZE = DEFAULT_CACHE_LINE_SIZE,
    parameter int unsigned NUM_WAYS = DEFAULT_L3_CACHE_WAYS
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Interface to L2 cache
    memory_req_rsp_if.slave l2_if,

    // Interface to Main Memory (e.g., DDR controller)
    memory_req_rsp_if.master mem_if
);

    localparam NUM_SETS = L3_CACHE_SIZE / (CACHE_LINE_SIZE * NUM_WAYS);
    localparam OFFSET_BITS = $clog2(CACHE_LINE_SIZE);
    localparam INDEX_BITS = $clog2(NUM_SETS);
    localparam TAG_BITS = riscv_cache_types_pkg::XLEN - INDEX_BITS - OFFSET_BITS;

    //---------------------------------------------------------------------------
    // L3 Cache Storage
    //---------------------------------------------------------------------------
    typedef logic [TAG_BITS-1:0] tag_t;

    tag_t  l3_tags [NUM_SETS-1:0][NUM_WAYS-1:0];
    logic  l3_valid[NUM_SETS-1:0][NUM_WAYS-1:0];
    logic  l3_dirty[NUM_SETS-1:0][NUM_WAYS-1:0];
    logic [CACHE_LINE_SIZE*8-1:0] l3_data [NUM_SETS-1:0][NUM_WAYS-1:0];

    // Simple round-robin replacement counter for each set
    logic [$clog2(NUM_WAYS)-1:0] replacement_ptr [NUM_SETS-1:0];

    //---------------------------------------------------------------------------
    // FSM for Cache Controller Logic
    //---------------------------------------------------------------------------
    typedef enum logic [3:0] {
        IDLE,
        TAG_CHECK,
        READ_HIT,
        WRITE_HIT,
        EVICT_WRITEBACK,
        WAIT_WRITEBACK_RSP,
        REFILL_READ,
        WAIT_REFILL_RSP,
        SEND_L2_RSP
    } state_e;

    state_e current_state, next_state;

    // Registers to hold request information
    memory_req_t active_req;
    logic [$clog2(NUM_WAYS)-1:0] hit_way;
    logic is_hit;

    // Address decoding
    tag_t  req_tag;
    logic [INDEX_BITS-1:0] req_index;
    assign req_tag = active_req.addr[XLEN-1:INDEX_BITS+OFFSET_BITS];
    assign req_index = active_req.addr[INDEX_BITS+OFFSET_BITS-1:OFFSET_BITS];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            current_state <= IDLE;
            for(int s=0; s<NUM_SETS; s++) begin
                replacement_ptr[s] <= '0;
                for (int w=0; w<NUM_WAYS; w++) begin
                    l3_valid[s][w] <= 1'b0;
                    l3_dirty[s][w] <= 1'b0;
                end
            end
        end else begin
            current_state <= next_state;
            if (l2_if.req_valid && next_state == TAG_CHECK) begin
                active_req <= l2_if.req;
            end
        end
    end

    always_comb begin
        next_state = current_state;
        is_hit = 1'b0;
        hit_way = '0;

        // Default outputs
        l2_if.req_ready = 1'b0;
        l2_if.rsp_valid = 1'b0;
        mem_if.req_valid = 1'b0;

        // Hit-check logic
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (l3_valid[req_index][i] && (l3_tags[req_index][i] == req_tag)) begin
                is_hit = 1'b1;
                hit_way = i;
            end
        end

        case (current_state)
            IDLE: begin
                if (l2_if.req_valid) begin
                    l2_if.req_ready = 1'b1;
                    next_state = TAG_CHECK;
                end
            end
            TAG_CHECK: begin
                if (is_hit) begin
                    next_state = active_req.write ? WRITE_HIT : READ_HIT;
                end else begin // It's a miss
                    logic victim_is_dirty = l3_valid[req_index][replacement_ptr[req_index]] &&
                                            l3_dirty[req_index][replacement_ptr[req_index]];
                    if (victim_is_dirty) begin
                        next_state = EVICT_WRITEBACK;
                    end else begin
                        next_state = REFILL_READ;
                    end
                end
            end
            READ_HIT: begin
                // Data is available, respond to L2
                l2_if.rsp.data = l3_data[req_index][hit_way]; // Simplified: assumes single word
                l2_if.rsp.last = 1'b1; // Simplified
                next_state = SEND_L2_RSP;
            end
            WRITE_HIT: begin
                // Write data and mark as dirty
                l3_data[req_index][hit_way] = active_req.data; // Simplified
                l3_dirty[req_index][hit_way] = 1'b1;
                l2_if.rsp.error = 1'b0;
                next_state = SEND_L2_RSP;
            end
            EVICT_WRITEBACK: begin
                // Issue write request to main memory for the dirty victim line
                mem_if.req_valid = 1'b1;
                // mem_if.req.addr = ... reconstruct victim address
                // mem_if.req.data = l3_data[req_index][replacement_ptr[req_index]];
                // mem_if.req.write = 1'b1;
                if (mem_if.req_ready) begin
                    next_state = WAIT_WRITEBACK_RSP;
                end
            end
            WAIT_WRITEBACK_RSP: begin
                if (mem_if.rsp_valid) begin // Wait for write confirmation
                    next_state = REFILL_READ;
                end
            end
            REFILL_READ: begin
                // Issue read request to main memory for the missed line
                mem_if.req_valid = 1'b1;
                mem_if.req.addr = active_req.addr;
                mem_if.req.write = 1'b0;
                if (mem_if.req_ready) begin
                    next_state = WAIT_REFILL_RSP;
                end
            end
            WAIT_REFILL_RSP: begin
                if (mem_if.rsp_valid) begin
                    // Refill the cache line with data from memory
                    l3_data[req_index][replacement_ptr[req_index]]  = mem_if.rsp.data;
                    l3_tags[req_index][replacement_ptr[req_index]]  = req_tag;
                    l3_valid[req_index][replacement_ptr[req_index]] = 1'b1;
                    l3_dirty[req_index][replacement_ptr[req_index]] = 1'b0;
                    
                    // Update replacement pointer
                    replacement_ptr[req_index] <= replacement_ptr[req_index] + 1;
                    
                    // Now that data is in L3, re-process the original request
                    next_state = TAG_CHECK;
                end
            end
            SEND_L2_RSP: begin
                l2_if.rsp_valid = 1'b1;
                if (l2_if.rsp_ready) begin
                    next_state = IDLE;
                end
            end
            default: begin
                next_state = IDLE;
            end
        endcase
    end

endmodule : l3_cache

`default_nettype wire 