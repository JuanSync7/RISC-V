//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: cache_coherency_controller.sv
// Module: cache_coherency_controller
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Manages cache coherency for the L2 cache using a MESI-like protocol.
//   It tracks the state of cache lines across all L1 caches, handles
//   requests from cores, issues snoops, and ensures data consistency.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_mem_types_pkg::*;

module cache_coherency_controller #(
    parameter integer NUM_CORES = 4,
    parameter integer ADDR_WIDTH = 32,
    parameter int unsigned L2_CACHE_WAYS = 8,
    parameter int unsigned L2_CACHE_SETS = 256
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Coherency interface connecting to all L1 caches
    cache_coherency_if.coherency_controller_port coherency_if,

    // Interface to L3/Memory for misses and writebacks
    memory_req_rsp_if.master mem_if,

    // Interface to L2 cache data and tag arrays
    input  logic [L2_CACHE_WAYS-1:0] l2_tag_match_way_i,
    input  cache_state_t             l2_line_state_i,
    input  logic [NUM_CORES-1:0]     l2_sharer_list_i,
    output logic                     l2_update_en_o,
    output logic [$clog2(L2_CACHE_WAYS)-1:0] l2_way_select_o
);

    //---------------------------------------------------------------------------
    // FSM and State Registers
    //---------------------------------------------------------------------------
    typedef enum logic [3:0] {
        IDLE,
        ARBITRATE,
        PROCESS,
        SNOOP,
        WAIT_SNOOP_RSP,
        WRITEBACK,
        WAIT_WB_RSP,
        FETCH_L3,
        WAIT_L3_RSP,
        SEND_RSP
    } state_e;

    state_e current_state, next_state;

    // Registers to hold arbitrated request info
    logic [CORE_ID_WIDTH-1:0]   active_core_id;
    addr_t                      active_addr;
    coherency_req_type_e        active_req_type;
    logic [NUM_CORES-1:0]       snoop_vector;

    // Round-robin arbiter state
    logic [CORE_ID_WIDTH-1:0]   last_granted_core;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            current_state <= IDLE;
            last_granted_core <= '0;
        end else begin
            current_state <= next_state;
            if(next_state == IDLE) begin
                last_granted_core <= last_granted_core + 1;
            end
        end
    end

    always_comb begin
        next_state = current_state;

        // Default outputs
        coherency_if.req_ready = '0;
        coherency_if.snoop_valid = '0;
        coherency_if.rsp_valid = '0;
        mem_if.req_valid = '0;
        l2_update_en_o = 1'b0;

        // Arbitration Logic
        for (int i = 0; i < NUM_CORES; i++) begin
            int core_idx = (last_granted_core + i) % NUM_CORES;
            if(coherency_if.req_valid[core_idx]) begin
                active_core_id = core_idx;
                active_addr = coherency_if.req_addr[core_idx];
                active_req_type = coherency_if.req_type[core_idx];
                break;
            end
        end

        case (current_state)
            IDLE: begin
                if (|coherency_if.req_valid) begin
                    coherency_if.req_ready[active_core_id] = 1'b1;
                    next_state = PROCESS;
                end
            end

            PROCESS: begin
                // Based on the request and L2 directory state, decide action
                logic is_hit = |l2_tag_match_way_i;
                snoop_vector = '0;

                case (active_req_type)
                    COHERENCY_REQ_READ: begin
                        if (is_hit) begin // Read Hit
                             // No snoops needed, L2 has a valid copy.
                             next_state = SEND_RSP;
                        end else begin // Read Miss
                             // Fetch from L3
                             next_state = FETCH_L3;
                        end
                    end
                    COHERENCY_REQ_WRITE: begin
                        if (is_hit) begin // Write Hit
                            if (l2_line_state_i == CACHE_MODIFIED || l2_line_state_i == CACHE_EXCLUSIVE) begin
                                // No other sharers, can write directly
                                next_state = SEND_RSP;
                            end else begin // State is SHARED
                                // Must invalidate other sharers
                                snoop_vector = l2_sharer_list_i & ~(1'b1 << active_core_id);
                                next_state = SNOOP;
                            end
                        end else begin // Write Miss
                            // Fetch from L3, no snoops needed yet as no one has it
                            next_state = FETCH_L3;
                        end
                    end
                    COHERENCY_REQ_UPGRADE: begin // L1 has in 'S', wants to write, needs 'M'
                         // Invalidate other sharers
                        snoop_vector = l2_sharer_list_i & ~(1'b1 << active_core_id);
                        next_state = SNOOP;
                    end
                endcase
            end

            SNOOP: begin
                // Broadcast invalidations or other snoop types
                coherency_if.snoop_valid = snoop_vector;
                coherency_if.snoop_addr = active_addr;
                coherency_if.snoop_type = COHERENCY_REQ_INVALIDATE;
                // A better FSM would wait here until all snoops are accepted
                next_state = WAIT_SNOOP_RSP;
            end
            
            WAIT_SNOOP_RSP: begin
                // Wait for all snooped cores to respond and acknowledge
                if ((coherency_if.snoop_rsp_valid & snoop_vector) == snoop_vector) begin
                    // All acks received. Now we can grant permission.
                    next_state = SEND_RSP;
                end
            end

            FETCH_L3: begin
                mem_if.req_valid = 1'b1;
                mem_if.req.addr = active_addr;
                mem_if.req.write = 1'b0;
                if (mem_if.req_ready) begin
                    next_state = WAIT_L3_RSP;
                end
            end

            WAIT_L3_RSP: begin
                if (mem_if.rsp_valid) begin
                    // We have the data from L3. Update L2 cache
                    l2_update_en_o = 1'b1;
                    // L2 cache logic will take mem_if.rsp.data and write it
                    next_state = SEND_RSP;
                end
            end

            SEND_RSP: begin
                // Send response to the original requesting core
                coherency_if.rsp_valid[active_core_id] = 1'b1;
                // Response state would be calculated here based on FSM path
                if (coherency_if.rsp_ready[active_core_id]) begin
                    next_state = IDLE;
                end
            end

            default: begin
                next_state = IDLE;
            end
        endcase
    end

endmodule : cache_coherency_controller

`default_nettype wire 