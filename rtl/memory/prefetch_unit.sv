//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: prefetch_unit.sv
// Module: prefetch_unit
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   A configurable stride-based prefetcher. It monitors a stream of memory
//   access addresses (e.g., from L1 misses or PC updates), detects regular
//   access patterns (strides), and issues speculative prefetch requests for
//   addresses that are likely to be accessed soon, aiming to hide memory latency.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Stride-based prefetching algorithm.
// AI_TAG: FEATURE - Configurable stride detection table size.
// AI_TAG: FEATURE - Confidence mechanism to reduce useless prefetches.
// AI_TAG: INTERNAL_BLOCK - StrideTable - Stores history and state for stride detection.
// AI_TAG: INTERNAL_BLOCK - PrefetchController - FSM to manage prefetch request generation and handshake.

module prefetch_unit #(
    parameter integer ADDR_WIDTH        = 32, // AI_TAG: PARAM_DESC - Width of the addresses in the memory access stream.
    parameter integer STRIDE_TABLE_SIZE = 64, // AI_TAG: PARAM_DESC - Number of entries in the stride detection table.
                                              // AI_TAG: PARAM_USAGE - More entries can track more streams, at the cost of area.
    parameter integer CACHE_LINE_BYTES  = 64  // AI_TAG: PARAM_DESC - The size of a cache line, used for address alignment.
) (
    input  logic clk_i,    // AI_TAG: PORT_DESC - System clock
    input  logic rst_ni,   // AI_TAG: PORT_DESC - Asynchronous active-low reset

    // Memory access stream to monitor (e.g., from L1 miss unit)
    input  logic        access_valid_i,     // AI_TAG: PORT_DESC - A valid address to monitor is present.
    input  logic [ADDR_WIDTH-1:0] access_addr_i,  // AI_TAG: PORT_DESC - The address of the memory access.

    // Prefetch request interface to the memory system (e.g., L2 cache)
    output logic        prefetch_req_valid_o, // AI_TAG: PORT_DESC - A valid prefetch request is being made.
    input  logic        prefetch_req_ready_i, // AI_TAG: PORT_DESC - The memory system is ready for a prefetch request.
    output logic [ADDR_WIDTH-1:0] prefetch_req_addr_o  // AI_TAG: PORT_DESC - The calculated address to prefetch.
);

    localparam TABLE_INDEX_BITS = $clog2(STRIDE_TABLE_SIZE);
    localparam OFFSET_BITS      = $clog2(CACHE_LINE_BYTES);

    // AI_TAG: INTERNAL_STORAGE - stride_entry_t - Structure for a single stride detection entry.
    typedef struct packed {
        logic                  valid;
        logic [ADDR_WIDTH-1:0] last_addr;
        logic signed [ADDR_WIDTH-1:0] stride;
        logic [7:0]            confidence;
    } stride_entry_t;

    stride_entry_t stride_table_r [STRIDE_TABLE_SIZE-1:0], stride_table_ns [STRIDE_TABLE_SIZE-1:0];

    // Prefetch request state
    logic [ADDR_WIDTH-1:0] prefetch_addr_r, prefetch_addr_ns;
    logic                  prefetch_pending_r, prefetch_pending_ns;

    //---------------------------------------------------------------------------
    // Combinational Logic
    //---------------------------------------------------------------------------
    logic [TABLE_INDEX_BITS-1:0]  table_index_c;
    logic signed [ADDR_WIDTH-1:0] detected_stride_c;
    logic                         generate_prefetch_c;
    logic [ADDR_WIDTH-1:0]        new_prefetch_addr_c;
    stride_entry_t                current_entry_c;

    // Simple index into the table based on block address bits, above the offset.
    assign table_index_c = access_addr_i[OFFSET_BITS +: TABLE_INDEX_BITS];

    // Stride detection logic
    assign current_entry_c   = stride_table_r[table_index_c];
    assign detected_stride_c = access_addr_i - current_entry_c.last_addr;
    assign new_prefetch_addr_c = access_addr_i + current_entry_c.stride;

    // A prefetch is generated if confidence is high.
    assign generate_prefetch_c = current_entry_c.valid && (current_entry_c.confidence > 8'hC0);

    // Drive outputs
    assign prefetch_req_valid_o = prefetch_pending_r;
    assign prefetch_req_addr_o  = prefetch_addr_r;

    //---------------------------------------------------------------------------
    // Next-State Logic
    //---------------------------------------------------------------------------
    always_comb begin : proc_next_state_logic
        // Default assignments
        stride_table_ns     = stride_table_r;
        prefetch_pending_ns = prefetch_pending_r;
        prefetch_addr_ns    = prefetch_addr_r;

        // --- Stride Table Update Logic ---
        if (access_valid_i) begin
            stride_entry_t updated_entry;
            updated_entry = current_entry_c; // Start with current values

            if (current_entry_c.valid) begin
                // Entry exists, update confidence based on stride match
                if (detected_stride_c == current_entry_c.stride) begin
                    if (updated_entry.confidence < 8'hFF) begin
                        updated_entry.confidence = current_entry_c.confidence + 1;
                    end
                end else begin
                    // Stride does not match, decrease confidence and update the stride
                    updated_entry.stride = detected_stride_c;
                    if (updated_entry.confidence > 8'h00) begin
                        updated_entry.confidence = current_entry_c.confidence - 1;
                    end
                end
            end else begin
                // No entry for this address region, create a new one
                updated_entry.valid      = 1'b1;
                updated_entry.stride     = detected_stride_c;
                updated_entry.confidence = 8'h80; // Start with medium confidence
            end
            
            // Always update the last seen address
            updated_entry.last_addr = access_addr_i;
            stride_table_ns[table_index_c] = updated_entry;
        end

        // --- Prefetch Generation and Handshake Logic ---
        if (prefetch_pending_r && prefetch_req_ready_i) begin
            // Outstanding prefetch was accepted, clear the pending flag
            prefetch_pending_ns = 1'b0;
        end

        // A new prefetch is triggered by a new access if confidence is high
        // It should not fire if another prefetch is already pending.
        if (access_valid_i && generate_prefetch_c && !prefetch_pending_ns) begin
            prefetch_pending_ns = 1'b1;
            prefetch_addr_ns    = new_prefetch_addr_c;
        end
    end

    //---------------------------------------------------------------------------
    // Sequential Logic
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // Reset stride table
            for (int i = 0; i < STRIDE_TABLE_SIZE; i++) begin
                stride_table_r[i] <= '{default:'0};
            end
            prefetch_pending_r <= 1'b0;
            prefetch_addr_r    <= '0;
        end else begin
            stride_table_r     <= stride_table_ns;
            prefetch_pending_r <= prefetch_pending_ns;
            prefetch_addr_r    <= prefetch_addr_ns;
        end
    end

endmodule : prefetch_unit

//=============================================================================
// Dependencies: None
//
// Performance:
//   - Critical Path: TBD
//   - Max Frequency: TBD
//   - Area: TBD (highly dependent on STRIDE_TABLE_SIZE)
//
// Verification Coverage: N/A
// Synthesis: N/A
// Testing: N/A
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial fleshed-out implementation with robust handshake.
// 0.1.0   | 2025-06-27 | DesignAI           | Initial skeleton release
//=============================================================================

`default_nettype wire 