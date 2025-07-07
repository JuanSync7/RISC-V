//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: dcache.sv
// Module: dcache
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Direct-mapped Data Cache (D-Cache) for the RISC-V core.
//   Handles load and store requests from the CPU and interacts with the
//   memory wrapper for cache misses.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

import riscv_mem_types_pkg::*;
import riscv_cache_types_pkg::*;

module dcache #(
    parameter integer DCACHE_SIZE = DEFAULT_DCACHE_SIZE,
    parameter integer DCACHE_LINE_SIZE = DEFAULT_CACHE_LINE_SIZE,
    parameter integer DCACHE_WAYS = DEFAULT_DCACHE_WAYS,
    parameter integer PADDR_WIDTH = ADDR_WIDTH
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    // CPU Interface (from Memory Stage)
    input  logic        req_valid_i,
    output logic        req_ready_o,
    input  logic [PADDR_WIDTH-1:0] req_addr_i,
    input  logic        req_write_i,
    input  word_t       req_wdata_i,
    input  logic [3:0]  req_wstrb_i,
    output logic        rsp_valid_o,
    input  logic        rsp_ready_i,
    output word_t       rsp_rdata_o,
    output logic        rsp_error_o,

    // Memory Interface (to Memory Wrapper)
    output logic        mem_req_valid_o,
    input  logic        mem_req_ready_i,
    output memory_req_t mem_req_o,
    input  logic        mem_rsp_valid_i,
    output logic        mem_rsp_ready_o,
    input  memory_rsp_t mem_rsp_i
);

    // Cache parameters calculation
    localparam integer NUM_SETS = DCACHE_SIZE / (DCACHE_LINE_SIZE * DCACHE_WAYS);
    localparam integer OFFSET_BITS = $clog2(DCACHE_LINE_SIZE);
    localparam integer INDEX_BITS = $clog2(NUM_SETS);
    localparam integer TAG_BITS = PADDR_WIDTH - OFFSET_BITS - INDEX_BITS;

    // Cache line structure
    typedef struct packed {
        logic        valid; // Valid bit
        logic        dirty; // Dirty bit
        logic [TAG_BITS-1:0] tag;   // Tag
        logic [DCACHE_LINE_SIZE*8-1:0] data;  // Data line
    } cache_line_t;

    // Cache memory
    cache_line_t cache_mem [NUM_SETS-1:0];

    // State machine for cache operations
    typedef enum logic [2:0] {
        IDLE,
        LOOKUP,
        READ_MISS,
        WRITE_MISS,
        WRITE_BACK,
        ALLOCATE
    } cache_state_e;

    cache_state_e current_state, next_state;

    // Internal signals
    addr_t       cpu_req_addr_q;
    logic        cpu_req_write_q;
    word_t       cpu_req_wdata_q;
    logic [3:0]  cpu_req_wstrb_q;
    logic        cpu_req_valid_q;

    logic [TAG_BITS-1:0]   req_tag;
    logic [INDEX_BITS-1:0] req_index;
    logic [OFFSET_BITS-1:0] req_offset;

    logic        hit;
    word_t       read_data;
    logic        error;

    // Assign address components
    assign req_offset = req_addr_i[OFFSET_BITS-1:0];
    assign req_index  = req_addr_i[OFFSET_BITS+INDEX_BITS-1:OFFSET_BITS];
    assign req_tag    = req_addr_i[ADDR_WIDTH-1:OFFSET_BITS+INDEX_BITS];

    // Cache lookup logic
    always_comb begin
        hit = 1'b0;
        read_data = '0;
        error = 1'b0;

        if (cache_mem[req_index].valid && cache_mem[req_index].tag == req_tag) begin
            hit = 1'b1;
            // Extract word from cache line based on offset
            read_data = cache_mem[req_index].data[req_offset*8 +: $bits(word_t)];
        end
    end

    // State machine logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            current_state <= IDLE;
            cpu_req_addr_q <= '0;
            cpu_req_write_q <= 1'b0;
            cpu_req_wdata_q <= '0;
            cpu_req_wstrb_q <= '0;
            cpu_req_valid_q <= 1'b0;
            for (int i = 0; i < NUM_SETS; i++) begin
                cache_mem[i].valid <= 1'b0;
                cache_mem[i].dirty <= 1'b0;
                cache_mem[i].tag <= '0;
                cache_mem[i].data <= '0;
            end
        end else begin
            current_state <= next_state;
            // Latch CPU request when ready and valid
            if (req_valid_i && req_ready_o) begin
                cpu_req_addr_q <= req_addr_i;
                cpu_req_write_q <= req_write_i;
                cpu_req_wdata_q <= req_wdata_i;
                cpu_req_wstrb_q <= req_wstrb_i;
                cpu_req_valid_q <= 1'b1;
            end else if (current_state == ALLOCATE || current_state == IDLE) begin
                cpu_req_valid_q <= 1'b0;
            end
        end
    end

    always_comb begin
        next_state = current_state;
        req_ready_o = 1'b0;
        rsp_valid_o = 1'b0;
        rsp_rdata_o = '0;
        rsp_error_o = 1'b0;

        mem_req_valid_o = 1'b0;
        mem_req_o = '0;
        mem_rsp_ready_o = 1'b0;

        case (current_state)
            IDLE:
                if (req_valid_i) begin
                    next_state = LOOKUP;
                    req_ready_o = 1'b1; // Accept request
                end
            LOOKUP:
                if (hit) begin
                    if (!cpu_req_write_q) begin // Read hit
                        rsp_valid_o = 1'b1;
                        rsp_rdata_o = read_data;
                        if (rsp_ready_i) begin
                            next_state = IDLE;
                        end
                    end else begin // Write hit
                        // Update cache line data
                        for (int i = 0; i < $bits(word_t)/8; i++) begin
                            if (cpu_req_wstrb_q[i]) begin
                                cache_mem[req_index].data[req_offset*8 + i*8 +: 8] = cpu_req_wdata_q[i*8 +: 8];
                            end
                        end
                        cache_mem[req_index].dirty = 1'b1;
                        rsp_valid_o = 1'b1;
                        if (rsp_ready_i) begin
                            next_state = IDLE;
                        end
                    end
                end else begin // Miss
                    if (cache_mem[req_index].valid && cache_mem[req_index].dirty) begin
                        next_state = WRITE_BACK; // Write-back dirty line
                    end else if (!cpu_req_write_q) begin
                        next_state = READ_MISS; // Read miss, fetch new line
                    end else begin
                        next_state = ALLOCATE; // Write miss, allocate new line
                    end
                end
            READ_MISS:
                mem_req_valid_o = 1'b1;
                mem_req_o.addr = {cpu_req_addr_q[ADDR_WIDTH-1:OFFSET_BITS], {OFFSET_BITS{1'b0}}}; // Line address
                mem_req_o.write = 1'b0;
                mem_req_o.burst_len = DCACHE_LINE_SIZE / ($bits(word_t)/8) - 1; // Number of words in a line - 1
                mem_req_o.id = 4'h1; // Data cache ID
                if (mem_req_ready_i) begin
                    mem_rsp_ready_o = 1'b1;
                    if (mem_rsp_valid_i) begin
                        // Assuming single beat response for simplicity, needs burst handling for full line
                        cache_mem[req_index].data = mem_rsp_i.data; // This is incorrect for burst, placeholder
                        cache_mem[req_index].valid = 1'b1;
                        cache_mem[req_index].dirty = 1'b0;
                        cache_mem[req_index].tag = req_tag;
                        next_state = ALLOCATE; // Go to allocate to handle original request
                    end
                end
            WRITE_MISS:
                // For write-allocate, same as read miss, then write to cache
                mem_req_valid_o = 1'b1;
                mem_req_o.addr = {cpu_req_addr_q[ADDR_WIDTH-1:OFFSET_BITS], {OFFSET_BITS{1'b0}}}; // Line address
                mem_req_o.write = 1'b0;
                mem_req_o.burst_len = DCACHE_LINE_SIZE / ($bits(word_t)/8) - 1;
                mem_req_o.id = 4'h1;
                if (mem_req_ready_i) begin
                    mem_rsp_ready_o = 1'b1;
                    if (mem_rsp_valid_i) begin
                        cache_mem[req_index].data = mem_rsp_i.data; // Placeholder
                        cache_mem[req_index].valid = 1'b1;
                        cache_mem[req_index].dirty = 1'b0;
                        cache_mem[req_index].tag = req_tag;
                        next_state = ALLOCATE; // Go to allocate to handle original request
                    end
                end
            WRITE_BACK:
                mem_req_valid_o = 1'b1;
                mem_req_o.addr = {cache_mem[req_index].tag, req_index, {OFFSET_BITS{1'b0}}}; // Original line address
                mem_req_o.write = 1'b1;
                mem_req_o.wdata = cache_mem[req_index].data; // Write back entire line
                mem_req_o.burst_len = DCACHE_LINE_SIZE / ($bits(word_t)/8) - 1;
                mem_req_o.id = 4'h1;
                if (mem_req_ready_i) begin
                    mem_rsp_ready_o = 1'b1;
                    if (mem_rsp_valid_i) begin // Response for write-back
                        cache_mem[req_index].dirty = 1'b0;
                        if (!cpu_req_write_q) begin
                            next_state = READ_MISS; // After write-back, fetch new line for read miss
                        end else begin
                            next_state = ALLOCATE; // After write-back, allocate for write miss
                        end
                    end
                end
            ALLOCATE:
                // Re-process the original CPU request after cache line is ready
                if (!cpu_req_write_q) begin // Original was a read
                    rsp_valid_o = 1'b1;
                    read_data = cache_mem[req_index].data[req_offset*8 +: $bits(word_t)];
                    if (rsp_ready_i) begin
                        next_state = IDLE;
                    end
                end else begin // Original was a write
                    for (int i = 0; i < XLEN/8; i++) begin
                        if (cpu_req_wstrb_q[i]) begin
                            cache_mem[req_index].data[req_offset*8 + i*8 +: 8] = cpu_req_wdata_q[i*8 +: 8];
                        end
                    end
                    cache_mem[req_index].dirty = 1'b1;
                    rsp_valid_o = 1'b1;
                    if (rsp_ready_i) begin
                        next_state = IDLE;
                    end
                end
        endcase
    end

endmodule : dcache
