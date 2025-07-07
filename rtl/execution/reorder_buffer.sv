//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: reorder_buffer.sv
// Module: reorder_buffer
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   The Reorder Buffer (ROB) for the out-of-order execution engine. It tracks
//   all instructions in flight, allowing them to execute out of order but
//   commit in order. This is key to implementing precise exceptions and state
//   recovery on mispredictions.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import ooo_pkg::*;

// AI_TAG: FEATURE - Enables in-order retirement for out-of-order execution.
// AI_TAG: FEATURE - Ensures precise exception handling.
// AI_TAG: FEATURE - Manages register write-back destinations and values.
// AI_TAG: INTERNAL_BLOCK - ROBEntries - Circular buffer for storing in-flight instruction state.
// AI_TAG: INTERNAL_BLOCK - CommitLogic - Determines when the head instruction can be committed.
// AI_TAG: INTERNAL_BLOCK - PointerLogic - Manages head/tail pointers and entry count.

module reorder_buffer #(
    parameter integer DATA_WIDTH     = ooo_pkg::DATA_WIDTH,
    parameter integer ROB_SIZE       = ooo_pkg::ROB_SIZE,
    parameter integer PC_WIDTH       = ooo_pkg::PC_WIDTH,
    parameter integer REG_ADDR_WIDTH = ooo_pkg::REG_ADDR_WIDTH
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Flush signal to clear the ROB on exceptions/mispredictions
    input  logic flush_i,

    // Dispatch interface (from Decode/Rename)
    input  ooo_dispatch_t dispatch_i,
    output logic          dispatch_ready_o,

    // Execution result interface (from functional units via CDB)
    input  ooo_result_t   execute_result_i,

    // Commit interface (to Writeback/Register File and CSRs)
    output ooo_commit_t   commit_o,
    input  logic          commit_ready_i
);

    localparam ROB_ADDR_WIDTH = $clog2(ROB_SIZE);

    // AI_TAG: INTERNAL_STORAGE - exception_info_t - Structure for exception details.
    typedef struct packed {
        logic       valid;
        logic [31:0] cause;
    } exception_info_t;

    // AI_TAG: INTERNAL_STORAGE - rob_entry_t - Structure for a single ROB entry.
    typedef struct packed {
        logic [PC_WIDTH-1:0]       pc;
        logic [REG_ADDR_WIDTH-1:0] rd_addr;
        logic [DATA_WIDTH-1:0]     result;
        exception_info_t           exception;
        logic                      is_ready;   // Instruction has finished execution
    } rob_entry_t;

    rob_entry_t [ROB_SIZE-1:0] rob_r, rob_ns;

    logic [ROB_ADDR_WIDTH-1:0] head_ptr_r, head_ptr_ns;
    logic [ROB_ADDR_WIDTH-1:0] tail_ptr_r, tail_ptr_ns;
    logic [ROB_ADDR_WIDTH:0]   entry_count_r, entry_count_ns;
    logic                      is_full_c;
    logic                      is_empty_c;

    //---------------------------------------------------------------------------
    // Combinational Logic
    //---------------------------------------------------------------------------

    assign is_full_c  = (entry_count_r == ROB_SIZE);
    assign is_empty_c = (entry_count_r == 0);

    assign dispatch_ready_o   = !is_full_c;

    // The instruction at the head of the ROB is ready to commit.
    assign commit_o.valid           = !is_empty_c && rob_r[head_ptr_r].is_ready;
    assign commit_o.pc              = rob_r[head_ptr_r].pc;
    assign commit_o.rd_addr         = rob_r[head_ptr_r].rd_addr;
    assign commit_o.result          = rob_r[head_ptr_r].result;
    assign commit_o.exception.valid = rob_r[head_ptr_r].exception.valid;
    assign commit_o.exception.cause = rob_r[head_ptr_r].exception.cause;

    //---------------------------------------------------------------------------
    // Next-State Logic
    //---------------------------------------------------------------------------
    always_comb begin : proc_next_state_logic
        logic do_dispatch_c;
        logic do_commit_c;

        // Default assignments
        rob_ns         = rob_r;
        head_ptr_ns    = head_ptr_r;
        tail_ptr_ns    = tail_ptr_r;
        entry_count_ns = entry_count_r;

        do_dispatch_c = dispatch_i.valid && dispatch_ready_o;
        do_commit_c   = commit_o.valid && commit_ready_i;

        // --- Dispatch Logic ---
        // A new instruction is allocated an entry at the tail.
        if (do_dispatch_c) begin
            rob_ns[tail_ptr_r].pc        = dispatch_i.pc;
            rob_ns[tail_ptr_r].rd_addr   = dispatch_i.rd_addr;
            rob_ns[tail_ptr_r].is_ready  = 1'b0;
            rob_ns[tail_ptr_r].exception = '{default: '0};
            tail_ptr_ns                  = tail_ptr_r + 1;
        end

        // --- Execution Result Update ---
        // A functional unit has completed and writes its result to the corresponding ROB entry.
        if (execute_result_i.valid) begin
            rob_ns[execute_result_i.rob_tag].result          = execute_result_i.data;
            rob_ns[execute_result_i.rob_tag].exception.valid = execute_result_i.exception_valid;
            rob_ns[execute_result_i.rob_tag].exception.cause = execute_result_i.exception_cause;
            rob_ns[execute_result_i.rob_tag].is_ready        = 1'b1;
        end

        // --- Commit Logic ---
        // The instruction at the head is retired.
        if (do_commit_c) begin
            head_ptr_ns = head_ptr_r + 1;
        end

        // --- Entry Count Update ---
        if (do_dispatch_c && !do_commit_c) begin
            entry_count_ns = entry_count_r + 1;
        end else if (!do_dispatch_c && do_commit_c) begin
            entry_count_ns = entry_count_r - 1;
        } else begin
            entry_count_ns = entry_count_r;
        end
    end

    //---------------------------------------------------------------------------
    // Sequential Logic (State Registers)
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_state_registers
        if (!rst_ni) begin
            head_ptr_r    <= '0;
            tail_ptr_r    <= '0;
            entry_count_r <= '0;
            // No need to reset ROB entries, as dispatch logic will overwrite.
        end else if (flush_i) begin
            head_ptr_r    <= '0;
            tail_ptr_r    <= '0;
            entry_count_r <= '0;
        end else begin
            head_ptr_r    <= head_ptr_ns;
            tail_ptr_r    <= tail_ptr_ns;
            entry_count_r <= entry_count_ns;
            // Only update ROB entries on dispatch or result writeback
            if (dispatch_i.valid && dispatch_ready_o) begin
                rob_r[tail_ptr_r] <= rob_ns[tail_ptr_r];
            }
            if (execute_result_i.valid) begin
                rob_r[execute_result_i.rob_tag] <= rob_ns[execute_result_i.rob_tag];
            }
        end
    end

endmodule : reorder_buffer

//=============================================================================
// Dependencies: None
//
// Performance:
//   - Critical Path: TBD
//   - Max Frequency: TBD
//   - Area: TBD (highly dependent on ROB_SIZE)
//
// Verification Coverage:
//   - Code Coverage: N/A
//   - Functional Coverage: N/A
//   - Branch Coverage: N/A
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: N/A
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: TBD
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial fleshed-out implementation with robust pointer/counter logic.
// 0.1.0   | 2025-06-27 | DesignAI           | Initial skeleton release
//=============================================================================

`default_nettype wire 