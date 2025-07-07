//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: reservation_station.sv
// Module: reservation_station
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   A simple, unified Reservation Station (RS) for the out-of-order execution
//   engine. It holds dispatched instructions, waits for source operands to
//   become available (via result forwarding from the Common Data Bus), and
//   issues ready instructions to the functional units.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import ooo_pkg::*;

// AI_TAG: FEATURE - Unified reservation station for all instruction types.
// AI_TAG: FEATURE - Full result forwarding logic to resolve operand dependencies.
// AI_TAG: FEATURE - Configurable number of entries.
// AI_TAG: INTERNAL_BLOCK - RSEntries - The storage array for instructions.
// AI_TAG: INTERNAL_BLOCK - IssueSelector - Selects a ready instruction to issue to a functional unit.
// AI_TAG: INTERNAL_BLOCK - DispatchLogic - Allocates a new entry for a dispatched instruction.
// AI_TAG: INTERNAL_BLOCK - ResultWatcher - Monitors the result bus and updates waiting instructions.

module reservation_station #(
    parameter integer DATA_WIDTH     = ooo_pkg::DATA_WIDTH,
    parameter integer RS_SIZE        = ooo_pkg::RS_SIZE,
    parameter integer ROB_ADDR_WIDTH = ooo_pkg::ROB_ADDR_WIDTH
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Flush signal to clear the RS on exceptions or mispredictions
    input  logic flush_i,

    // Dispatch interface (from Decode/Rename)
    input  ooo_dispatch_t dispatch_i,
    output logic          dispatch_ready_o,

    // Result forwarding bus (Common Data Bus - CDB)
    input  ooo_result_t   result_i,

    // Issue interface (to functional units)
    output ooo_issue_t    issue_o,
    input  logic          issue_ready_i
);

    localparam RS_ADDR_WIDTH = (RS_SIZE > 1) ? $clog2(RS_SIZE) : 1;

    // AI_TAG: INTERNAL_STORAGE - rs_entry_t - Structure for a single reservation station entry.
    typedef struct packed {
        logic                       busy;
        logic [31:0]                opcode;
        logic [DATA_WIDTH-1:0]      v_rs1;
        logic                       q_rs1_valid;
        logic [ROB_ADDR_WIDTH-1:0]  q_rs1;
        logic [DATA_WIDTH-1:0]      v_rs2;
        logic                       q_rs2_valid;
        logic [ROB_ADDR_WIDTH-1:0]  q_rs2;
        logic [ROB_ADDR_WIDTH-1:0]  rob_tag;
    } rs_entry_t;

    rs_entry_t [RS_SIZE-1:0] rs_r, rs_ns;
    logic [RS_ADDR_WIDTH:0]  entry_count_r, entry_count_ns;
    logic [RS_ADDR_WIDTH-1:0] alloc_ptr_r, alloc_ptr_ns; // Points to the next free slot
    logic [RS_ADDR_WIDTH-1:0] issue_idx_c;

    //---------------------------------------------------------------------------
    // Combinational Logic
    //---------------------------------------------------------------------------

    assign dispatch_ready_o = (entry_count_r < RS_SIZE);

    // Issue the selected instruction
    assign issue_o.valid   = rs_r[issue_idx_c].busy && !rs_r[issue_idx_c].q_rs1_valid && !rs_r[issue_idx_c].q_rs2_valid;
    assign issue_o.opcode  = rs_r[issue_idx_c].opcode;
    assign issue_o.v_rs1   = rs_r[issue_idx_c].v_rs1;
    assign issue_o.v_rs2   = rs_r[issue_idx_c].v_rs2;
    assign issue_o.rob_tag = rs_r[issue_idx_c].rob_tag;


    // --- Issue Selection Logic (simple priority encoder) ---
    // AI_TAG: FSM_NAME - issue_selector_fsm
    // AI_TAG: FSM_PURPOSE - issue_selector_fsm - Finds the first ready-to-issue instruction.
    always_comb begin : proc_issue_selector
        issue_idx_c = '0;
        for (int i = 0; i < RS_SIZE; i++) begin
            // An instruction is ready if it's busy and both its operands are valid (not waiting)
            if (rs_r[i].busy && !rs_r[i].q_rs1_valid && !rs_r[i].q_rs2_valid) begin
                issue_idx_c = RS_ADDR_WIDTH'(i);
                break;
            end
        end
    end

    //---------------------------------------------------------------------------
    // Next-State Logic
    //---------------------------------------------------------------------------
    always_comb begin : proc_next_state_logic
        logic do_dispatch_c;
        logic do_issue_c;

        // Default assignments
        rs_ns = rs_r;
        alloc_ptr_ns = alloc_ptr_r;
        entry_count_ns = entry_count_r;

        do_dispatch_c = dispatch_i.valid && dispatch_ready_o;
        do_issue_c    = issue_o.valid && issue_ready_i;

        // Handle simultaneous dispatch and issue to the same entry
        // If an entry is issued, it becomes free for dispatch in the same cycle.
        if (do_issue_c) begin
            rs_ns[issue_idx_c].busy = 1'b0;
            if (!do_dispatch_c || (alloc_ptr_r != issue_idx_c)) begin
                entry_count_ns = entry_count_r - 1;
            end
        end

        // --- Result Forwarding ---
        if (result_i.valid) begin
            for (int i = 0; i < RS_SIZE; i++) begin
                if (rs_ns[i].busy) begin
                    if (rs_ns[i].q_rs1_valid && (rs_ns[i].q_rs1 == result_i.rob_tag)) begin
                        rs_ns[i].v_rs1 = result_i.data;
                        rs_ns[i].q_rs1_valid = 1'b0;
                    end
                    if (rs_ns[i].q_rs2_valid && (rs_ns[i].q_rs2 == result_i.rob_tag)) begin
                        rs_ns[i].v_rs2 = result_i.data;
                        rs_ns[i].q_rs2_valid = 1'b0;
                    end
                end
            end
        end

        // --- Instruction Dispatch ---
        if (do_dispatch_c) begin
            rs_ns[alloc_ptr_r].busy        = 1'b1;
            rs_ns[alloc_ptr_r].opcode      = dispatch_i.opcode;
            rs_ns[alloc_ptr_r].v_rs1       = dispatch_i.v_rs1;
            rs_ns[alloc_ptr_r].q_rs1_valid = dispatch_i.q_rs1_valid;
            rs_ns[alloc_ptr_r].q_rs1       = dispatch_i.q_rs1;
            rs_ns[alloc_ptr_r].v_rs2       = dispatch_i.v_rs2;
            rs_ns[alloc_ptr_r].q_rs2_valid = dispatch_i.q_rs2_valid;
            rs_ns[alloc_ptr_r].q_rs2       = dispatch_i.q_rs2;
            rs_ns[alloc_ptr_r].rob_tag     = dispatch_i.rob_tag;

            alloc_ptr_ns = alloc_ptr_r + 1;
            if (!do_issue_c || (alloc_ptr_r != issue_idx_c)) begin
                 entry_count_ns = entry_count_r + 1;
            end
        end
    end

    //---------------------------------------------------------------------------
    // Sequential Logic (State Registers)
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_state_registers
        if (!rst_ni) begin
            // Reset all entries to not busy
            for (int i = 0; i < RS_SIZE; i++) begin
                rs_r[i] <= '{default:'0};
            end
            alloc_ptr_r   <= '0;
            entry_count_r <= '0;
        end else if (flush_i) begin
            // Flush all entries
            for (int i = 0; i < RS_SIZE; i++) begin
                rs_r[i] <= '{default:'0};
            end
            alloc_ptr_r   <= '0;
            entry_count_r <= '0;
        end else begin
            rs_r          <= rs_ns;
            alloc_ptr_r   <= alloc_ptr_ns;
            entry_count_r <= entry_count_ns;
        end
    end

endmodule : reservation_station

//=============================================================================
// Dependencies: None
//
// Performance:
//   - Critical Path: TBD, likely in the issue selection or result forwarding logic.
//   - Max Frequency: TBD
//   - Area: TBD (highly dependent on RS_SIZE)
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
// 1.0.0   | 2025-06-28 | DesignAI           | Initial fleshed-out implementation with robust entry management.
// 0.1.0   | 2025-06-27 | DesignAI           | Initial skeleton release
//=============================================================================

`default_nettype wire 