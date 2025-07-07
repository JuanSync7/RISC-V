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

import riscv_ooo_types_pkg::*;
import riscv_core_types_pkg::*;

// AI_TAG: FEATURE - Unified reservation station for all instruction types.
// AI_TAG: FEATURE - Full result forwarding logic to resolve operand dependencies.
// AI_TAG: FEATURE - Configurable number of entries.
// AI_TAG: INTERNAL_BLOCK - RSEntries - The storage array for instructions.
// AI_TAG: INTERNAL_BLOCK - IssueSelector - Selects a ready instruction to issue to a functional unit.
// AI_TAG: INTERNAL_BLOCK - DispatchLogic - Allocates a new entry for a dispatched instruction.
// AI_TAG: INTERNAL_BLOCK - ResultWatcher - Monitors the result bus and updates waiting instructions.

module reservation_station #(
    parameter integer DATA_WIDTH     = XLEN, // AI_TAG: PARAM_DESC - Width of the data path and instruction operands.
    parameter integer RS_SIZE        = DEFAULT_RS_SIZE, // AI_TAG: PARAM_DESC - Number of entries in the reservation station.
                                           // AI_TAG: PARAM_USAGE - Determines the depth of the instruction buffer.
                                           // AI_TAG: PARAM_CONSTRAINTS - Should be a power of 2 for efficiency.
    parameter integer ROB_ADDR_WIDTH = ROB_ADDR_WIDTH_G   // AI_TAG: PARAM_DESC - Width of the Re-Order Buffer (ROB) tag.
                                           // AI_TAG: PARAM_USAGE - Must match the ROB's address width.
) (
    input  logic clk_i,    // AI_TAG: PORT_DESC - System clock
                           // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic rst_ni,   // AI_TAG: PORT_DESC - Asynchronous active-low reset
                           // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)

    // Flush signal to clear the RS on exceptions or mispredictions
    input  logic flush_i,  // AI_TAG: PORT_DESC - High to flush all entries in the RS.
                           // AI_TAG: PORT_CLK_DOMAIN - clk_i

    // Dispatch interface (from Decode/Rename)
    input  logic        dispatch_valid_i,     // AI_TAG: PORT_DESC - The instruction dispatched from rename is valid.
    output logic        dispatch_ready_o,     // AI_TAG: PORT_DESC - RS is ready to accept a new instruction.
    input  logic [31:0] dispatch_opcode_i,    // AI_TAG: PORT_DESC - The full instruction opcode/data.
    input  logic [DATA_WIDTH-1:0] dispatch_v_rs1_i, // AI_TAG: PORT_DESC - Value of operand 1 if available.
    input  logic        dispatch_q_rs1_valid_i, // AI_TAG: PORT_DESC - Flag indicating if operand 1 is waiting for a result from the ROB.
    input  logic [ROB_ADDR_WIDTH-1:0] dispatch_q_rs1_i, // AI_TAG: PORT_DESC - ROB tag for operand 1.
    input  logic [DATA_WIDTH-1:0] dispatch_v_rs2_i, // AI_TAG: PORT_DESC - Value of operand 2 if available.
    input  logic        dispatch_q_rs2_valid_i, // AI_TAG: PORT_DESC - Flag indicating if operand 2 is waiting for a result from the ROB.
    input  logic [ROB_ADDR_WIDTH-1:0] dispatch_q_rs2_i, // AI_TAG: PORT_DESC - ROB tag for operand 2.
    input  logic [ROB_ADDR_WIDTH-1:0] dispatch_rob_tag_i, // AI_TAG: PORT_DESC - ROB tag for this new instruction's result.

    // Result forwarding bus (Common Data Bus - CDB)
    input  logic        result_valid_i,       // AI_TAG: PORT_DESC - A valid result is being broadcast on the CDB.
    input  logic [ROB_ADDR_WIDTH-1:0] result_rob_tag_i, // AI_TAG: PORT_DESC - The ROB tag of the broadcasted result.
    input  logic [DATA_WIDTH-1:0] result_data_i,    // AI_TAG: PORT_DESC - The data value of the broadcasted result.

    // Issue interface (to functional units)
    output logic        issue_valid_o,        // AI_TAG: PORT_DESC - A valid instruction is ready to be issued.
    input  logic        issue_ready_i,        // AI_TAG: PORT_DESC - The functional unit is ready to accept an instruction.
    output logic [31:0] issue_opcode_o,     // AI_TAG: PORT_DESC - Opcode of the issued instruction.
    output logic [DATA_WIDTH-1:0] issue_v_rs1_o,    // AI_TAG: PORT_DESC - Value of operand 1 for the issued instruction.
    output logic [DATA_WIDTH-1:0] issue_v_rs2_o,    // AI_TAG: PORT_DESC - Value of operand 2 for the issued instruction.
    output logic [ROB_ADDR_WIDTH-1:0] issue_rob_tag_o // AI_TAG: PORT_DESC - ROB tag of the issued instruction.
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
    assign issue_valid_o   = rs_r[issue_idx_c].busy && !rs_r[issue_idx_c].q_rs1_valid && !rs_r[issue_idx_c].q_rs2_valid;
    assign issue_opcode_o  = rs_r[issue_idx_c].opcode;
    assign issue_v_rs1_o   = rs_r[issue_idx_c].v_rs1;
    assign issue_v_rs2_o   = rs_r[issue_idx_c].v_rs2;
    assign issue_rob_tag_o = rs_r[issue_idx_c].rob_tag;


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

        do_dispatch_c = dispatch_valid_i && dispatch_ready_o;
        do_issue_c    = issue_valid_o && issue_ready_i;

        // Handle simultaneous dispatch and issue to the same entry
        // If an entry is issued, it becomes free for dispatch in the same cycle.
        if (do_issue_c) begin
            rs_ns[issue_idx_c].busy = 1'b0;
            if (!do_dispatch_c || (alloc_ptr_r != issue_idx_c)) begin
                entry_count_ns = entry_count_r - 1;
            end
        end

        // --- Result Forwarding ---
        if (result_valid_i) begin
            for (int i = 0; i < RS_SIZE; i++) begin
                if (rs_ns[i].busy) begin
                    if (rs_ns[i].q_rs1_valid && (rs_ns[i].q_rs1 == result_rob_tag_i)) begin
                        rs_ns[i].v_rs1 = result_data_i;
                        rs_ns[i].q_rs1_valid = 1'b0;
                    end
                    if (rs_ns[i].q_rs2_valid && (rs_ns[i].q_rs2 == result_rob_tag_i)) begin
                        rs_ns[i].v_rs2 = result_data_i;
                        rs_ns[i].q_rs2_valid = 1'b0;
                    end
                end
            end
        end

        // --- Instruction Dispatch ---
        if (do_dispatch_c) begin
            rs_ns[alloc_ptr_r].busy        = 1'b1;
            rs_ns[alloc_ptr_r].opcode      = dispatch_opcode_i;
            rs_ns[alloc_ptr_r].v_rs1       = dispatch_v_rs1_i;
            rs_ns[alloc_ptr_r].q_rs1_valid = dispatch_q_rs1_valid_i;
            rs_ns[alloc_ptr_r].q_rs1       = dispatch_q_rs1_i;
            rs_ns[alloc_ptr_r].v_rs2       = dispatch_v_rs2_i;
            rs_ns[alloc_ptr_r].q_rs2_valid = dispatch_q_rs2_valid_i;
            rs_ns[alloc_ptr_r].q_rs2       = dispatch_q_rs2_i;
            rs_ns[alloc_ptr_r].rob_tag     = dispatch_rob_tag_i;

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