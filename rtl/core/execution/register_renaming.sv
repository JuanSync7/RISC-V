//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: register_renaming.sv
// Module: register_renaming
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Implements register renaming to eliminate WAR and WAW hazards, a key
//   enabler for out-of-order execution. It maps architectural registers
//   to physical tags (ROB tags) and provides either the physical tag or the
//   actual data value if it's ready, sourcing it from a physical register file
//   that snoops the result bus.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none



// AI_TAG: FEATURE - Eliminates WAR and WAW hazards via register renaming.
// AI_TAG: FEATURE - Provides operand values directly if ready, reducing stalls.
// AI_TAG: FEATURE - Maintains the mapping between architectural and physical registers (ROB tags).
// AI_TAG: INTERNAL_BLOCK - MapTable - Stores the mapping from architectural register to ROB tag.
// AI_TAG: INTERNAL_BLOCK - PhysicalRegFile - Stores the latest speculative register values.
// AI_TAG: INTERNAL_BLOCK - OperandFetch - Logic to fetch tags or data for source operands.

module register_renaming #(
    parameter integer DATA_WIDTH, // AI_TAG: PARAM_DESC - Width of the data path and registers.
    parameter integer ARCH_REG_COUNT, // AI_TAG: PARAM_DESC - Number of architectural registers.
    parameter integer ROB_SIZE, // AI_TAG: PARAM_DESC - Number of entries in the ROB.
    parameter integer REG_ADDR_WIDTH   // AI_TAG: PARAM_DESC - Width of the architectural register file address.
) (
    input  logic clk_i,    // AI_TAG: PORT_DESC - System clock
                           // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic rst_ni,   // AI_TAG: PORT_DESC - Asynchronous active-low reset
                           // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)

    // Flush signal
    input  logic flush_i,  // AI_TAG: PORT_DESC - High to flush all speculative state.
                           // AI_TAG: PORT_CLK_DOMAIN - clk_i

    // Decode interface (inputs)
    input  logic      decode_valid_i,         // AI_TAG: PORT_DESC - Valid instruction from decode stage.
    input  logic [REG_ADDR_WIDTH-1:0] decode_rs1_addr_i,  // AI_TAG: PORT_DESC - Address of source register 1.
    input  logic [REG_ADDR_WIDTH-1:0] decode_rs2_addr_i,  // AI_TAG: PORT_DESC - Address of source register 2.
    input  logic [REG_ADDR_WIDTH-1:0] decode_rd_addr_i,   // AI_TAG: PORT_DESC - Address of destination register.
    input  logic      decode_rd_write_en_i,   // AI_TAG: PORT_DESC - Indicates if the instruction writes to a destination register.

    // Dispatch interface (outputs to Reservation Station)
    output logic      dispatch_valid_o,         // AI_TAG: PORT_DESC - Renamed instruction is valid for dispatch.
    output logic [DATA_WIDTH-1:0] dispatch_v_rs1_o, // AI_TAG: PORT_DESC - Value of operand 1 if ready.
    output logic      dispatch_q_rs1_valid_o, // AI_TAG: PORT_DESC - Is operand 1 not ready (i.e., waiting for a tag)?
    output logic [$clog2(ROB_SIZE)-1:0] dispatch_q_rs1_o,   // AI_TAG: PORT_DESC - ROB tag for operand 1.
    output logic [DATA_WIDTH-1:0] dispatch_v_rs2_o, // AI_TAG: PORT_DESC - Value of operand 2 if ready.
    output logic      dispatch_q_rs2_valid_o, // AI_TAG: PORT_DESC - Is operand 2 not ready?
    output logic [$clog2(ROB_SIZE)-1:0] dispatch_q_rs2_o,   // AI_TAG: PORT_DESC - ROB tag for operand 2.

    // ROB interface
    input  logic [$clog2(ROB_SIZE)-1:0] rob_new_tag_i,      // AI_TAG: PORT_DESC - The new ROB tag allocated for this instruction.
    input  logic      rob_ready_i,            // AI_TAG: PORT_DESC - Is the ROB ready to accept a new entry?

    // Result bus (CDB) for snooping and updating the PRF
    input  logic      result_valid_i,         // AI_TAG: PORT_DESC - A valid result is on the CDB.
    input  logic [$clog2(ROB_SIZE)-1:0] result_rob_tag_i,   // AI_TAG: PORT_DESC - The ROB tag of the result.
    input  logic [DATA_WIDTH-1:0] result_data_i,        // AI_TAG: PORT_DESC - The result value.

    // Commit interface (to update/invalidate map table entries)
    input  logic      commit_valid_i,         // AI_TAG: PORT_DESC - An instruction is committing.
    input  logic [REG_ADDR_WIDTH-1:0] commit_rd_addr_i,   // AI_TAG: PORT_DESC - The destination register of the committing instruction.
    input  logic [$clog2(ROB_SIZE)-1:0] commit_rob_tag_i    // AI_TAG: PORT_DESC - The ROB tag of the committing instruction.
);

    localparam ROB_ADDR_WIDTH = $clog2(ROB_SIZE);

    // AI_TAG: INTERNAL_STORAGE - map_table_entry_t - Maps an architectural register to a physical (ROB) tag.
    typedef struct packed {
        logic [ROB_ADDR_WIDTH-1:0] tag;
        logic busy; // Is there an instruction in flight writing to this reg?
    } map_table_entry_t;

    map_table_entry_t [ARCH_REG_COUNT-1:0] map_table_r, map_table_ns;

    // AI_TAG: INTERNAL_STORAGE - prf - Physical Register File stores speculative values.
    // It is indexed by ROB tag.
    logic [DATA_WIDTH-1:0] [ROB_SIZE-1:0] prf_r, prf_ns;
    logic [ROB_SIZE-1:0]                  prf_ready_r, prf_ready_ns; // Bitmask of which PRF entries have been written by the CDB

    //---------------------------------------------------------------------------
    // Combinational Logic
    //---------------------------------------------------------------------------

    // Operand 1 Fetch Logic
    map_table_entry_t rs1_map_c;
    logic             rs1_is_mapped_c;
    logic             rs1_is_ready_c;

    assign rs1_map_c       = map_table_r[decode_rs1_addr_i];
    assign rs1_is_mapped_c = rs1_map_c.busy && (decode_rs1_addr_i != 0);
    assign rs1_is_ready_c  = prf_ready_r[rs1_map_c.tag];

    assign dispatch_q_rs1_valid_o = rs1_is_mapped_c && !rs1_is_ready_c;
    assign dispatch_q_rs1_o       = rs1_map_c.tag;
    assign dispatch_v_rs1_o       = rs1_is_ready_c ? prf_r[rs1_map_c.tag] : '0;

    // Operand 2 Fetch Logic
    map_table_entry_t rs2_map_c;
    logic             rs2_is_mapped_c;
    logic             rs2_is_ready_c;

    assign rs2_map_c       = map_table_r[decode_rs2_addr_i];
    assign rs2_is_mapped_c = rs2_map_c.busy && (decode_rs2_addr_i != 0);
    assign rs2_is_ready_c  = prf_ready_r[rs2_map_c.tag];

    assign dispatch_q_rs2_valid_o = rs2_is_mapped_c && !rs2_is_ready_c;
    assign dispatch_q_rs2_o       = rs2_map_c.tag;
    assign dispatch_v_rs2_o       = rs2_is_ready_c ? prf_r[rs2_map_c.tag] : '0;


    // The overall dispatch is valid if the source instruction is valid and the ROB has space.
    assign dispatch_valid_o = decode_valid_i && rob_ready_i;

    //---------------------------------------------------------------------------
    // Next-State Logic
    //---------------------------------------------------------------------------
    always_comb begin : proc_next_state_logic
        logic do_dispatch_c;

        // Default assignments
        map_table_ns = map_table_r;
        prf_ns       = prf_r;
        prf_ready_ns = prf_ready_r;
        do_dispatch_c = dispatch_valid_o;

        // --- Result Bus Update (snooping) ---
        // A result is broadcast on the CDB. Update the corresponding PRF entry.
        if (result_valid_i) begin
            prf_ns[result_rob_tag_i]       = result_data_i;
            prf_ready_ns[result_rob_tag_i] = 1'b1;
        end

        // --- Commit Stage: Freeing a mapping ---
        // An instruction commits. If the map table still points to its tag,
        // the mapping is now stale (value is in architectural file), so we clear it.
        if (commit_valid_i) begin
            if (map_table_r[commit_rd_addr_i].busy && (map_table_r[commit_rd_addr_i].tag == commit_rob_tag_i)) begin
                map_table_ns[commit_rd_addr_i].busy = 1'b0;
            end
        end

        // --- Dispatch Stage: Allocating a new mapping ---
        // A new instruction is dispatched. Update the map table for its destination register.
        // This must have higher priority than the commit stage logic for back-to-back dependencies.
        if (do_dispatch_c && decode_rd_write_en_i && (decode_rd_addr_i != 0)) begin
            map_table_ns[decode_rd_addr_i].busy = 1'b1;
            map_table_ns[decode_rd_addr_i].tag  = rob_new_tag_i;
            // The new PRF entry for this instruction is not ready yet.
            prf_ready_ns[rob_new_tag_i] = 1'b0;
        end
    end

    //---------------------------------------------------------------------------
    // Sequential Logic (State Registers)
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_state_registers
        if (!rst_ni) begin
            map_table_r <= '{default:'0};
            prf_ready_r <= '{default:'0};
            // No need to reset PRF data
        end else if (flush_i) begin
            map_table_r <= '{default:'0};
            prf_ready_r <= '{default:'0};
        end else begin
            map_table_r <= map_table_ns;
            prf_r       <= prf_ns;
            prf_ready_r <= prf_ready_ns;
        end
    end

endmodule : register_renaming

//=============================================================================
// Dependencies: None
//
// Performance:
//   - Critical Path: TBD, likely in the map table lookup and operand fetch logic.
//   - Max Frequency: TBD
//   - Area: TBD (highly dependent on ROB_SIZE and ARCH_REG_COUNT)
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
// 1.0.0   | 2025-06-28 | DesignAI           | Initial fleshed-out implementation with PRF and bypass logic.
// 0.1.0   | 2025-06-27 | DesignAI           | Initial skeleton release
//=============================================================================

`default_nettype wire 