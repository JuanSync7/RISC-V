//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: branch_predictor.sv
// Module: branch_predictor
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Branch Prediction Unit (BPU) for the RISC-V core. Implements a 2-bit
//   saturating counter with Branch Target Buffer (BTB) and Branch History
//   Table (BHT) for improved branch prediction accuracy. Target: >85%
//   prediction accuracy for typical workloads.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_types_pkg::*;
import riscv_config_pkg::*;

module branch_predictor #(
    // AI_TAG: PARAM_DESC - BTB_ENTRIES - Number of entries in the Branch Target Buffer.
    // AI_TAG: PARAM_USAGE - Determines the number of branch targets that can be cached.
    // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2 for efficient indexing.
    parameter integer BTB_ENTRIES = DEFAULT_BTB_ENTRIES,
    
    // AI_TAG: PARAM_DESC - BHT_ENTRIES - Number of entries in the Branch History Table.
    // AI_TAG: PARAM_USAGE - Determines the number of branch history patterns that can be tracked.
    // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2 for efficient indexing.
    parameter integer BHT_ENTRIES = DEFAULT_BHT_ENTRIES,

    parameter integer GLOBAL_HISTORY_WIDTH = DEFAULT_GLOBAL_HISTORY_WIDTH
) (
    // AI_TAG: PORT_DESC - clk_i - System clock for synchronous operations.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        clk_i,
    
    // AI_TAG: PORT_DESC - rst_ni - Asynchronous active-low reset.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
    // AI_TAG: PORT_TIMING - Asynchronous
    input  logic        rst_ni,

    // --- Prediction Interface ---
    // AI_TAG: PORT_DESC - pc_i - Program counter for branch prediction lookup.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_TIMING - Combinatorial
    input  addr_t       pc_i,
    
    // AI_TAG: PORT_DESC - predict_taken_o - Branch prediction result (1=taken, 0=not-taken).
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_DEFAULT_STATE - 1'b0 (predict not-taken by default)
    // AI_TAG: PORT_TIMING - Combinatorial
    output logic        predict_taken_o,
    
    // AI_TAG: PORT_DESC - predict_target_o - Predicted branch target address.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_DEFAULT_STATE - 32'h0
    // AI_TAG: PORT_TIMING - Combinatorial
    output addr_t       predict_target_o,
    
    // AI_TAG: PORT_DESC - btb_hit_o - Indicates if the PC was found in the BTB.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_DEFAULT_STATE - 1'b0
    // AI_TAG: PORT_TIMING - Combinatorial
    output logic        btb_hit_o,

    // --- Update Interface ---
    // AI_TAG: PORT_DESC - update_i - Update signal to record actual branch outcome.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        update_i,
    
    // AI_TAG: PORT_DESC - update_pc_i - PC of the branch being updated.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  addr_t       update_pc_i,
    
    // AI_TAG: PORT_DESC - actual_taken_i - Actual branch outcome (1=taken, 0=not-taken).
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        actual_taken_i,
    
    // AI_TAG: PORT_DESC - actual_target_i - Actual branch target address.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  addr_t       actual_target_i,
    
    // AI_TAG: PORT_DESC - is_branch_i - Indicates if the instruction is a branch.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        is_branch_i
);

    // AI_TAG: INTERNAL_STORAGE - Branch Target Buffer (BTB) structure
    typedef struct packed {
        logic        valid;      // Valid bit for this entry
        addr_t       tag;        // PC tag for matching
        addr_t       target;     // Branch target address
        logic [1:0]  counter;    // 2-bit saturating counter
    } btb_entry_t;
    
    // AI_TAG: INTERNAL_STORAGE - BTB memory array
    btb_entry_t btb_mem [BTB_ENTRIES-1:0];
    
    // AI_TAG: INTERNAL_STORAGE - Branch History Table (BHT) for global history
    logic [1:0] bht_mem [BHT_ENTRIES-1:0];
    
    // AI_TAG: INTERNAL_STORAGE - Global branch history register
    logic [GLOBAL_HISTORY_WIDTH-1:0] global_history_r;
    
    // AI_TAG: INTERNAL_LOGIC - BTB indexing and tag calculation
    localparam integer BTB_INDEX_BITS = $clog2(BTB_ENTRIES);
    localparam integer BTB_TAG_BITS = ADDR_WIDTH - BTB_INDEX_BITS;
    
    logic [BTB_INDEX_BITS-1:0] btb_index;
    logic [BTB_TAG_BITS-1:0]   btb_tag;
    logic [BTB_INDEX_BITS-1:0] update_btb_index;
    logic [BTB_TAG_BITS-1:0]   update_btb_tag;
    
    // AI_TAG: INTERNAL_LOGIC - BHT indexing
    localparam integer BHT_INDEX_BITS = $clog2(BHT_ENTRIES);
    logic [BHT_INDEX_BITS-1:0] bht_index;
    logic [BHT_INDEX_BITS-1:0] update_bht_index;
    
    // AI_TAG: INTERNAL_LOGIC - BTB lookup signals
    logic btb_valid_match;
    logic btb_tag_match;
    logic btb_entry_valid;
    
    // AI_TAG: INTERNAL_LOGIC - BHT lookup signals
    logic [1:0] bht_counter;
    
    // AI_TAG: INTERNAL_LOGIC - Index and tag calculation for prediction
    assign btb_index = pc_i[BTB_INDEX_BITS+1:2];  // Use PC[7:2] for 64-entry BTB
    assign btb_tag   = pc_i[ADDR_WIDTH-1:BTB_INDEX_BITS+2];
    
    // AI_TAG: INTERNAL_LOGIC - Index and tag calculation for updates
    assign update_btb_index = update_pc_i[BTB_INDEX_BITS+1:2];
    assign update_btb_tag   = update_pc_i[ADDR_WIDTH-1:BTB_INDEX_BITS+2];
    
    // AI_TAG: INTERNAL_LOGIC - BHT index calculation using global history
    assign bht_index = global_history_r[BHT_INDEX_BITS-1:0] ^ pc_i[BHT_INDEX_BITS+1:2];
    assign update_bht_index = global_history_r[BHT_INDEX_BITS-1:0] ^ update_pc_i[BHT_INDEX_BITS+1:2];
    
    // AI_TAG: INTERNAL_LOGIC - BTB lookup logic
    assign btb_entry_valid = btb_mem[btb_index].valid;
    assign btb_tag_match   = (btb_mem[btb_index].tag == btb_tag);
    assign btb_valid_match = btb_entry_valid && btb_tag_match;
    
    // AI_TAG: INTERNAL_LOGIC - BHT lookup
    assign bht_counter = bht_mem[bht_index];
    
    // AI_TAG: INTERNAL_LOGIC - Branch prediction logic
    // Use BTB hit and BHT counter to make prediction
    always_comb begin
        if (btb_valid_match) begin
            // BTB hit - use BHT counter for prediction
            predict_taken_o = bht_counter[1];  // MSB of 2-bit counter
            predict_target_o = btb_mem[btb_index].target;
            btb_hit_o = 1'b1;
        end else begin
            // BTB miss - predict not-taken
            predict_taken_o = 1'b0;
            predict_target_o = pc_i + 4;  // Sequential next instruction
            btb_hit_o = 1'b0;
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - BTB update logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // AI_TAG: RESET_STRATEGY - Clear all BTB entries on reset
            for (int i = 0; i < BTB_ENTRIES; i++) begin
                btb_mem[i].valid <= 1'b0;
                btb_mem[i].tag <= '0;
                btb_mem[i].target <= '0;
                btb_mem[i].counter <= 2'b01;  // Weakly not-taken
            end
        end else if (update_i && is_branch_i) begin
            // Update BTB entry
            btb_mem[update_btb_index].valid <= 1'b1;
            btb_mem[update_btb_index].tag <= update_btb_tag;
            btb_mem[update_btb_index].target <= actual_target_i;
            
            // Update 2-bit saturating counter
            if (actual_taken_i && btb_mem[update_btb_index].counter != 2'b11) begin
                btb_mem[update_btb_index].counter <= btb_mem[update_btb_index].counter + 1;
            end else if (!actual_taken_i && btb_mem[update_btb_index].counter != 2'b00) begin
                btb_mem[update_btb_index].counter <= btb_mem[update_btb_index].counter - 1;
            end
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - BHT update logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // AI_TAG: RESET_STRATEGY - Initialize BHT to weakly not-taken
            for (int i = 0; i < BHT_ENTRIES; i++) begin
                bht_mem[i] <= 2'b01;
            end
            global_history_r <= '0;
        end else if (update_i && is_branch_i) begin
            // Update BHT counter
            if (actual_taken_i && bht_mem[update_bht_index] != 2'b11) begin
                bht_mem[update_bht_index] <= bht_mem[update_bht_index] + 1;
            end else if (!actual_taken_i && bht_mem[update_bht_index] != 2'b00) begin
                bht_mem[update_bht_index] <= bht_mem[update_bht_index] - 1;
            end
            
            // Update global history register
            global_history_r <= {global_history_r[GLOBAL_HISTORY_WIDTH-2:0], actual_taken_i};
        end
    end

    // AI_TAG: ASSERTION - a_btb_index_bounds: Ensures BTB index is within bounds
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    property p_btb_index_bounds;
        @(posedge clk_i) disable iff (!rst_ni)
        (btb_index < BTB_ENTRIES);
    endproperty
    a_btb_index_bounds: assert property (p_btb_index_bounds) 
        else $error("BTB index out of bounds: %0d >= %0d", btb_index, BTB_ENTRIES);

    // AI_TAG: ASSERTION - a_bht_index_bounds: Ensures BHT index is within bounds
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    property p_bht_index_bounds;
        @(posedge clk_i) disable iff (!rst_ni)
        (bht_index < BHT_ENTRIES);
    endproperty
    a_bht_index_bounds: assert property (p_bht_index_bounds) 
        else $error("BHT index out of bounds: %0d >= %0d", bht_index, BHT_ENTRIES);

endmodule : branch_predictor

//=============================================================================
// Dependencies: riscv_core_pkg.sv
// Instantiated In:
//   - core/integration/core_subsystem.sv
//   - core/pipeline/fetch_stage.sv
//
// Performance:
//   - Critical Path: BTB/BHT lookup to prediction output
//   - Max Frequency: TBD
//   - Area: TBD
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)
//
// Testing:
//   - Testbench: TBD
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//=============================================================================