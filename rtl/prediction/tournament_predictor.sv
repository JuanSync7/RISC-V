//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: tournament_predictor.sv
// Module: tournament_predictor
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Advanced tournament branch predictor. It combines a local predictor
//   (based on per-branch history) and a global predictor (based on global
//   branch history) and uses a selector to choose the most accurate
//   prediction for a given branch.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_types_pkg::*;

module tournament_predictor #(
    parameter integer ADDR_WIDTH = 32,
    parameter integer GLOBAL_HISTORY_WIDTH = 8,
    parameter integer BTB_ENTRIES = 128,
    parameter integer BHT_ENTRIES = 512,
    parameter integer PHT_ENTRIES = 4096,
    parameter integer SELECTOR_ENTRIES = 4096
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Prediction request from Fetch Stage
    input  addr_t pc_i,
    output branch_prediction_t prediction_o,

    // Branch resolution from Writeback/Execute Stage
    input  branch_update_t     update_i
);

    //---------------------------------------------------------------------------
    // Internal Structures
    //---------------------------------------------------------------------------
    logic [1:0] bht [BHT_ENTRIES-1:0];
    logic [GLOBAL_HISTORY_WIDTH-1:0] ghr_r;
    logic [1:0] pht [PHT_ENTRIES-1:0];
    logic [1:0] selector_table [SELECTOR_ENTRIES-1:0];

    // BTB: Tag + Target
    logic [ADDR_WIDTH-1:0] btb_tag_r    [BTB_ENTRIES-1:0];
    logic [ADDR_WIDTH-1:0] btb_target_r [BTB_ENTRIES-1:0];
    logic                  btb_valid_r  [BTB_ENTRIES-1:0];


    //---------------------------------------------------------------------------
    // Prediction Logic
    //---------------------------------------------------------------------------
    logic local_prediction_c;
    logic global_prediction_c;
    logic final_prediction_c;
    logic btb_hit_c;

    // Index calculations
    logic [$clog2(BHT_ENTRIES)-1:0]      pred_bht_idx_c;
    logic [$clog2(PHT_ENTRIES)-1:0]      pred_pht_idx_c;
    logic [$clog2(SELECTOR_ENTRIES)-1:0] pred_selector_idx_c;
    logic [$clog2(BTB_ENTRIES)-1:0]      pred_btb_idx_c;

    assign pred_bht_idx_c = pc_i[$clog2(BHT_ENTRIES)+1:2];
    assign pred_pht_idx_c = ghr_r ^ pc_i[$clog2(PHT_ENTRIES)+1:2];
    assign pred_selector_idx_c = ghr_r ^ pc_i[$clog2(SELECTOR_ENTRIES)+1:2];
    assign pred_btb_idx_c = pc_i[$clog2(BTB_ENTRIES)+1:2];

    always_comb begin
        local_prediction_c  = bht[pred_bht_idx_c][1];
        global_prediction_c = pht[pred_pht_idx_c][1];

        if (selector_table[pred_selector_idx_c][1]) begin
            final_prediction_c = global_prediction_c;
        end else begin
            final_prediction_c = local_prediction_c;
        end

        btb_hit_c = (btb_valid_r[pred_btb_idx_c] && (btb_tag_r[pred_btb_idx_c] == pc_i));

        prediction_o.predict_taken = final_prediction_c && btb_hit_c;
        prediction_o.predict_target = btb_target_r[pred_btb_idx_c];
        prediction_o.btb_hit = btb_hit_c;
    end

    //---------------------------------------------------------------------------
    // Update Logic
    //---------------------------------------------------------------------------
    logic [$clog2(BHT_ENTRIES)-1:0]      update_bht_idx_c;
    logic [$clog2(PHT_ENTRIES)-1:0]      update_pht_idx_c;
    logic [$clog2(SELECTOR_ENTRIES)-1:0] update_selector_idx_c;
    logic [$clog2(BTB_ENTRIES)-1:0]      update_btb_idx_c;

    assign update_bht_idx_c = update_i.update_pc[$clog2(BHT_ENTRIES)+1:2];
    assign update_pht_idx_c = ghr_r ^ update_i.update_pc[$clog2(PHT_ENTRIES)+1:2];
    assign update_selector_idx_c = ghr_r ^ update_i.update_pc[$clog2(SELECTOR_ENTRIES)+1:2];
    assign update_btb_idx_c = update_i.update_pc[$clog2(BTB_ENTRIES)+1:2];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            ghr_r <= '0;
            for (int i = 0; i < BTB_ENTRIES; i++) btb_valid_r[i] <= 1'b0;
            // Other tables can remain uninitialized
        end else begin
            if (update_i.update_valid && update_i.is_branch) begin
                ghr_r <= {ghr_r[GLOBAL_HISTORY_WIDTH-2:0], update_i.actual_taken};

                logic resolved_local_pred  = bht[update_bht_idx_c][1];
                logic resolved_global_pred = pht[update_pht_idx_c][1];

                // Update BHT
                if (update_i.actual_taken) begin
                    if (bht[update_bht_idx_c] < 2'b11) bht[update_bht_idx_c] <= bht[update_bht_idx_c] + 1;
                end else begin
                    if (bht[update_bht_idx_c] > 2'b00) bht[update_bht_idx_c] <= bht[update_bht_idx_c] - 1;
                end

                // Update PHT
                if (update_i.actual_taken) begin
                    if (pht[update_pht_idx_c] < 2'b11) pht[update_pht_idx_c] <= pht[update_pht_idx_c] + 1;
                end else begin
                    if (pht[update_pht_idx_c] > 2'b00) pht[update_pht_idx_c] <= pht[update_pht_idx_c] - 1;
                end

                // Update Selector Table
                logic local_correct  = (resolved_local_pred == update_i.actual_taken);
                logic global_correct = (resolved_global_pred == update_i.actual_taken);

                if (global_correct && !local_correct) begin
                    if (selector_table[update_selector_idx_c] < 2'b11) selector_table[update_selector_idx_c] <= selector_table[update_selector_idx_c] + 1;
                end else if (!global_correct && local_correct) begin
                    if (selector_table[update_selector_idx_c] > 2'b00) selector_table[update_selector_idx_c] <= selector_table[update_selector_idx_c] - 1;
                end

                // Update BTB
                btb_tag_r[update_btb_idx_c]    <= update_i.update_pc;
                btb_target_r[update_btb_idx_c] <= update_i.actual_target;
                btb_valid_r[update_btb_idx_c]  <= 1'b1;
            end
        end
    end

endmodule : tournament_predictor

`