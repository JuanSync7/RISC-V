
//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: selector.sv
// Module: selector
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Selector for the tournament branch predictor. Chooses between the local
//   and global predictors based on which one has been more accurate for a
//   given branch history.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_types_pkg::*;
import riscv_config_pkg::*;
import riscv_bp_types_pkg::*;

module selector #(
    parameter integer ADDR_WIDTH = CONFIG_ADDR_WIDTH,
    parameter integer GLOBAL_HISTORY_WIDTH = CONFIG_GLOBAL_HISTORY_WIDTH,
    parameter integer SELECTOR_ENTRIES = CONFIG_SELECTOR_ENTRIES
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Prediction interface
    input  addr_t pc_i,
    input  logic  local_prediction_i,
    input  logic  global_prediction_i,
    output logic  final_prediction_o,

    // Update interface
    input  branch_update_t update_i
);

    logic [1:0] selector_table [SELECTOR_ENTRIES-1:0];
    logic [GLOBAL_HISTORY_WIDTH-1:0] ghr_r;

    // Index calculations
    logic [$clog2(SELECTOR_ENTRIES)-1:0] pred_selector_idx_c;
    logic [$clog2(SELECTOR_ENTRIES)-1:0] update_selector_idx_c;

    assign pred_selector_idx_c = ghr_r ^ pc_i[$clog2(SELECTOR_ENTRIES)+1:2];
    assign update_selector_idx_c = ghr_r ^ update_i.update_pc[$clog2(SELECTOR_ENTRIES)+1:2];

    assign final_prediction_o = selector_table[pred_selector_idx_c][1] ? global_prediction_i : local_prediction_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            ghr_r <= '0;
            for (int i = 0; i < SELECTOR_ENTRIES; i++) begin
                selector_table[i] <= 2'b10; // Default to global predictor
            end
        end else begin
            if (update_i.update_valid && update_i.is_branch) begin
                ghr_r <= {ghr_r[GLOBAL_HISTORY_WIDTH-2:0], update_i.actual_taken};

                logic local_correct  = (local_prediction_i == update_i.actual_taken);
                logic global_correct = (global_prediction_i == update_i.actual_taken);

                if (global_correct && !local_correct) begin
                    if (selector_table[update_selector_idx_c] < 2'b11) begin
                        selector_table[update_selector_idx_c] <= selector_table[update_selector_idx_c] + 1;
                    end
                end else if (!global_correct && local_correct) begin
                    if (selector_table[update_selector_idx_c] > 2'b00) begin
                        selector_table[update_selector_idx_c] <= selector_table[update_selector_idx_c] - 1;
                    end
                end
            end
        end
    end

endmodule : selector
