
//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: local_predictor.sv
// Module: local_predictor
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Local branch predictor for the tournament predictor. Uses a Branch
//   History Table (BHT) to predict the outcome of branches based on their
//   own past behavior.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_types_pkg::*;

module local_predictor #(
    parameter integer ADDR_WIDTH = 32,
    parameter integer BHT_ENTRIES = 512
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Prediction interface
    input  addr_t pc_i,
    output logic  predict_taken_o,

    // Update interface
    input  branch_update_t update_i
);

    logic [1:0] bht [BHT_ENTRIES-1:0];

    // Index calculations
    logic [$clog2(BHT_ENTRIES)-1:0] pred_bht_idx_c;
    logic [$clog2(BHT_ENTRIES)-1:0] update_bht_idx_c;

    assign pred_bht_idx_c = pc_i[$clog2(BHT_ENTRIES)+1:2];
    assign update_bht_idx_c = update_i.update_pc[$clog2(BHT_ENTRIES)+1:2];

    assign predict_taken_o = bht[pred_bht_idx_c][1];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int i = 0; i < BHT_ENTRIES; i++) begin
                bht[i] <= 2'b01; // Weakly not-taken
            end
        end else begin
            if (update_i.update_valid && update_i.is_branch) begin
                if (update_i.actual_taken) begin
                    if (bht[update_bht_idx_c] < 2'b11) begin
                        bht[update_bht_idx_c] <= bht[update_bht_idx_c] + 1;
                    end
                end else begin
                    if (bht[update_bht_idx_c] > 2'b00) begin
                        bht[update_bht_idx_c] <= bht[update_bht_idx_c] - 1;
                    end
                end
            end
        end
    end

endmodule : local_predictor
