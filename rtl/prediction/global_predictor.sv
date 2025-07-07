
//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: global_predictor.sv
// Module: global_predictor
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Global branch predictor for the tournament predictor. Uses a Pattern
//   History Table (PHT) and a Global History Register (GHR) to predict
//   branch outcomes based on the recent history of all branches.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_types_pkg::*;

module global_predictor #(
    parameter integer ADDR_WIDTH = 32,
    parameter integer GLOBAL_HISTORY_WIDTH = 8,
    parameter integer PHT_ENTRIES = 4096
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Prediction interface
    input  addr_t pc_i,
    output logic  predict_taken_o,

    // Update interface
    input  branch_update_t update_i
);

    logic [GLOBAL_HISTORY_WIDTH-1:0] ghr_r;
    logic [1:0] pht [PHT_ENTRIES-1:0];

    // Index calculations
    logic [$clog2(PHT_ENTRIES)-1:0] pred_pht_idx_c;
    logic [$clog2(PHT_ENTRIES)-1:0] update_pht_idx_c;

    assign pred_pht_idx_c = ghr_r ^ pc_i[$clog2(PHT_ENTRIES)+1:2];
    assign update_pht_idx_c = ghr_r ^ update_i.update_pc[$clog2(PHT_ENTRIES)+1:2];

    assign predict_taken_o = pht[pred_pht_idx_c][1];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            ghr_r <= '0;
            for (int i = 0; i < PHT_ENTRIES; i++) begin
                pht[i] <= 2'b01; // Weakly not-taken
            end
        end else begin
            if (update_i.update_valid && update_i.is_branch) begin
                ghr_r <= {ghr_r[GLOBAL_HISTORY_WIDTH-2:0], update_i.actual_taken};

                if (update_i.actual_taken) begin
                    if (pht[update_pht_idx_c] < 2'b11) begin
                        pht[update_pht_idx_c] <= pht[update_pht_idx_c] + 1;
                    end
                end else begin
                    if (pht[update_pht_idx_c] > 2'b00) begin
                        pht[update_pht_idx_c] <= pht[update_pht_idx_c] - 1;
                    end
                end
            end
        end
    end

endmodule : global_predictor
