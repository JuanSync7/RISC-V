
//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: btb.sv
// Module: btb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Branch Target Buffer (BTB) for the tournament branch predictor. Caches
//   the target addresses of recently executed branch instructions.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_types_pkg::*;

module btb #(
    parameter integer ADDR_WIDTH = 32,
    parameter integer BTB_ENTRIES = 128
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Prediction interface
    input  addr_t pc_i,
    output logic  btb_hit_o,
    output addr_t btb_target_o,

    // Update interface
    input  branch_update_t update_i
);

    // BTB: Tag + Target
    logic [ADDR_WIDTH-1:0] btb_tag_r    [BTB_ENTRIES-1:0];
    logic [ADDR_WIDTH-1:0] btb_target_r [BTB_ENTRIES-1:0];
    logic                  btb_valid_r  [BTB_ENTRIES-1:0];

    // Index calculations
    logic [$clog2(BTB_ENTRIES)-1:0] pred_btb_idx_c;
    logic [$clog2(BTB_ENTRIES)-1:0] update_btb_idx_c;

    assign pred_btb_idx_c = pc_i[$clog2(BTB_ENTRIES)+1:2];
    assign update_btb_idx_c = update_i.update_pc[$clog2(BTB_ENTRIES)+1:2];

    assign btb_hit_o = btb_valid_r[pred_btb_idx_c] && (btb_tag_r[pred_btb_idx_c] == pc_i);
    assign btb_target_o = btb_target_r[pred_btb_idx_c];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int i = 0; i < BTB_ENTRIES; i++) begin
                btb_valid_r[i] <= 1'b0;
            end
        end else begin
            if (update_i.update_valid && update_i.is_branch) begin
                btb_tag_r[update_btb_idx_c]    <= update_i.update_pc;
                btb_target_r[update_btb_idx_c] <= update_i.actual_target;
                btb_valid_r[update_btb_idx_c]  <= 1'b1;
            end
        end
    end

endmodule : btb
