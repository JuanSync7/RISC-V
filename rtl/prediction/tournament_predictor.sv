
//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: tournament_predictor.sv
// Module: tournament_predictor
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Top-level structural module for the tournament branch predictor.
//   Instantiates and connects the BTB, local predictor, global predictor,
//   and selector modules.
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

    logic local_prediction_c;
    logic global_prediction_c;
    logic final_prediction_c;
    logic btb_hit_c;
    addr_t btb_target_c;

    btb #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .BTB_ENTRIES(BTB_ENTRIES)
    ) i_btb (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .pc_i(pc_i),
        .btb_hit_o(btb_hit_c),
        .btb_target_o(btb_target_c),
        .update_i(update_i)
    );

    local_predictor #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .BHT_ENTRIES(BHT_ENTRIES)
    ) i_local_predictor (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .pc_i(pc_i),
        .predict_taken_o(local_prediction_c),
        .update_i(update_i)
    );

    global_predictor #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .GLOBAL_HISTORY_WIDTH(GLOBAL_HISTORY_WIDTH),
        .PHT_ENTRIES(PHT_ENTRIES)
    ) i_global_predictor (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .pc_i(pc_i),
        .predict_taken_o(global_prediction_c),
        .update_i(update_i)
    );

    selector #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .GLOBAL_HISTORY_WIDTH(GLOBAL_HISTORY_WIDTH),
        .SELECTOR_ENTRIES(SELECTOR_ENTRIES)
    ) i_selector (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .pc_i(pc_i),
        .local_prediction_i(local_prediction_c),
        .global_prediction_i(global_prediction_c),
        .final_prediction_o(final_prediction_c),
        .update_i(update_i)
    );

    assign prediction_o.predict_taken = final_prediction_c && btb_hit_c;
    assign prediction_o.predict_target = btb_target_c;
    assign prediction_o.btb_hit = btb_hit_c;

endmodule : tournament_predictor
