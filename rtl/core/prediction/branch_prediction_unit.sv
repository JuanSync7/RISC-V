//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: branch_prediction_unit.sv
// Module: branch_prediction_unit
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   This module encapsulates the branch prediction logic, including the
//   branch predictor instantiation and the logic for generating branch updates.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module branch_prediction_unit #(
    parameter string BRANCH_PREDICTOR_TYPE = DEFAULT_BRANCH_PREDICTOR_TYPE,
    parameter addr_t ADDR_WIDTH = ADDR_WIDTH // Assuming ADDR_WIDTH is passed down or imported
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    input  addr_t       pc_i,
    output branch_prediction_t bp_prediction_o,
    input  branch_update_t bp_update_i,

    // Inputs from execute stage for branch update
    input  logic        ex_mem_reg_valid_i,
    input  logic        ex_mem_reg_ctrl_is_branch_i,
    input  addr_t       ex_mem_reg_pc_i,
    input  logic        ex_mem_branch_taken_i,
    input  addr_t       ex_mem_branch_target_i,
    input  logic        id_ex_reg_ctrl_is_jal_i,
    input  addr_t       id_ex_reg_jal_target_i,
    input  logic        id_ex_reg_ctrl_is_jalr_i
);

    // Internal signals for branch prediction
    branch_prediction_t bp_prediction;
    branch_update_t bp_update;

    //------------------------------------------------------------------------- 
    // Branch Prediction (if enabled)
    //------------------------------------------------------------------------- 
    generate
        if (BRANCH_PREDICTOR_TYPE != "STATIC") begin : gen_dynamic_branch_predictor
            // AI_TAG: INTERNAL_BLOCK - Dynamic branch predictor
            branch_predictor #(.BTB_ENTRIES(DEFAULT_BTB_ENTRIES), .BHT_ENTRIES(DEFAULT_BHT_ENTRIES), .RAS_ENTRIES(DEFAULT_RAS_ENTRIES)) u_branch_predictor (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .pc_i(pc_i),
                .predict_taken_o(bp_prediction.taken),
                .predict_target_o(bp_prediction.target),
                .btb_hit_o(bp_prediction.btb_hit),
                .ras_predict_target_o(bp_prediction.ras_target),
                .update_i(bp_update.update_valid),
                .update_pc_i(bp_update.update_pc),
                .actual_taken_i(bp_update.actual_taken),
                .actual_target_i(bp_update.actual_target),
                .is_branch_i(bp_update.is_branch),
                .is_jal_i(bp_update.is_jal),
                .jal_target_i(bp_update.jal_target),
                .is_jalr_i(bp_update.is_jalr)
            );
        end else begin : gen_static_prediction
            // Static prediction - always not taken
            assign bp_prediction.taken = 1'b0;
            assign bp_prediction.target = '0;
            assign bp_prediction.btb_hit = 1'b0;
            assign bp_prediction.ras_target = '0;
        end
    endgenerate

    //------------------------------------------------------------------------- 
    // Branch Update Signal Generation
    //------------------------------------------------------------------------- 
    // AI_TAG: INTERNAL_LOGIC - Generate branch predictor update from execute stage
    always_comb begin : proc_branch_update
        bp_update.update_valid = ex_mem_reg_valid_i && ex_mem_reg_ctrl_is_branch_i;
        bp_update.update_pc = ex_mem_reg_pc_i;
        bp_update.actual_taken = ex_mem_branch_taken_i;
        bp_update.actual_target = ex_mem_branch_target_i;
        bp_update.is_branch = ex_mem_reg_ctrl_is_branch_i;
        bp_update.is_jal = id_ex_reg_ctrl_is_jal_i;
        bp_update.jal_target = id_ex_reg_jal_target_i;
        bp_update.is_jalr = id_ex_reg_ctrl_is_jalr_i;
    end

    assign bp_prediction_o = bp_prediction;

endmodule : branch_prediction_unit

`default_nettype wire
