//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: ooo_engine.sv
// Module: ooo_engine
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Top-level module for the Out-of-Order (OoO) execution engine. It instantiates
//   and connects the Reservation Station (RS), Reorder Buffer (ROB),
//   Register Renaming (RR), and Multiple Execution Units (MEU) to form a
//   complete OoO pipeline.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import ooo_pkg::*;

module ooo_engine #(
    parameter integer DATA_WIDTH     = ooo_pkg::DATA_WIDTH,
    parameter integer PC_WIDTH       = ooo_pkg::PC_WIDTH,
    parameter integer REG_ADDR_WIDTH = ooo_pkg::REG_ADDR_WIDTH,
    parameter integer RS_SIZE        = ooo_pkg::RS_SIZE,
    parameter integer ROB_SIZE       = ooo_pkg::ROB_SIZE
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Flush signal (e.g., from branch misprediction or exception)
    input  logic flush_i,

    // Interface from Decode Stage
    input  ooo_dispatch_t decode_dispatch_i, // Instruction to be dispatched to OoO engine
    output logic          decode_ready_o,    // OoO engine is ready to accept a new instruction

    // Interface to Commit Stage (architectural update)
    output ooo_commit_t   commit_o,          // Instruction ready to commit
    input  logic          commit_ready_i     // Commit stage is ready to accept a committed instruction
);

    // Internal signals for connecting OoO components
    ooo_dispatch_t rr_dispatch_o; // From Register Renaming to RS/ROB
    logic          rr_rob_new_tag_c; // New ROB tag from ROB to RR
    logic          rob_ready_c;      // ROB ready signal to RR

    ooo_issue_t    rs_issue_o;    // From RS to MEU
    logic          meu_issue_ready_c; // MEU ready signal to RS

    ooo_result_t   meu_result_o;  // From MEU (CDB) to RS, RR, ROB

    // Instantiate Register Renaming Unit
    register_renaming #(
        .DATA_WIDTH    (DATA_WIDTH),
        .ARCH_REG_COUNT(32),
        .ROB_SIZE      (ROB_SIZE),
        .REG_ADDR_WIDTH(REG_ADDR_WIDTH)
    ) u_register_renaming (
        .clk_i             (clk_i),
        .rst_ni            (rst_ni),
        .flush_i           (flush_i),
        .decode_valid_i    (decode_dispatch_i.valid),
        .decode_rs1_addr_i (decode_dispatch_i.q_rs1), // Using q_rs1 as rs1_addr for now, will be proper arch reg later
        .decode_rs2_addr_i (decode_dispatch_i.q_rs2), // Using q_rs2 as rs2_addr for now, will be proper arch reg later
        .decode_rd_addr_i  (decode_dispatch_i.rd_addr),
        .decode_rd_write_en_i(decode_dispatch_i.rd_write_en),
        .decode_pc_i       (decode_dispatch_i.pc),
        .decode_opcode_i   (decode_dispatch_i.opcode),
        .dispatch_o        (rr_dispatch_o),
        .rob_new_tag_i     (rr_rob_new_tag_c),
        .rob_ready_i       (rob_ready_c),
        .result_i          (meu_result_o),
        .commit_i          (commit_o) // Commit info from ROB to RR
    );

    // Instantiate Reorder Buffer
    reorder_buffer #(
        .DATA_WIDTH    (DATA_WIDTH),
        .ROB_SIZE      (ROB_SIZE),
        .PC_WIDTH      (PC_WIDTH),
        .REG_ADDR_WIDTH(REG_ADDR_WIDTH)
    ) u_reorder_buffer (
        .clk_i            (clk_i),
        .rst_ni           (rst_ni),
        .flush_i          (flush_i),
        .dispatch_i       (rr_dispatch_o), // Dispatch from RR
        .dispatch_ready_o (rob_ready_c),   // ROB ready to RR
        .execute_result_i (meu_result_o),  // Result from MEU (CDB)
        .commit_o         (commit_o),      // Instruction ready to commit
        .commit_ready_i   (commit_ready_i) // Commit stage ready
    );

    // Connect ROB's new tag output to Register Renaming
    assign rr_rob_new_tag_c = rr_dispatch_o.rob_tag; // ROB assigns the tag, RR uses it

    // Instantiate Reservation Station
    reservation_station #(
        .DATA_WIDTH    (DATA_WIDTH),
        .RS_SIZE       (RS_SIZE),
        .ROB_ADDR_WIDTH(ROB_ADDR_WIDTH)
    ) u_reservation_station (
        .clk_i            (clk_i),
        .rst_ni           (rst_ni),
        .flush_i          (flush_i),
        .dispatch_i       (rr_dispatch_o), // Dispatch from RR
        .dispatch_ready_o (decode_ready_o), // RS ready to Decode stage
        .result_i         (meu_result_o),  // Result from MEU (CDB)
        .issue_o          (rs_issue_o),    // Issue to MEU
        .issue_ready_i    (meu_issue_ready_c) // MEU ready
    );

    // Instantiate Multiple Execution Units
    multiple_execution_units #(
        .DATA_WIDTH    (DATA_WIDTH),
        .ROB_ADDR_WIDTH(ROB_ADDR_WIDTH),
        .NUM_ALU_UNITS (2),
        .NUM_MULT_UNITS(1),
        .NUM_DIV_UNITS (1)
    ) u_multiple_execution_units (
        .clk_i           (clk_i),
        .rst_ni          (rst_ni),
        .issue_ready_o   (meu_issue_ready_c), // MEU ready to RS
        .issue_i         (rs_issue_o),    // Issue from RS
        .result_o        (meu_result_o)   // Result to CDB (RS, RR, ROB)
    );

endmodule : ooo_engine