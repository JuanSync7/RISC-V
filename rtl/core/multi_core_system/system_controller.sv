//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: system_controller.sv
// Module: system_controller
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Manages system-wide configuration, status, and top-level interface clock/reset connections.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module system_controller #(
    parameter integer NUM_CORES = DEFAULT_NUM_CORES // AI_TAG: PARAM_DESC - Number of cores in the system
) (
    input  logic        clk_i,     // AI_TAG: PORT_DESC - System clock
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                   // AI_TAG: PORT_TIMING - Rising edge active
    input  logic        rst_ni,    // AI_TAG: PORT_DESC - Asynchronous active-low reset
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
                                   // AI_TAG: PORT_TIMING - Asynchronous assert, synchronous deassert

    // System configuration interface
    input  logic [31:0] sys_config_i,     // AI_TAG: PORT_DESC - System configuration register
                                          // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                          // AI_TAG: PORT_TIMING - Registered input
    output logic [31:0] sys_status_o,     // AI_TAG: PORT_DESC - System status register
                                          // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                          // AI_TAG: PORT_DEFAULT_STATE - 32'h0000_0001 (system ready)
                                          // AI_TAG: PORT_TIMING - Combinatorial output

    // External memory interfaces using proper SystemVerilog interfaces
    axi4_if.master axi4_if,
    chi_if.rn chi_if,
    tilelink_if.master tl_if,

    // Inputs for sys_status_o calculation
    input  logic [31:0] current_ipc_calculated_i,
    input  logic [7:0]  cache_hit_rate_l1_i,
    input  logic        any_core_active_i,
    input  logic        pipeline_bottleneck_i,
    input  logic        high_power_mode_i,
    input  logic        good_bp_i
);

    //-------------------------------------------------------------------------
    // Connect interface clocks and resets
    //-------------------------------------------------------------------------
    assign axi4_if.aclk = clk_i;
    assign axi4_if.aresetn = rst_ni;
    assign chi_if.clk = clk_i;
    assign chi_if.resetn = rst_ni;
    assign tl_if.clk = clk_i;
    assign tl_if.resetn = rst_ni;

    //-------------------------------------------------------------------------
    // Enhanced system status with comprehensive monitoring
    //-------------------------------------------------------------------------
    assign sys_status_o = {
        4'h0,                                    // Reserved [31:28]
        current_ipc_calculated_i[11:0],          // Current IPC [27:16] (Q8.4 format)
        cache_hit_rate_l1_i[7:0],                // L1 hit rate [15:8] (percentage)
        any_core_active_i,                       // Any core active [7]
        pipeline_bottleneck_i,                   // Pipeline bottleneck [6]
        high_power_mode_i,                       // High power mode [5]
        good_bp_i,                               // Good BP [4]
        NUM_CORES[3:0]                           // Number of cores [3:0]
    };

endmodule : system_controller

//=============================================================================
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | DesignAI           | Initial release - Extracted from multi_core_system.sv
//=============================================================================
