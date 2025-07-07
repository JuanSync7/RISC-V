//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: watchdog_monitor.sv
// Module: watchdog_monitor
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Monitors bus activity to enable the watchdog timer.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module watchdog_monitor #(
    parameter int BUS_WIDTH = 32
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,

    // Bus Interface
    input  logic [BUS_WIDTH-1:0]  bus_addr_i,
    input  logic                  bus_req_i,
    input  logic                  bus_gnt_i,

    // Watchdog Enable
    output logic                  watchdog_enable_o
);

    // Simple logic to detect a stuck bus request
    // Enable the watchdog if the request is high but grant is low
    assign watchdog_enable_o = bus_req_i & ~bus_gnt_i;

endmodule : watchdog_monitor
