//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: bus_watchdog.sv
// Module: bus_watchdog
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Top-level module for the bus watchdog, integrating the timer, CSR,
//   and monitor components.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module bus_watchdog #(
    // Feature Flags
    parameter bit ENABLE_WATCHDOG = 1,

    // CSR Parameters
    parameter int ADDR_WIDTH = 12,
    parameter int DATA_WIDTH = 32,

    // Bus Parameters
    parameter int BUS_WIDTH = 32
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,

    // CSR Interface
    input  logic [ADDR_WIDTH-1:0] csr_addr_i,
    input  logic [DATA_WIDTH-1:0] csr_wdata_i,
    input  logic                  csr_write_en_i,
    output logic [DATA_WIDTH-1:0] csr_rdata_o,

    // Bus Interface
    input  logic [BUS_WIDTH-1:0]  bus_addr_i,
    input  logic                  bus_req_i,
    input  logic                  bus_gnt_i,

    // Interrupt Output
    output logic                  watchdog_irq_o
);

    // Parameter Sanity Checks
    initial begin
        if (ENABLE_WATCHDOG)
            $display("Bus Watchdog is enabled.");
        else
            $display("Bus Watchdog is disabled.");
    end

    // Instantiate Watchdog Components
    if (ENABLE_WATCHDOG) begin : gen_watchdog
        logic watchdog_enable_w;
        logic timeout_w;
        logic [DATA_WIDTH-1:0] timeout_value_w;

        // CSR Module
        watchdog_csr #(
            .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH)
        ) u_watchdog_csr (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            .csr_addr_i(csr_addr_i),
            .csr_wdata_i(csr_wdata_i),
            .csr_write_en_i(csr_write_en_i),
            .csr_rdata_o(csr_rdata_o),
            .watchdog_enable_o(watchdog_enable_w),
            .timeout_value_o(timeout_value_w),
            .timeout_status_i(timeout_w)
        );

        logic monitor_enable_w;

        // Monitor Module
        watchdog_monitor #(
            .BUS_WIDTH(BUS_WIDTH)
        ) u_watchdog_monitor (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            .bus_addr_i(bus_addr_i),
            .bus_req_i(bus_req_i),
            .bus_gnt_i(bus_gnt_i),
            .watchdog_enable_o(monitor_enable_w)
        );

        // Timer Module
        watchdog_timer #(
            .TIMEOUT_CYCLES(timeout_value_w)
        ) u_watchdog_timer (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            .enable_i(watchdog_enable_w & monitor_enable_w),
            .timeout_o(timeout_w)
        );

        assign watchdog_irq_o = timeout_w;

    end else begin : gen_no_watchdog
        // If watchdog is disabled, tie off outputs
        assign csr_rdata_o = '0;
        assign watchdog_irq_o = 1'b0;
    end

endmodule : bus_watchdog
