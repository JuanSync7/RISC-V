//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: watchdog_csr.sv
// Module: watchdog_csr
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Control and Status Registers (CSR) for the bus watchdog.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module watchdog_csr #(
    parameter int ADDR_WIDTH = 12,
    parameter int DATA_WIDTH = 32
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,

    // CSR Interface
    input  logic [ADDR_WIDTH-1:0] csr_addr_i,
    input  logic [DATA_WIDTH-1:0] csr_wdata_i,
    input  logic                  csr_write_en_i,
    output logic [DATA_WIDTH-1:0] csr_rdata_o,

    // Watchdog Control and Status
    output logic                  watchdog_enable_o,
    output logic [DATA_WIDTH-1:0] timeout_value_o,
    input  logic                  timeout_status_i
);

    // CSR Addresses
    localparam int WDT_ENABLE_ADDR = 12'hB00;
    localparam int WDT_TIMEOUT_ADDR = 12'hB01;
    localparam int WDT_STATUS_ADDR = 12'hB02;

    // CSR Registers
    logic                  watchdog_enable_q;
    logic [DATA_WIDTH-1:0] timeout_value_q;

    // CSR Read/Write Logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            watchdog_enable_q <= 1'b0;
            timeout_value_q   <= 32'd1000; // Default timeout
        end else if (csr_write_en_i) begin
            case (csr_addr_i)
                WDT_ENABLE_ADDR:  watchdog_enable_q <= csr_wdata_i[0];
                WDT_TIMEOUT_ADDR: timeout_value_q   <= csr_wdata_i;
                default:          begin
                    watchdog_enable_q <= watchdog_enable_q;
                    timeout_value_q   <= timeout_value_q;
                end
            endcase
        end
    end

    // CSR Read Logic
    always_comb begin
        case (csr_addr_i)
            WDT_ENABLE_ADDR:  csr_rdata_o = {31'b0, watchdog_enable_q};
            WDT_TIMEOUT_ADDR: csr_rdata_o = timeout_value_q;
            WDT_STATUS_ADDR:  csr_rdata_o = {31'b0, timeout_status_i};
            default:          csr_rdata_o = 32'b0;
        endcase
    end

    // Assign outputs
    assign watchdog_enable_o = watchdog_enable_q;
    assign timeout_value_o   = timeout_value_q;

endmodule : watchdog_csr
