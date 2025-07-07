//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: watchdog_timer.sv
// Module: watchdog_timer
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Core countdown timer for the bus watchdog.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module watchdog_timer # (
    parameter int TIMEOUT_CYCLES = 1000
) (
    input  logic clk_i,
    input  logic rst_ni,
    input  logic enable_i,
    output logic timeout_o
);

    localparam int COUNTER_WIDTH = $clog2(TIMEOUT_CYCLES);

    logic [COUNTER_WIDTH-1:0] counter_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            counter_q <= '0;
        end else if (enable_i) begin
            if (counter_q == TIMEOUT_CYCLES - 1) begin
                counter_q <= '0;
            end else begin
                counter_q <= counter_q + 1;
            end
        end else begin
            counter_q <= '0;
        end
    end

    assign timeout_o = (counter_q == TIMEOUT_CYCLES - 1);

endmodule : watchdog_timer
