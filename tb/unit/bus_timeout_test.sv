//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: bus_timeout_test.sv
// Module: bus_timeout_test
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Unit test for the bus timeout mechanism.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module bus_timeout_test;

    import riscv_core_pkg::*;

    // Testbench signals
    logic clk = 0;
    logic rst_n = 0;

    // Instantiate the core_subsystem testbench
    core_subsystem_tb tb();

    // Test sequence
    initial begin
        // Wait for reset to de-assert
        @(posedge tb.rst_n);

        // Initiate a memory request
        tb.mem_if.req_valid = 1'b1;
        tb.mem_if.req.addr = 32'h1000;

        // Wait for the timeout period
        #1000;

        // Check that the memory wrapper signals an error
        if (tb.dut.dcache_if.rsp.error) begin
            $display("Bus timeout successfully detected.");
        end else begin
            $error("Bus timeout not detected.");
        end

        $finish;
    end

endmodule : bus_timeout_test
