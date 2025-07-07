//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: illegal_instruction_test.sv
// Module: illegal_instruction_test
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Unit test for illegal instruction handling.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module illegal_instruction_test;

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

        // Load an FPU instruction into memory
        tb.mem.mem[0] = 32'h00000053; // fadd.s f0, f0, f0

        // Wait for the instruction to be fetched and executed
        #100;

        // Check for an illegal instruction exception
        if (tb.dut.exception_o.valid && tb.dut.exception_o.cause == CAUSE_ILLEGAL_INSTRUCTION) begin
            $display("Illegal instruction exception successfully detected.");
        end else begin
            $error("Illegal instruction exception not detected.");
        end

        $finish;
    end

endmodule : illegal_instruction_test
