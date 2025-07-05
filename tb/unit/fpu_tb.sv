//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: fpu_tb.sv
// Module: fpu_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Initial Testbench
//
// Description:
//   Testbench for the fpu_unit module.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module fpu_tb;

    import riscv_core_pkg::*;
    import riscv_config_pkg::*;
    import riscv_fpu_types_pkg::*;

    // Clock and Reset
    logic clk;
    logic rst_n;

    // FPU Interface
    fpu_req_t  fpu_req;
    logic      fpu_req_ready;
    fpu_rsp_t  fpu_rsp;
    logic      fpu_rsp_ready;

    // Instantiate the FPU Unit
    fpu_unit uut (
        .clk_i(clk),
        .rst_ni(rst_n),
        .fpu_req_i(fpu_req),
        .fpu_req_ready_o(fpu_req_ready),
        .fpu_rsp_o(fpu_rsp),
        .fpu_rsp_ready_i(fpu_rsp_ready)
    );

    // Clock Generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period (100MHz)
    end

    // Test Stimulus
    initial begin
        $display("\n--------------------------------------------------");
        $display("Starting FPU Testbench");
        $display("--------------------------------------------------");

        // Initialize signals
        rst_n = 0;
        fpu_req = '0;
        fpu_rsp_ready = 0;

        #10; // Wait for a bit
        rst_n = 1; // Release reset
        $display("Reset released.");

        // --- Test Scenario 1: FPU_ADD (Placeholder) ---
        $display("\n--- Test Scenario 1: FPU_ADD (Placeholder) ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_ADD;
        fpu_req.operand1 = 32'h40400000; // 3.0 in float
        fpu_req.operand2 = 32'h40800000; // 4.0 in float
        fpu_req.rd_addr = 5'd1; // Example destination register
        fpu_req.rs1_addr = 5'd2; // Example source register
        fpu_req.rs2_addr = 5'd3; // Example source register

        #10; // Request cycle
        wait(fpu_req_ready); // Wait for FPU to accept request
        fpu_req.valid = 0; // De-assert request
        fpu_rsp_ready = 1; // Be ready to accept response

        #10; // Response cycle
        wait(fpu_rsp.valid); // Wait for FPU response
        $display("FPU ADD (3.0 + 4.0) Result: %h (Expected: 40E00000), Error: %b", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0; // De-assert response ready
        #10;

        // --- Test Scenario 2: FPU_SUB (7.0 - 3.0) ---
        $display("\n--- Test Scenario 2: FPU_SUB (7.0 - 3.0) ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_SUB;
        fpu_req.operand1 = 32'h40E00000; // 7.0 in float
        fpu_req.operand2 = 32'h40400000; // 3.0 in float
        fpu_req.rd_addr = 5'd1;
        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;
        #10;
        wait(fpu_rsp.valid);
        $display("FPU SUB (7.0 - 3.0) Result: %h (Expected: 40800000), Error: %b", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 3: FPU_MUL (2.5 * 2.0) ---
        $display("\n--- Test Scenario 3: FPU_MUL (2.5 * 2.0) ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_MUL;
        fpu_req.operand1 = 32'h40200000; // 2.5 in float
        fpu_req.operand2 = 32'h40000000; // 2.0 in float
        fpu_req.rd_addr = 5'd1;
        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;
        #10;
        wait(fpu_rsp.valid);
        $display("FPU MUL (2.5 * 2.0) Result: %h (Expected: 40A00000), Error: %b", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 4: FPU_DIV (10.0 / 2.0) ---
        $display("\n--- Test Scenario 4: FPU_DIV (10.0 / 2.0) ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_DIV;
        fpu_req.operand1 = 32'h41200000; // 10.0 in float
        fpu_req.operand2 = 32'h40000000; // 2.0 in float
        fpu_req.rd_addr = 5'd1;
        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;
        #10;
        wait(fpu_rsp.valid);
        $display("FPU DIV (10.0 / 2.0) Result: %h (Expected: 40A00000), Error: %b", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 5: FPU_DIV (Division by Zero) ---
        $display("\n--- Test Scenario 5: FPU_DIV (Division by Zero) ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_DIV;
        fpu_req.operand1 = 32'h40000000; // 2.0 in float
        fpu_req.operand2 = 32'h00000000; // 0.0 in float
        fpu_req.rd_addr = 5'd1;
        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;
        #10;
        wait(fpu_rsp.valid);
        $display("FPU DIV (2.0 / 0.0) Result: %h, Error: %b (Expected: Error=1)", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 6: FPU_SQRT (25.0) ---
        $display("\n--- Test Scenario 6: FPU_SQRT (25.0) ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_SQRT;
        fpu_req.operand1 = 32'h41C80000; // 25.0 in float
        fpu_req.operand2 = '0; // Not used
        fpu_req.rd_addr = 5'd1;
        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;
        #10;
        wait(fpu_rsp.valid);
        $display("FPU SQRT (25.0) Result: %h (Expected: 40A00000), Error: %b", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 7: FPU_SQRT (-4.0) - Expect Error ---
        $display("\n--- Test Scenario 7: FPU_SQRT (-4.0) - Expect Error ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_SQRT;
        fpu_req.operand1 = 32'hC0800000; // -4.0 in float
        fpu_req.operand2 = '0;
        fpu_req.rd_addr = 5'd1;
        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;
        #10;
        wait(fpu_rsp.valid);
        $display("FPU SQRT (-4.0) Result: %h, Error: %b (Expected: Error=1)", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 8: FPU_F2I (3.75 to Integer) ---
        $display("\n--- Test Scenario 8: FPU_F2I (3.75 to Integer) ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_F2I;
        fpu_req.operand1 = 32'h40700000; // 3.75 in float
        fpu_req.operand2 = '0;
        fpu_req.rd_addr = 5'd1;
        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;
        #10;
        wait(fpu_rsp.valid);
        $display("FPU F2I (3.75) Result: %h (Expected: 00000003), Error: %b", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 9: FPU_I2F (5 to Float) ---
        $display("\n--- Test Scenario 9: FPU_I2F (5 to Float) ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_I2F;
        fpu_req.operand1 = 32'h00000005; // 5 as integer
        fpu_req.operand2 = '0;
        fpu_req.rd_addr = 5'd1;
        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;
        #10;
        wait(fpu_rsp.valid);
        $display("FPU I2F (5) Result: %h (Expected: 40A00000), Error: %b", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 10: Unsupported Opcode ---
        $display("\n--- Test Scenario 10: Unsupported Opcode ---");
        fpu_req.valid = 1;
        fpu_req.opcode = 4'hF; // Invalid opcode
        fpu_req.operand1 = 32'h0;
        fpu_req.operand2 = 32'h0;
        fpu_req.rd_addr = 5'd10;

        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;

        #10;
        wait(fpu_rsp.valid);
        $display("FPU Unsupported Opcode Result: %h, Error: %b (Expected: Error=1)", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 10: Unsupported Opcode ---
        $display("\n--- Test Scenario 10: Unsupported Opcode ---");
        fpu_req.valid = 1;
        fpu_req.opcode = 4'hF; // Invalid opcode
        fpu_req.operand1 = 32'h0;
        fpu_req.operand2 = 32'h0;
        fpu_req.rd_addr = 5'd10;

        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;

        #10;
        wait(fpu_rsp.valid);
        $display("FPU Unsupported Opcode Result: %h, Error: %b (Expected: Error=1)", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 11: FPU_FMA (2.0 * 3.0 + 1.0) ---
        $display("\n--- Test Scenario 11: FPU_FMA (2.0 * 3.0 + 1.0) ---");
        fpu_req.valid = 1;
        fpu_req.opcode = FPU_FMA;
        fpu_req.operand1 = 32'h40000000; // 2.0
        fpu_req.operand2 = 32'h40400000; // 3.0
        fpu_req.operand3 = 32'h3F800000; // 1.0
        fpu_req.rd_addr = 5'd1;
        #10;
        wait(fpu_req_ready);
        fpu_req.valid = 0;
        fpu_rsp_ready = 1;
        #10;
        wait(fpu_rsp.valid);
        $display("FPU FMA (2.0 * 3.0 + 1.0) Result: %h (Expected: 40E00000), Error: %b", fpu_rsp.data, fpu_rsp.error);
        fpu_rsp_ready = 0;
        #10;

        $display("\n--------------------------------------------------");
        $display("FPU Testbench Finished");
        $display("--------------------------------------------------");
        $finish;
    end

endmodule : fpu_tb
