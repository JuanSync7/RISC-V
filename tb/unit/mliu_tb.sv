//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: mliu_tb.sv
// Module: mliu_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Initial Testbench
//
// Description:
//   Testbench for the ml_inference_unit module.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module mliu_tb;

    import riscv_core_pkg::*;
    import riscv_config_pkg::*;
    import riscv_ml_types_pkg::*;

    // Clock and Reset
    logic clk;
    logic rst_n;

    // MLIU Interface
    mliu_req_t  mliu_req;
    logic       mliu_req_ready;
    mliu_rsp_t  mliu_rsp;
    logic       mliu_rsp_ready;

    // Instantiate the MLIU Unit
    ml_inference_unit uut (
        .clk_i(clk),
        .rst_ni(rst_n),
        .mliu_req_i(mliu_req),
        .mliu_req_ready_o(mliu_req_ready),
        .mliu_rsp_o(mliu_rsp),
        .mliu_rsp_ready_i(mliu_rsp_ready)
    );

    // Clock Generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period (100MHz)
    end

    // Test Stimulus
    initial begin
        $display("\n--------------------------------------------------");
        $display("Starting MLIU Testbench");
        $display("--------------------------------------------------");

        // Initialize signals
        rst_n = 0;
        mliu_req = '0;
        mliu_rsp_ready = 0;

        #10; // Wait for a bit
        rst_n = 1; // Release reset
        $display("Reset released.");

        // --- Test Scenario 1: MLIU_MATRIX_MUL (Placeholder) ---
        $display("\n--- Test Scenario 1: MLIU_MATRIX_MUL (Placeholder) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_MATRIX_MUL;
        mliu_req.operand1 = 32'h0000000A; // Example input
        mliu_req.operand2 = 32'h00000005; // Example weight
        mliu_req.rd_addr = 5'd1;

        #10; // Request cycle
        wait(mliu_req_ready); // Wait for MLIU to accept request
        mliu_req.valid = 0; // De-assert request
        mliu_rsp_ready = 1; // Be ready to accept response

        #10; // Response cycle
        wait(mliu_rsp.valid); // Wait for MLIU response
        $display("MLIU MATRIX_MUL Result: %h, Error: %b (Expected: 0000000F)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0; // De-assert response ready
        #10;

        // --- Test Scenario 2: MLIU_CONVOLUTION (Placeholder) ---
        $display("\n--- Test Scenario 2: MLIU_CONVOLUTION (Placeholder) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_CONVOLUTION;
        mliu_req.operand1 = 32'h00000003; // Example input
        mliu_req.operand2 = 32'h00000002; // Example kernel
        mliu_req.rd_addr = 5'd2;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU CONVOLUTION Result: %h, Error: %b (Expected: 00000006)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        // --- Test Scenario 3: MLIU_ACTIVATION (ReLU) ---
        $display("\n--- Test Scenario 3: MLIU_ACTIVATION (ReLU) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_ACTIVATION;
        mliu_req.operand1 = 32'hFFFFFFF0; // -16
        mliu_req.operand2 = '0;
        mliu_req.rd_addr = 5'd3;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU ACTIVATION (-16) Result: %h, Error: %b (Expected: 00000000)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_ACTIVATION;
        mliu_req.operand1 = 32'h0000000A; // 10
        mliu_req.operand2 = '0;
        mliu_req.rd_addr = 5'd3;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU ACTIVATION (10) Result: %h, Error: %b (Expected: 0000000A)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        // --- Test Scenario 4: MLIU_POOLING (Max Pooling) ---
        $display("\n--- Test Scenario 4: MLIU_POOLING (Max Pooling) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_POOLING;
        mliu_req.operand1 = 32'h00000007; // 7
        mliu_req.operand2 = 32'h0000000C; // 12
        mliu_req.rd_addr = 5'd4;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU POOLING (7, 12) Result: %h, Error: %b (Expected: 0000000C)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        // --- Test Scenario 4: MLIU_POOLING (Max Pooling) ---
        $display("\n--- Test Scenario 4: MLIU_POOLING (Max Pooling) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_POOLING;
        mliu_req.operand1 = 32'h00000007; // 7
        mliu_req.operand2 = 32'h0000000C; // 12
        mliu_req.rd_addr = 5'd4;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU POOLING (7, 12) Result: %h, Error: %b (Expected: 0000000C)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        // --- Test Scenario 5: MLIU_RELU (ReLU Activation) ---
        $display("\n--- Test Scenario 5: MLIU_RELU (ReLU Activation) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_RELU;
        mliu_req.operand1 = 32'hFFFFFFF0; // -16
        mliu_req.operand2 = '0;
        mliu_req.rd_addr = 5'd5;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU RELU (-16) Result: %h, Error: %b (Expected: 00000000)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_RELU;
        mliu_req.operand1 = 32'h0000000A; // 10
        mliu_req.operand2 = '0;
        mliu_req.rd_addr = 5'd5;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU RELU (10) Result: %h, Error: %b (Expected: 0000000A)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        // --- Test Scenario 6: MLIU_SIGMOID (Sigmoid Activation) ---
        $display("\n--- Test Scenario 6: MLIU_SIGMOID (Sigmoid Activation) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_SIGMOID;
        mliu_req.operand1 = 32'h00000001; // Example input
        mliu_req.operand2 = '0;
        mliu_req.rd_addr = 5'd6;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU SIGMOID (1) Result: %h, Error: %b (Expected: 00000001 for placeholder)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        // --- Test Scenario 7: MLIU_TANH (Tanh Activation) ---
        $display("\n--- Test Scenario 7: MLIU_TANH (Tanh Activation) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_TANH;
        mliu_req.operand1 = 32'hFFFFFFF0; // -16
        mliu_req.operand2 = '0;
        mliu_req.rd_addr = 5'd7;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU TANH (-16) Result: %h, Error: %b (Expected: FFFFFFFF for placeholder)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_TANH;
        mliu_req.operand1 = 32'h0000000A; // 10
        mliu_req.operand2 = '0;
        mliu_req.rd_addr = 5'd7;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU TANH (10) Result: %h, Error: %b (Expected: 00000001 for placeholder)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        // --- Test Scenario 8: MLIU_MAX_POOL (Max Pooling) ---
        $display("\n--- Test Scenario 8: MLIU_MAX_POOL (Max Pooling) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_MAX_POOL;
        mliu_req.operand1 = 32'h00000007; // 7
        mliu_req.operand2 = 32'h0000000C; // 12
        mliu_req.rd_addr = 5'd8;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU MAX_POOL (7, 12) Result: %h, Error: %b (Expected: 0000000C)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        // --- Test Scenario 9: MLIU_AVG_POOL (Average Pooling) ---
        $display("\n--- Test Scenario 9: MLIU_AVG_POOL (Average Pooling) ---");
        mliu_req.valid = 1;
        mliu_req.opcode = MLIU_AVG_POOL;
        mliu_req.operand1 = 32'h0000000A; // 10
        mliu_req.operand2 = 32'h00000004; // 4
        mliu_req.rd_addr = 5'd9;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU AVG_POOL (10, 4) Result: %h, Error: %b (Expected: 00000007)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        // --- Test Scenario 10: Unsupported Opcode ---
        $display("\n--- Test Scenario 10: Unsupported Opcode ---");
        mliu_req.valid = 1;
        mliu_req.opcode = 4'hF; // Invalid opcode
        mliu_req.operand1 = 32'h0;
        mliu_req.operand2 = 32'h0;
        mliu_req.rd_addr = 5'd10;

        #10;
        wait(mliu_req_ready);
        mliu_req.valid = 0;
        mliu_rsp_ready = 1;

        #10;
        wait(mliu_rsp.valid);
        $display("MLIU Unsupported Opcode Result: %h, Error: %b (Expected: Error=1)", mliu_rsp.data, mliu_rsp.error);
        mliu_rsp_ready = 0;
        #10;

        $display("\n--------------------------------------------------");
        $display("MLIU Testbench Finished");
        $display("--------------------------------------------------");
        $finish;
    end

endmodule : mliu_tb
