//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: vpu_tb.sv
// Module: vpu_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Initial Testbench
//
// Description:
//   Testbench for the vpu_unit module.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module vpu_tb;

    import riscv_core_pkg::*;
    import riscv_config_pkg::*;
    import riscv_vpu_types_pkg::*;

    // Clock and Reset
    logic clk;
    logic rst_n;

    // VPU Interface
    vpu_req_t  vpu_req;
    logic      vpu_req_ready;
    vpu_rsp_t  vpu_rsp;
    logic      vpu_rsp_ready;

    // Instantiate the VPU Unit
    vpu_unit #(
        .MAX_VECTOR_LENGTH(MAX_VECTOR_LENGTH)
    ) uut (
        .clk_i(clk),
        .rst_ni(rst_n),
        .vpu_req_i(vpu_req),
        .vpu_req_ready_o(vpu_req_ready),
        .vpu_rsp_o(vpu_rsp),
        .vpu_rsp_ready_i(vpu_rsp_ready)
    );

    // Clock Generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period (100MHz)
    end

    // Test Stimulus
    initial begin
        $display("\n--------------------------------------------------");
        $display("Starting VPU Testbench");
        $display("--------------------------------------------------");

        // Initialize signals
        rst_n = 0;
        vpu_req = '0;
        vpu_rsp_ready = 0;

        #10; // Wait for a bit
        rst_n = 1; // Release reset
        $display("Reset released.");

        // --- Test Scenario 1: VPU_ADD (Placeholder) ---
        $display("\n--- Test Scenario 1: VPU_ADD (Placeholder) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_ADD;
        vpu_req.vector_length = 4; // Example vector length
        vpu_req.operand1_vector = '{32'h00000001, 32'h00000002, 32'h00000003, 32'h00000004, default: '0};
        vpu_req.operand2_vector = '{32'h00000005, 32'h00000006, 32'h00000007, 32'h00000008, default: '0};

        #10; // Request cycle
        wait(vpu_req_ready); // Wait for VPU to accept request
        vpu_req.valid = 0; // De-assert request
        vpu_rsp_ready = 1; // Be ready to accept response

        #10; // Response cycle
        wait(vpu_rsp.valid); // Wait for VPU response
        $display("VPU ADD Result Vector: %p, Error: %b (Expected: {6, 8, 10, 12, 0, 0, 0, 0})", vpu_rsp.result_vector, vpu_rsp.error);
        vpu_rsp_ready = 0; // De-assert response ready
        #10;

        // --- Test Scenario 2: VPU_SUB (Vector Subtraction) ---
        $display("\n--- Test Scenario 2: VPU_SUB (Vector Subtraction) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_SUB;
        vpu_req.vector_length = 4;
        vpu_req.operand1_vector = '{32'h0000000A, 32'h0000000B, 32'h0000000C, 32'h0000000D, default: '0};
        vpu_req.operand2_vector = '{32'h00000001, 32'h00000002, 32'h00000003, 32'h00000004, default: '0};

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU SUB Result Vector: %p, Error: %b (Expected: {9, 9, 9, 9, 0, 0, 0, 0})", vpu_rsp.result_vector, vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 3: VPU_MUL (Vector Multiplication) ---
        $display("\n--- Test Scenario 3: VPU_MUL (Vector Multiplication) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_MUL;
        vpu_req.vector_length = 3;
        vpu_req.operand1_vector = '{32'h00000002, 32'h00000003, 32'h00000004, default: '0};
        vpu_req.operand2_vector = '{32'h00000005, 32'h00000006, 32'h00000007, default: '0};

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU MUL Result Vector: %p, Error: %b (Expected: {10, 18, 28, 0, 0, 0, 0, 0})", vpu_rsp.result_vector, vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 4: VPU_DIV (Vector Division) ---
        $display("\n--- Test Scenario 4: VPU_DIV (Vector Division) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_DIV;
        vpu_req.vector_length = 2;
        vpu_req.operand1_vector = '{32'h0000000A, 32'h0000000C, default: '0};
        vpu_req.operand2_vector = '{32'h00000002, 32'h00000003, default: '0};

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU DIV Result Vector: %p, Error: %b (Expected: {5, 4, 0, 0, 0, 0, 0, 0})", vpu_rsp.result_vector, vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 5: VPU_DIV (Division by Zero) ---
        $display("\n--- Test Scenario 5: VPU_DIV (Division by Zero) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_DIV;
        vpu_req.vector_length = 2;
        vpu_req.operand1_vector = '{32'h0000000A, 32'h0000000C, default: '0};
        vpu_req.operand2_vector = '{32'h00000002, 32'h00000000, default: '0};

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU DIV Result Vector: %p, Error: %b (Expected: Error=1)", vpu_rsp.result_vector, vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 6: VPU_STORE (Store Vector to Memory) ---
        $display("\n--- Test Scenario 6: VPU_STORE (Store Vector to Memory) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_STORE;
        vpu_req.vector_length = 4;
        vpu_req.addr = 32'h100; // Store at address 0x100
        vpu_req.operand1_vector = '{32'hAA, 32'hBB, 32'hCC, 32'hDD, default: '0};

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid); // Wait for VPU to complete store operation
        $display("VPU STORE completed. Error: %b (Expected: 0)", vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 7: VPU_LOAD (Load Vector from Memory) ---
        $display("\n--- Test Scenario 7: VPU_LOAD (Load Vector from Memory) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_LOAD;
        vpu_req.vector_length = 4;
        vpu_req.addr = 32'h100; // Load from address 0x100

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU LOAD Result Vector: %p, Error: %b (Expected: {AA, BB, CC, DD, 0, 0, 0, 0})", vpu_rsp.result_vector, vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 7: VPU_LOAD (Load Vector from Memory) ---
        $display("\n--- Test Scenario 7: VPU_LOAD (Load Vector from Memory) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_LOAD;
        vpu_req.vector_length = 4;
        vpu_req.addr = 32'h100; // Load from address 0x100

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU LOAD Result Vector: %p, Error: %b (Expected: {AA, BB, CC, DD, 0, 0, 0, 0})", vpu_rsp.result_vector, vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 8: VPU_REDUCE_SUM (Sum of Vector Elements) ---
        $display("\n--- Test Scenario 8: VPU_REDUCE_SUM (Sum of Vector Elements) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_REDUCE_SUM;
        vpu_req.vector_length = 4;
        vpu_req.operand1_vector = '{32'h1, 32'h2, 32'h3, 32'h4, default: '0};

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU REDUCE_SUM Result: %h, Error: %b (Expected: 0000000A)", vpu_rsp.result_vector[0], vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 9: VPU_REDUCE_MIN (Minimum of Vector Elements) ---
        $display("\n--- Test Scenario 9: VPU_REDUCE_MIN (Minimum of Vector Elements) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_REDUCE_MIN;
        vpu_req.vector_length = 5;
        vpu_req.operand1_vector = '{32'h5, 32'h2, 32'h8, 32'h1, 32'h9, default: '0};

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU REDUCE_MIN Result: %h, Error: %b (Expected: 00000001)", vpu_rsp.result_vector[0], vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 10: VPU_REDUCE_MAX (Maximum of Vector Elements) ---
        $display("\n--- Test Scenario 10: VPU_REDUCE_MAX (Maximum of Vector Elements) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_REDUCE_MAX;
        vpu_req.vector_length = 3;
        vpu_req.operand1_vector = '{32'h10, 32'h5, 32'h15, default: '0};

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU REDUCE_MAX Result: %h, Error: %b (Expected: 0000000F)", vpu_rsp.result_vector[0], vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 11: VPU_PERMUTE (Vector Permutation) ---
        $display("\n--- Test Scenario 11: VPU_PERMUTE (Vector Permutation) ---");
        vpu_req.valid = 1;
        vpu_req.opcode = VPU_PERMUTE;
        vpu_req.vector_length = 4;
        vpu_req.operand1_vector = '{32'hAA, 32'hBB, 32'hCC, 32'hDD, default: '0}; // Data to permute
        vpu_req.operand2_vector = '{32'h3, 32'h1, 32'h0, 32'h2, default: '0}; // Permutation indices

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU PERMUTE Result Vector: %p, Error: %b (Expected: {DD, BB, AA, CC, 0, 0, 0, 0})", vpu_rsp.result_vector, vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        // --- Test Scenario 12: Unsupported Opcode ---
        $display("\n--- Test Scenario 12: Unsupported Opcode ---");
        vpu_req.valid = 1;
        vpu_req.opcode = 4'hF; // Invalid opcode
        vpu_req.vector_length = 1;
        vpu_req.operand1_vector = '{32'h1, default: '0};
        vpu_req.operand2_vector = '{32'h1, default: '0};

        #10;
        wait(vpu_req_ready);
        vpu_req.valid = 0;
        vpu_rsp_ready = 1;

        #10;
        wait(vpu_rsp.valid);
        $display("VPU Unsupported Opcode Result: %p, Error: %b (Expected: 1)", vpu_rsp.result_vector, vpu_rsp.error);
        vpu_rsp_ready = 0;
        #10;

        $display("\n--------------------------------------------------");
        $display("VPU Testbench Finished");
        $display("--------------------------------------------------");
        $finish;
    end

endmodule : vpu_tb
