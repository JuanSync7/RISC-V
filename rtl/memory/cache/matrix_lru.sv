//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: matrix_lru.sv
// Module: matrix_lru
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
//
// Description:
//   Implements a true LRU policy for an N-way set-associative cache using an
//   (N*(N-1))/2 bit matrix. This is a generic, reusable LRU module.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module matrix_lru #(
    parameter integer NUM_WAYS = 8,
    localparam WAY_BITS  = $clog2(NUM_WAYS),
    localparam LRU_WIDTH = (NUM_WAYS * (NUM_WAYS - 1)) / 2
) (
    input  logic clk_i,
    input  logic rst_ni,

    // AI_TAG: PORT_DESC - Update the LRU state
    input  logic                   update_en_i,
    // AI_TAG: PORT_DESC - The way that was accessed and is now the MRU
    input  logic [WAY_BITS-1:0]    update_way_i,

    // AI_TAG: PORT_DESC - The way that should be victimized
    output logic [WAY_BITS-1:0]    lru_way_o,
    // AI_TAG: PORT_DESC - The current LRU state bits for this set
    input  logic [LRU_WIDTH-1:0]   lru_state_i,
    // AI_TAG: PORT_DESC - The next LRU state bits after an update
    output logic [LRU_WIDTH-1:0]   lru_state_o
);
    logic [NUM_WAYS-1:0][NUM_WAYS-1:0] lru_matrix;
    integer k;

    always_comb begin
        // Decode flat LRU state vector into a matrix representation.
        // The matrix indicates priority: if matrix[i][j] is 1, then i was used more recently than j.
        k = 0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            for (int j = i + 1; j < NUM_WAYS; j++) begin
                lru_matrix[i][j] = lru_state_i[k];
                lru_matrix[j][i] = ~lru_state_i[k];
                k++;
            end
            lru_matrix[i][i] = 1'b0; // A way cannot be more recent than itself.
        end

        // Find victim: the way whose row is all zeros is the LRU.
        // This means it has not been used more recently than any other way.
        lru_way_o = '0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (|lru_matrix[i] == 1'b0) begin
                lru_way_o = i;
                break;
            end
        end

        // Calculate next state based on the update
        logic [NUM_WAYS-1:0][NUM_WAYS-1:0] next_lru_matrix;
        next_lru_matrix = lru_matrix;

        if (update_en_i) begin
            // To make update_way_i the MRU, set its row to all 1s.
            // This indicates it is more recent than all other ways.
            for (int i = 0; i < NUM_WAYS; i++) begin
                next_lru_matrix[update_way_i][i] = 1'b1;
            end
            
            // Set its column to all 0s.
            // This indicates all other ways are less recent than it.
            for (int i = 0; i < NUM_WAYS; i++) begin
                next_lru_matrix[i][update_way_i] = 1'b0;
            end
        end

        // Encode the matrix back into the flat state vector for storage.
        k = 0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            for (int j = i + 1; j < NUM_WAYS; j++) begin
                lru_state_o[k] = next_lru_matrix[i][j];
                k++;
            end
        end
    end
endmodule 

//=============================================================================
// Dependencies: None
// Instantiated In:
//   - memory/cache/l2_cache.sv

// Performance:
//   - Critical Path: Matrix calculation combinatorial logic
//   - Max Frequency: TBD
//   - Area: TBD

// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured

// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)

// Testing:
//   - Testbench: TBD
//   - Test Vectors: TBD
//   - Simulation Time: TBD

//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//============================================================================= 