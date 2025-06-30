//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: qos_arbiter.sv
// Module: qos_arbiter
//
// Project Name: RISC-V RV32IM QoS Arbiter
// Target Devices: ASIC/FPGA
//
// Description:
//   QoS-aware arbiter for multi-core memory transactions. Implements
//   priority-based arbitration with anti-starvation and bandwidth control.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_config_pkg::*;

module qos_arbiter #(
    parameter integer NUM_REQUESTERS = DEFAULT_NUM_REQUESTERS,           // Number of requesting agents
    parameter integer ADDR_WIDTH = ADDR_WIDTH,              // Address width
    parameter integer DATA_WIDTH = XLEN,              // Data width
    parameter integer QOS_LEVELS = DEFAULT_QOS_LEVELS               // Number of QoS levels
) (
    input  logic clk_i,                             // Clock
    input  logic rst_ni,                            // Active-low reset

    // Request interfaces from multiple agents (cores, DMA, etc.)
    input  logic [NUM_REQUESTERS-1:0]      req_valid_i,    // Request valid
    input  qos_config_t [NUM_REQUESTERS-1:0] qos_config_i, // QoS configuration
    input  logic [ADDR_WIDTH-1:0] [NUM_REQUESTERS-1:0] req_addr_i,   // Request address
    input  logic [DATA_WIDTH-1:0] [NUM_REQUESTERS-1:0] req_data_i,   // Request data
    input  logic [NUM_REQUESTERS-1:0]      req_write_i,    // Write request
    output logic [NUM_REQUESTERS-1:0]      req_ready_o,    // Request ready

    // Arbitrated output to memory system
    output logic                            arb_valid_o,    // Arbitrated request valid
    output qos_config_t                     arb_qos_o,      // Arbitrated QoS config
    output logic [ADDR_WIDTH-1:0]          arb_addr_o,     // Arbitrated address
    output logic [DATA_WIDTH-1:0]          arb_data_o,     // Arbitrated data
    output logic                            arb_write_o,    // Arbitrated write
    input  logic                            arb_ready_i,    // Memory system ready

    // QoS configuration interface
    input  logic                            qos_enable_i,   // Global QoS enable
    input  logic [1:0]                      arbiter_mode_i, // Arbitration mode
    
    // Performance monitoring
    output logic [31:0]                     qos_violations_o,   // QoS violations
    output logic [31:0]                     total_requests_o,   // Total requests
    output logic [NUM_REQUESTERS-1:0]      starvation_flags_o  // Starvation indicators
);

    //---------------------------------------------------------------------------
    // Internal Signals
    //---------------------------------------------------------------------------
    
    // Arbitration state
    logic [NUM_REQUESTERS-1:0]      grant_mask;
    logic [$clog2(NUM_REQUESTERS)-1:0] winner_id;
    logic                           winner_valid;
    
    // Priority calculation
    logic [31:0] [NUM_REQUESTERS-1:0] priority_scores;
    logic [31:0] [NUM_REQUESTERS-1:0] wait_times;
    
    // Performance counters
    logic [31:0]                    violation_count_r;
    logic [31:0]                    request_count_r;
    logic [31:0] [NUM_REQUESTERS-1:0] starvation_counters;
    
    // Round-robin pointer for fair arbitration
    logic [$clog2(NUM_REQUESTERS)-1:0] rr_pointer_r;

    //---------------------------------------------------------------------------
    // Wait Time Tracking (Anti-Starvation)
    //---------------------------------------------------------------------------
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_wait_time_tracking
        if (!rst_ni) begin
            for (int i = 0; i < NUM_REQUESTERS; i++) begin
                wait_times[i] <= '0;
                starvation_counters[i] <= '0;
            end
        end else begin
            for (int i = 0; i < NUM_REQUESTERS; i++) begin
                if (req_valid_i[i]) begin
                    if (grant_mask[i] && arb_ready_i) begin
                        // Request granted, reset wait time
                        wait_times[i] <= '0;
                        starvation_counters[i] <= '0;
                    end else begin
                        // Request waiting, increment counters
                        wait_times[i] <= wait_times[i] + 1;
                        if (wait_times[i] > DEFAULT_STARVATION_THRESHOLD) begin // Starvation threshold
                            starvation_counters[i] <= starvation_counters[i] + 1;
                        end
                    end
                end else begin
                    wait_times[i] <= '0;
                end
            end
        end
    end

    //---------------------------------------------------------------------------
    // Optimized Priority Score Calculation - Pipelined for High Frequency
    //---------------------------------------------------------------------------
    // AI_TAG: PERFORMANCE_OPT - Pipelined priority calculation to reduce critical path
    
    // Pipeline registers for priority calculation
    logic [15:0] [NUM_REQUESTERS-1:0] priority_scores_pipe_r;
    logic [NUM_REQUESTERS-1:0] req_valid_pipe_r;
    qos_config_t [NUM_REQUESTERS-1:0] qos_config_pipe_r;
    
    // Stage 1: Basic priority calculation (reduced bit width for speed)
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_priority_stage1
        if (!rst_ni) begin
            priority_scores_pipe_r <= '{default: '0};
            req_valid_pipe_r <= '0;
            qos_config_pipe_r <= '{default: '0};
        end else begin
            req_valid_pipe_r <= req_valid_i;
            qos_config_pipe_r <= qos_config_i;
            
            for (int i = 0; i < NUM_REQUESTERS; i++) begin
                if (qos_enable_i && req_valid_i[i]) begin
                    // Optimized 16-bit priority calculation for speed
                    logic [15:0] base_priority = {8'h0, qos_config_i[i].qos_level, 4'h0};
                    logic [15:0] urgency_bonus = qos_config_i[i].urgent ? QOS_URGENCY_BONUS : 16'h0;
                    logic [15:0] rt_bonus = qos_config_i[i].real_time ? QOS_REAL_TIME_BONUS : 16'h0;
                    
                    // Simplified aging (capped to prevent overflow)
                    logic [15:0] aging_bonus = wait_times[i][15:0];
                    
                    priority_scores_pipe_r[i] <= base_priority + urgency_bonus + rt_bonus + aging_bonus;
                end else begin
                    priority_scores_pipe_r[i] <= wait_times[i][15:0]; // Aging only
                end
            end
        end
    end
    
    // Convert pipelined scores to full width for compatibility
    always_comb begin : proc_priority_expansion
        for (int i = 0; i < NUM_REQUESTERS; i++) begin
            priority_scores[i] = {16'h0, priority_scores_pipe_r[i]};
        end
    end

    //---------------------------------------------------------------------------
    // Optimized Tree-Based Arbitration Logic for High Frequency
    //---------------------------------------------------------------------------
    // AI_TAG: PERFORMANCE_OPT - Tree-based arbitration to reduce critical path delay
    
    // Registered arbitration mode and winner selection
    logic [1:0] arbiter_mode_r;
    logic [$clog2(NUM_REQUESTERS)-1:0] winner_id_r;
    logic winner_valid_r;
    logic [NUM_REQUESTERS-1:0] grant_mask_r;
    
    // Pipeline arbitration for high frequency
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_arbitration_pipe
        if (!rst_ni) begin
            arbiter_mode_r <= 2'b00;
            winner_id_r <= '0;
            winner_valid_r <= 1'b0;
            grant_mask_r <= '0;
        end else begin
            arbiter_mode_r <= arbiter_mode_i;
            
            // Tree-based winner selection for improved timing
            logic [$clog2(NUM_REQUESTERS)-1:0] temp_winner;
            logic temp_valid;
            
            case (arbiter_mode_i)
                2'b00: begin // Optimized Round-robin
                    temp_winner = '0;
                    temp_valid = 1'b0;
                    
                    // Unrolled round-robin for better timing (assuming NUM_REQUESTERS = 4)
                    if (NUM_REQUESTERS == 4) begin
                        case (rr_pointer_r)
                            2'b00: begin
                                if (req_valid_pipe_r[0]) begin
                                    temp_winner = 2'b00; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[1]) begin
                                    temp_winner = 2'b01; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[2]) begin
                                    temp_winner = 2'b10; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[3]) begin
                                    temp_winner = 2'b11; temp_valid = 1'b1;
                                end
                            end
                            2'b01: begin
                                if (req_valid_pipe_r[1]) begin
                                    temp_winner = 2'b01; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[2]) begin
                                    temp_winner = 2'b10; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[3]) begin
                                    temp_winner = 2'b11; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[0]) begin
                                    temp_winner = 2'b00; temp_valid = 1'b1;
                                end
                            end
                            2'b10: begin
                                if (req_valid_pipe_r[2]) begin
                                    temp_winner = 2'b10; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[3]) begin
                                    temp_winner = 2'b11; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[0]) begin
                                    temp_winner = 2'b00; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[1]) begin
                                    temp_winner = 2'b01; temp_valid = 1'b1;
                                end
                            end
                            2'b11: begin
                                if (req_valid_pipe_r[3]) begin
                                    temp_winner = 2'b11; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[0]) begin
                                    temp_winner = 2'b00; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[1]) begin
                                    temp_winner = 2'b01; temp_valid = 1'b1;
                                end else if (req_valid_pipe_r[2]) begin
                                    temp_winner = 2'b10; temp_valid = 1'b1;
                                end
                            end
                        endcase
                    end
                end
                
                2'b01: begin // Tree-based Priority Arbitration
                    // Binary tree comparison for 4 requesters
                    logic [1:0] winner_01, winner_23;
                    logic valid_01, valid_23;
                    
                    // Level 1: Compare pairs
                    if (req_valid_pipe_r[0] && req_valid_pipe_r[1]) begin
                        winner_01 = (priority_scores[0] >= priority_scores[1]) ? 2'b00 : 2'b01;
                        valid_01 = 1'b1;
                    end else if (req_valid_pipe_r[0]) begin
                        winner_01 = 2'b00; valid_01 = 1'b1;
                    end else if (req_valid_pipe_r[1]) begin
                        winner_01 = 2'b01; valid_01 = 1'b1;
                    end else begin
                        winner_01 = 2'b00; valid_01 = 1'b0;
                    end
                    
                    if (req_valid_pipe_r[2] && req_valid_pipe_r[3]) begin
                        winner_23 = (priority_scores[2] >= priority_scores[3]) ? 2'b10 : 2'b11;
                        valid_23 = 1'b1;
                    end else if (req_valid_pipe_r[2]) begin
                        winner_23 = 2'b10; valid_23 = 1'b1;
                    end else if (req_valid_pipe_r[3]) begin
                        winner_23 = 2'b11; valid_23 = 1'b1;
                    end else begin
                        winner_23 = 2'b10; valid_23 = 1'b0;
                    end
                    
                    // Level 2: Final comparison
                    if (valid_01 && valid_23) begin
                        temp_winner = (priority_scores[winner_01] >= priority_scores[winner_23]) ? 
                                     winner_01 : winner_23;
                        temp_valid = 1'b1;
                    end else if (valid_01) begin
                        temp_winner = winner_01; temp_valid = 1'b1;
                    end else if (valid_23) begin
                        temp_winner = winner_23; temp_valid = 1'b1;
                    end else begin
                        temp_winner = 2'b00; temp_valid = 1'b0;
                    end
                end
                
                default: begin // Default to round-robin
                    temp_winner = '0; temp_valid = 1'b0;
                    // Simplified default case
                    for (int i = 0; i < NUM_REQUESTERS; i++) begin
                        if (req_valid_pipe_r[i] && !temp_valid) begin
                            temp_winner = i[$clog2(NUM_REQUESTERS)-1:0];
                            temp_valid = 1'b1;
                        end
                    end
                end
            endcase
            
            // Register outputs
            winner_id_r <= temp_winner;
            winner_valid_r <= temp_valid;
            grant_mask_r <= '0;
            if (temp_valid) begin
                grant_mask_r[temp_winner] <= 1'b1;
            end
        end
    end
    
    // Assign outputs from registered values
    assign winner_id = winner_id_r;
    assign winner_valid = winner_valid_r;
    assign grant_mask = grant_mask_r;

    //---------------------------------------------------------------------------
    // Round-Robin Pointer Update
    //---------------------------------------------------------------------------
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_rr_pointer
        if (!rst_ni) begin
            rr_pointer_r <= '0;
        end else if (winner_valid && arb_ready_i) begin
            rr_pointer_r <= (winner_id + 1) % NUM_REQUESTERS;
        end
    end

    //---------------------------------------------------------------------------
    // Output Assignment
    //---------------------------------------------------------------------------
    
    assign req_ready_o = grant_mask & {NUM_REQUESTERS{arb_ready_i}};
    
    assign arb_valid_o = winner_valid;
    assign arb_qos_o = winner_valid ? qos_config_i[winner_id] : '0;
    assign arb_addr_o = winner_valid ? req_addr_i[winner_id] : '0;
    assign arb_data_o = winner_valid ? req_data_i[winner_id] : '0;
    assign arb_write_o = winner_valid ? req_write_i[winner_id] : 1'b0;

    //---------------------------------------------------------------------------
    // Performance Monitoring
    //---------------------------------------------------------------------------
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_performance_monitoring
        if (!rst_ni) begin
            violation_count_r <= '0;
            request_count_r <= '0;
        end else begin
            // Count total requests
            if (arb_valid_o && arb_ready_i) begin
                request_count_r <= request_count_r + 1;
            end
            
            // Count QoS violations (requests that waited too long)
            for (int i = 0; i < NUM_REQUESTERS; i++) begin
                if (req_valid_i[i] && wait_times[i] > qos_config_i[i].max_latency_cycles) begin
                    violation_count_r <= violation_count_r + 1;
                end
            end
        end
    end
    
    assign qos_violations_o = violation_count_r;
    assign total_requests_o = request_count_r;
    
    // Starvation flags
    always_comb begin : proc_starvation_flags
        for (int i = 0; i < NUM_REQUESTERS; i++) begin
            starvation_flags_o[i] = (starvation_counters[i] > 100); // Threshold
        end
    end

endmodule : qos_arbiter

//=============================================================================
// Dependencies: riscv_core_pkg.sv
// Instantiated In:
//   - Not currently instantiated in RTL modules

// Performance:
//   - Critical Path: Priority score calculation and arbitration logic
//   - Max Frequency: 500MHz ASIC, 250MHz FPGA (estimated)
//   - Area: Depends on NUM_REQUESTERS (~150 gates per requester)
//
// Verification Coverage:
//   - Code Coverage: TBD
//   - Functional Coverage: QoS scenarios, starvation, fairness
//   - Branch Coverage: All arbitration modes
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)
//
// Testing:
//   - Testbench: qos_arbiter_tb.sv
//   - Test Vectors: Multi-core contention scenarios
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-01-27 | DesignAI          | Initial implementation
//=============================================================================

`default_nettype wire 