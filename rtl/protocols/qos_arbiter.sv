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

import riscv_qos_pkg::*;
import riscv_config_pkg::*;
import riscv_types_pkg::*;

module qos_arbiter #(
    parameter integer NUM_REQUESTERS = 4,           // Number of requesting agents
    parameter integer ADDR_WIDTH = 32,              // Address width
    parameter integer DATA_WIDTH = 32,              // Data width
    parameter integer QOS_LEVELS = 16               // Number of QoS levels
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
                        if (wait_times[i] > 1000) begin // Starvation threshold
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
    // Priority Score Calculation
    //---------------------------------------------------------------------------
    
    always_comb begin : proc_priority_calculation
        for (int i = 0; i < NUM_REQUESTERS; i++) begin
            if (qos_enable_i && req_valid_i[i]) begin
                // Base priority from QoS level (higher QoS = higher priority)
                logic [31:0] base_priority = {24'h0, qos_config_i[i].qos_level, 4'h0};
                
                // Urgency bonus
                logic [31:0] urgency_bonus = qos_config_i[i].urgent ? 32'h1000 : 32'h0;
                
                // Anti-starvation aging (older requests get higher priority)
                logic [31:0] aging_bonus = wait_times[i] * qos_config_i[i].weight;
                
                // Real-time boost
                logic [31:0] rt_bonus = qos_config_i[i].real_time ? 32'h2000 : 32'h0;
                
                priority_scores[i] = base_priority + urgency_bonus + aging_bonus + rt_bonus;
            end else begin
                // No QoS or invalid request
                priority_scores[i] = wait_times[i]; // Only aging for fairness
            end
        end
    end

    //---------------------------------------------------------------------------
    // Arbitration Logic
    //---------------------------------------------------------------------------
    
    always_comb begin : proc_arbitration
        winner_id = '0;
        winner_valid = 1'b0;
        grant_mask = '0;
        
        case (arbiter_mode_i)
            2'b00: begin // Round-robin arbitration
                // Simple round-robin starting from rr_pointer_r
                for (int i = 0; i < NUM_REQUESTERS; i++) begin
                    int idx = (rr_pointer_r + i) % NUM_REQUESTERS;
                    if (req_valid_i[idx] && !winner_valid) begin
                        winner_id = idx[$clog2(NUM_REQUESTERS)-1:0];
                        winner_valid = 1'b1;
                        grant_mask[idx] = 1'b1;
                    end
                end
            end
            
            2'b01: begin // Strict priority arbitration
                // Highest QoS level wins
                logic [31:0] max_priority = '0;
                for (int i = 0; i < NUM_REQUESTERS; i++) begin
                    if (req_valid_i[i] && priority_scores[i] > max_priority) begin
                        max_priority = priority_scores[i];
                        winner_id = i[$clog2(NUM_REQUESTERS)-1:0];
                        winner_valid = 1'b1;
                    end
                end
                if (winner_valid) begin
                    grant_mask[winner_id] = 1'b1;
                end
            end
            
            2'b10: begin // Weighted round-robin with QoS
                // Priority-aware round-robin
                logic [31:0] best_score = '0;
                logic [$clog2(NUM_REQUESTERS)-1:0] best_candidate = '0;
                logic candidate_found = 1'b0;
                
                // Look for candidates starting from round-robin pointer
                for (int i = 0; i < NUM_REQUESTERS; i++) begin
                    int idx = (rr_pointer_r + i) % NUM_REQUESTERS;
                    if (req_valid_i[idx]) begin
                        if (!candidate_found || priority_scores[idx] > best_score) begin
                            best_score = priority_scores[idx];
                            best_candidate = idx[$clog2(NUM_REQUESTERS)-1:0];
                            candidate_found = 1'b1;
                        end
                    end
                end
                
                if (candidate_found) begin
                    winner_id = best_candidate;
                    winner_valid = 1'b1;
                    grant_mask[best_candidate] = 1'b1;
                end
            end
            
            default: begin // Fair arbitration (aging-based)
                logic [31:0] max_wait = '0;
                for (int i = 0; i < NUM_REQUESTERS; i++) begin
                    if (req_valid_i[i] && wait_times[i] > max_wait) begin
                        max_wait = wait_times[i];
                        winner_id = i[$clog2(NUM_REQUESTERS)-1:0];
                        winner_valid = 1'b1;
                    end
                end
                if (winner_valid) begin
                    grant_mask[winner_id] = 1'b1;
                end
            end
        endcase
    end

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

`default_nettype wire 