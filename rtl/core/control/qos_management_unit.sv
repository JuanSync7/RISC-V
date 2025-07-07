//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: qos_management_unit.sv
// Module: qos_management_unit
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   This module handles Quality of Service (QoS) configuration and violation
//   monitoring for the RISC-V core. It provides functions to generate QoS
//   configurations for instruction and data accesses and tracks QoS violations.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_qos_pkg::*;

module qos_management_unit #(
    parameter integer CORE_ID = 0
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    input  logic        qos_enable_i,          // Global QoS enable
    input  logic        exception_pending_i,   // Indicates if an exception is pending
    input  logic        debug_access_pending_i, // Indicates if a debug access is pending
    input  logic        mem_req_valid_i,       // Memory request valid from arbitration
    input  logic        mem_req_ready_i,       // Memory request ready from external memory

    output qos_config_t instr_qos_config_o,    // QoS config for instruction fetches
    output qos_config_t data_qos_config_o,     // QoS config for data accesses
    output logic [31:0] qos_violations_o       // QoS violations counter
);

    logic critical_access_pending;
    logic [31:0] qos_violation_counter;

    assign critical_access_pending = exception_pending_i || debug_access_pending_i;

    // Generate QoS configuration for instruction fetches
    function automatic qos_config_t get_instruction_qos_config();
        qos_config_t qos_config;
        
        qos_config.qos_level = exception_pending_i ? QOS_LEVEL_CRITICAL : QOS_LEVEL_HIGH;
        qos_config.transaction_type = QOS_TYPE_INSTR_FETCH;
        qos_config.urgent = exception_pending_i;
        qos_config.guaranteed_bw = 1'b1;
        qos_config.weight = exception_pending_i ? QOS_WEIGHT_CRITICAL : QOS_WEIGHT_HIGH;
        qos_config.max_latency_cycles = exception_pending_i ? QOS_INSTR_LATENCY_CRITICAL : QOS_INSTR_LATENCY_NORMAL;
        qos_config.bandwidth_percent = QOS_INSTR_BW_PERCENT;
        qos_config.core_id = CORE_ID[3:0];
        qos_config.preemptable = ~exception_pending_i;
        qos_config.real_time = exception_pending_i;
        qos_config.retry_limit = QOS_INSTR_RETRY_LIMIT;
        qos_config.ordered = 1'b1;
        
        return qos_config;
    endfunction
    
    // Generate QoS configuration for data accesses
    function automatic qos_config_t get_data_qos_config(
        input logic is_store,
        input logic is_critical
    );
        qos_config_t qos_config;
        
        if (is_critical || exception_pending_i) begin
            qos_config.qos_level = QOS_LEVEL_CRITICAL;
            qos_config.weight = QOS_WEIGHT_CRITICAL;
            qos_config.max_latency_cycles = CONFIG_QOS_DATA_LATENCY_CRITICAL;
            qos_config.urgent = 1'b1;
            qos_config.real_time = 1'b1;
            qos_config.preemptable = 1'b0;
        end else begin
            qos_config.qos_level = is_store ? QOS_LEVEL_MEDIUM : QOS_LEVEL_MEDIUM_HIGH;
            qos_config.weight = is_store ? QOS_WEIGHT_MEDIUM : QOS_WEIGHT_MEDIUM_HIGH;
            qos_config.max_latency_cycles = is_store ? CONFIG_QOS_DATA_STORE_LATENCY_NORMAL : CONFIG_QOS_DATA_LOAD_LATENCY_NORMAL;
            qos_config.urgent = 1'b0;
            qos_config.real_time = 1'b0;
            qos_config.preemptable = 1'b1;
        end
        
        qos_config.transaction_type = QOS_TYPE_DATA_ACCESS;
        qos_config.guaranteed_bw = is_critical || exception_pending_i;
        qos_config.bandwidth_percent = CONFIG_QOS_DATA_BW_PERCENT;
        qos_config.core_id = CORE_ID[3:0];
        qos_config.retry_limit = QOS_DATA_RETRY_LIMIT;
        qos_config.ordered = 1'b1;
        
        return qos_config;
    endfunction
    
    // QoS configuration assignment
    always_comb begin : proc_qos_config_assignment
        instr_qos_config_o = get_instruction_qos_config();
        data_qos_config_o = get_data_qos_config(1'b0, critical_access_pending); // Default to load config
    end
    
    // QoS Violation Monitoring
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_qos_monitoring
        if (!rst_ni) begin
            qos_violation_counter <= 0;
        end else begin
            // Monitor for QoS violations
            if (mem_req_valid_i && !mem_req_ready_i && qos_enable_i) begin
                // Memory not ready when we have a request - potential violation
                qos_violation_counter <= qos_violation_counter + 1;
            end
            
            // Additional violation monitoring can be added here
            // e.g., latency deadline misses, bandwidth violations
        end
    end
    
    assign qos_violations_o = qos_violation_counter;

endmodule : qos_management_unit

`default_nettype wire