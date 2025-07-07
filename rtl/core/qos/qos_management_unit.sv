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
//   Manages Quality of Service (QoS) configurations and monitors for violations.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module qos_management_unit (
    input  logic        clk_i,
    input  logic        rst_ni,

    input  qos_config_t core_qos_config_i,
    input  logic        qos_enable_i,
    input  logic        exception_pending_i,
    input  logic        debug_access_pending_i,
    input  logic        mem_req_valid_i,
    input  logic        mem_req_ready_i,

    output qos_config_t instr_qos_config_o,
    output qos_config_t data_qos_config_o,
    output logic [31:0] qos_violations_o
);

    qos_config_t instr_qos_config;
    qos_config_t data_qos_config;
    logic [31:0] qos_violation_counter;

    logic critical_access_pending;

    assign critical_access_pending = exception_pending_i || debug_access_pending_i;

    // AI_TAG: INTERNAL_LOGIC - Determine QoS configuration for instruction fetches
    function automatic qos_config_t get_instruction_qos_config(
        input qos_config_t base_config,
        input logic critical_access
    );
        qos_config_t qos_config;
        qos_config = base_config;
        if (critical_access) begin
            qos_config.qos_level = QOS_LEVEL_CRITICAL;
            qos_config.urgent = 1'b1;
        end
        return qos_config;
    endfunction

    // AI_TAG: INTERNAL_LOGIC - Determine QoS configuration for data accesses
    function automatic qos_config_t get_data_qos_config(
        input qos_config_t base_config,
        input logic critical_access
    );
        qos_config_t qos_config;
        qos_config = base_config;
        if (critical_access) begin
            qos_config.qos_level = QOS_LEVEL_CRITICAL;
            qos_config.urgent = 1'b1;
        end
        return qos_config;
    endfunction

    // Assign QoS configurations
    assign instr_qos_config = get_instruction_qos_config(core_qos_config_i, critical_access);
    assign data_qos_config = get_data_qos_config(core_qos_config_i, critical_access);

    assign instr_qos_config_o = instr_qos_config;
    assign data_qos_config_o = data_qos_config;

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
