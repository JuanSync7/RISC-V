//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: memory_arbitration_unit.sv
// Module: memory_arbitration_unit
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Arbitrates between instruction and data cache memory requests based on QoS.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module memory_arbitration_unit (
    input  logic                clk_i,
    input  logic                rst_ni,

    // I-Cache Interface
    input  logic                icache_req_valid_i,
    input  memory_req_t         icache_req_i,
    output logic                icache_req_ready_o,
    input  logic                icache_rsp_valid_i,
    input  memory_rsp_t         icache_rsp_i,
    output logic                icache_rsp_ready_o,

    // D-Cache Interface
    input  logic                dcache_req_valid_i,
    input  memory_req_t         dcache_req_i,
    output logic                dcache_req_ready_o,
    input  logic                dcache_rsp_valid_i,
    input  memory_rsp_t         dcache_rsp_i,
    output logic                dcache_rsp_ready_o,

    // QoS Inputs
    input  qos_config_t         instr_qos_config_i,
    input  qos_config_t         data_qos_config_i,
    input  logic                qos_enable_i,

    // Memory Interface to next level (e.g., L2 Cache or main memory)
    output logic                mem_req_valid_o,
    output memory_req_t         mem_req_o,
    output qos_config_t         mem_qos_config_o,
    input  logic                mem_req_ready_i,
    input  logic                mem_rsp_valid_i,
    input  memory_rsp_t         mem_rsp_i,
    output logic                mem_rsp_ready_o
);

    logic icache_req_pending;
    logic dcache_req_pending;
    logic priority_to_icache;

    assign icache_req_pending = icache_req_valid_i && qos_enable_i;
    assign dcache_req_pending = dcache_req_valid_i && qos_enable_i;

    // Arbitration between I-cache and D-cache based on QoS
    always_comb begin : proc_cache_arbitration
        priority_to_icache = 1'b0;
        
        if (icache_req_pending && dcache_req_pending) begin
            // Both caches have requests - arbitrate based on QoS
            if (instr_qos_config_i.qos_level > data_qos_config_i.qos_level) begin
                priority_to_icache = 1'b1;
            end else if (instr_qos_config_i.qos_level == data_qos_config_i.qos_level) begin
                // Same QoS level - prioritize based on urgency
                priority_to_icache = instr_qos_config_i.urgent && !data_qos_config_i.urgent;
            end
            // Otherwise, D-cache gets priority (default to data access)
        end else if (icache_req_pending) begin
            priority_to_icache = 1'b1;
        end
        // else D-cache gets priority or no requests
    end
    
    // Memory interface outputs for multi-core arbitration
    always_comb begin : proc_memory_interface_output
        if (qos_enable_i) begin
            if (priority_to_icache && icache_req_pending) begin
                // Forward I-cache request
                mem_req_valid_o = icache_req_valid_i;
                mem_req_o = icache_req_i;
                mem_qos_config_o = instr_qos_config_i;
                icache_req_ready_o = mem_req_ready_i;
                dcache_req_ready_o = 1'b0; // Block D-cache
            end else if (dcache_req_pending) begin
                // Forward D-cache request
                mem_req_valid_o = dcache_req_valid_i;
                mem_req_o = dcache_req_i;
                mem_qos_config_o = data_qos_config_i;
                dcache_req_ready_o = mem_req_ready_i;
                icache_req_ready_o = 1'b0; // Block I-cache
            end else begin
                // No requests or QoS disabled
                mem_req_valid_o = 1'b0;
                mem_req_o = '0;
                mem_qos_config_o = '0;
                icache_req_ready_o = 1'b1;
                dcache_req_ready_o = 1'b1;
            end
        end else begin
            // QoS disabled - simple passthrough to first available interface
            mem_req_valid_o = icache_req_valid_i || dcache_req_valid_i;
            mem_req_o = icache_req_valid_i ? icache_req_i : dcache_req_i;
            mem_qos_config_o = '0; // No specific QoS when disabled
            icache_req_ready_o = mem_req_ready_i && icache_req_valid_i;
            dcache_req_ready_o = mem_req_ready_i && !icache_req_valid_i;
        end
    end
    
    // Route responses back to appropriate cache based on transaction ID
    always_comb begin : proc_response_assignment
        if (mem_rsp_valid_i) begin
            // ID 0 is for I-cache, all others are for D-cache
            if (mem_rsp_i.id == 4'h0) begin
                icache_rsp_valid_o = 1'b1;
                icache_rsp_ready_o = icache_rsp_valid_i;
                dcache_rsp_valid_o = 1'b0;
                dcache_rsp_ready_o = 1'b0;
                mem_rsp_ready_o = icache_rsp_ready_o;
            end else begin
                dcache_rsp_valid_o = 1'b1;
                dcache_rsp_ready_o = dcache_rsp_valid_i;
                icache_rsp_valid_o = 1'b0;
                icache_rsp_ready_o = 1'b0;
                mem_rsp_ready_o = dcache_rsp_ready_o;
            end
        end else begin
            icache_rsp_valid_o = 1'b0;
            dcache_rsp_valid_o = 1'b0;
            icache_rsp_ready_o = 1'b1;
            dcache_rsp_ready_o = 1'b1;
            mem_rsp_ready_o = 1'b1;
        end
    end

endmodule : memory_arbitration_unit

`default_nettype wire
