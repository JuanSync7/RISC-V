//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: multi_core_interconnect.sv
// Module: multi_core_interconnect
//
// Project Name: RISC-V RV32IM Core
//
// Description:
//   Manages interfaces and routing for the multi-core system.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;


module multi_core_interconnect #(
    parameter integer NUM_CORES = DEFAULT_NUM_CORES,
    parameter string DEFAULT_PROTOCOL = DEFAULT_MEMORY_PROTOCOL,
    parameter integer MAX_OUTSTANDING = DEFAULT_AXI4_MAX_OUTSTANDING,
    parameter integer MSG_WIDTH = DEFAULT_MSG_WIDTH,
    parameter integer NUM_BARRIERS = DEFAULT_NUM_BARRIERS
) (
    input  logic clk_i,
    input  logic rst_ni,

    // System Config
    input  logic [31:0] sys_config_i,

    // Core-facing interfaces
    input memory_req_rsp_if l1_icache_if [NUM_CORES],
    input memory_req_rsp_if l1_dcache_if [NUM_CORES],

    // Memory-facing interface (output to cluster)
    output memory_req_rsp_if mem_controller_if [MAX_MEMORY_CONTROLLERS],

    // External protocol interfaces
    inout axi4_if.master axi4_if,
    inout chi_if.rn chi_if,
    inout tilelink_if.master tl_if,
    
    // Coherency and communication interfaces
    inout cache_coherency_if coherency_if,
    inout inter_core_comm_if inter_core_if,
    inout sync_primitives_if sync_if
);

    // Protocol factory interface
    memory_req_rsp_if protocol_generic_if (
        .clk(clk_i),
        .rst_n(rst_ni)
    );

    //-------------------------------------------------------------------------
    // Memory Controller Interface Routing
    //-------------------------------------------------------------------------
    generate
        for (genvar mc_id = 0; mc_id < MAX_MEMORY_CONTROLLERS; mc_id++) begin : gen_memory_controller_routing
            if (mc_id == 0) begin : gen_primary_memory_controller
                // Primary memory controller always gets routed to protocol factory
                assign protocol_generic_if.req_valid = mem_controller_if[mc_id].req_valid;
                assign protocol_generic_if.req = mem_controller_if[mc_id].req;
                assign mem_controller_if[mc_id].req_ready = protocol_generic_if.req_ready;
                assign mem_controller_if[mc_id].rsp_valid = protocol_generic_if.rsp_valid;
                assign mem_controller_if[mc_id].rsp = protocol_generic_if.rsp;
                assign protocol_generic_if.rsp_ready = mem_controller_if[mc_id].rsp_ready;
            end else begin : gen_secondary_memory_controllers
                // Tie off unused secondary controllers
                assign mem_controller_if[mc_id].req_ready = 1'b0;
                assign mem_controller_if[mc_id].rsp_valid = 1'b0;
                assign mem_controller_if[mc_id].rsp = '0;
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Protocol Factory
    //-------------------------------------------------------------------------
    protocol_factory #(
        .DEFAULT_PROTOCOL(DEFAULT_PROTOCOL),
        .ADDR_WIDTH(riscv_core_types_pkg::ADDR_WIDTH),
        .DATA_WIDTH(riscv_core_types_pkg::XLEN),
        .ID_WIDTH(riscv_protocol_types_pkg::AXI4_ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING)
    ) u_protocol_factory (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        .config_reg_i(sys_config_i),
        .status_reg_o(),
        
        .generic_if(protocol_generic_if),
        
        .axi4_if(axi4_if),
        .chi_if(chi_if),
        .tl_if(tl_if),
        
        .protocol_transactions_o(),
        .protocol_latency_avg_o(),
        .protocol_bandwidth_o()
    );

endmodule : multi_core_interconnect 