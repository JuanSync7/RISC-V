//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: multi_core_management.sv
// Module: multi_core_management
//
// Project Name: RISC-V RV32IM Core
//
// Description:
//   Handles system-level control, configuration, and coordination.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;


module multi_core_management #(
    parameter integer NUM_CORES = DEFAULT_NUM_CORES,
    parameter integer L2_CACHE_SIZE = DEFAULT_L2_CACHE_SIZE,
    parameter integer L3_CACHE_SIZE = DEFAULT_L3_CACHE_SIZE,
    parameter integer MSG_WIDTH = DEFAULT_MSG_WIDTH,
    parameter integer NUM_BARRIERS = DEFAULT_NUM_BARRIERS
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    // System Configuration
    input  logic [31:0] sys_config_i,
    output logic [31:0] sys_status_o,

    // External Memory Interfaces
    inout axi4_if.master axi4_if,
    inout chi_if.rn chi_if,
    inout tilelink_if.master tl_if,

    // Performance Inputs for System Controller
    input  logic [31:0] current_ipc_calculated,
    input  logic [7:0]  cache_hit_rate_l1,
    input  logic        any_core_active,
    input  logic        pipeline_bottleneck,
    input  logic        high_power_mode,
    input  logic        good_bp,

    // Core Status
    input  logic [NUM_CORES-1:0] core_active_i,

    // Communication Interfaces
    inout inter_core_comm_if comm_if,
    inout sync_primitives_if sync_if,

    // Output
    output system_cache_topology_t cache_topology_config
);

    //-------------------------------------------------------------------------
    // Cache Topology Configuration
    //-------------------------------------------------------------------------
    always_comb begin
        case (NUM_CORES)
            1, 2: begin
                cache_topology_config = get_unified_topology(NUM_CORES, L2_CACHE_SIZE, L3_CACHE_SIZE);
            end
            3, 4: begin
                if (DEFAULT_CACHE_TOPOLOGY == "CLUSTERED") begin
                    cache_topology_config = get_clustered_topology(NUM_CORES, L2_CACHE_SIZE, L3_CACHE_SIZE);
                end else begin
                    cache_topology_config = get_unified_topology(NUM_CORES, L2_CACHE_SIZE, L3_CACHE_SIZE);
                end
            end
            default: begin
                if (DEFAULT_CACHE_TOPOLOGY == "NUMA") begin
                    cache_topology_config = get_numa_topology(NUM_CORES, L2_CACHE_SIZE, L3_CACHE_SIZE);
                end else begin
                    cache_topology_config = get_clustered_topology(NUM_CORES, L2_CACHE_SIZE, L3_CACHE_SIZE);
                end
            end
        endcase

        if (!ENABLE_L2_CACHE) begin
            cache_topology_config.num_l2_instances = 0;
            for (int i = 0; i < MAX_L2_INSTANCES; i++) begin
                cache_topology_config.clusters[i].num_l2_instances = 0;
            end
        end
        if (!ENABLE_L3_CACHE) begin
            cache_topology_config.num_l3_instances = 0;
        end
    end

    //-------------------------------------------------------------------------
    // System Controller
    //-------------------------------------------------------------------------
    system_controller #(
        .NUM_CORES(NUM_CORES)
    ) u_system_controller (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .sys_config_i(sys_config_i),
        .sys_status_o(sys_status_o),
        .axi4_if(axi4_if),
        .chi_if(chi_if),
        .tl_if(tl_if),
        .current_ipc_calculated_i(current_ipc_calculated),
        .cache_hit_rate_l1_i(cache_hit_rate_l1),
        .any_core_active_i(any_core_active),
        .pipeline_bottleneck_i(pipeline_bottleneck),
        .high_power_mode_i(high_power_mode),
        .good_bp_i(good_bp)
    );

    //-------------------------------------------------------------------------
    // Inter-Core Communication Network Manager
    //-------------------------------------------------------------------------
    core_manager #(
        .NUM_CORES(NUM_CORES),
        .CORE_ID_WIDTH($clog2(NUM_CORES))
    ) u_core_manager (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        .core_active_i(core_active_i),
        .core_ready_o(/* internal status */),
        
        .comm_if(comm_if),
        .sync_if(sync_if)
    );

endmodule : multi_core_management 