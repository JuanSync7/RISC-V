//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: multi_core_cluster.sv
// Module: multi_core_cluster
//
// Project Name: RISC-V RV32IM Core
//
// Description:
//   Contains the core array and cache hierarchy.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_memory_config_pkg::*;

module multi_core_cluster #(
    parameter integer NUM_CORES = DEFAULT_NUM_CORES,
    parameter string EXECUTION_MODE = DEFAULT_EXECUTION_MODE,
    parameter string BRANCH_PREDICTOR_TYPE = DEFAULT_BRANCH_PREDICTOR_TYPE,
    parameter integer L1_ICACHE_SIZE = DEFAULT_L1_ICACHE_SIZE,
    parameter integer L1_DCACHE_SIZE = DEFAULT_L1_DCACHE_SIZE,
    parameter integer L2_CACHE_SIZE = DEFAULT_L2_CACHE_SIZE,
    parameter integer L3_CACHE_SIZE = DEFAULT_L3_CACHE_SIZE
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    // Memory interfaces
    output memory_req_rsp_if l1_icache_if [NUM_CORES],
    output memory_req_rsp_if l1_dcache_if [NUM_CORES],
    input memory_req_rsp_if mem_controller_if [MAX_MEMORY_CONTROLLERS],

    // Cache coherency
    inout cache_coherency_if coherency_if,

    // Interrupts
    input  logic [NUM_CORES-1:0]    external_irq_i,
    input  logic                    timer_irq_i,
    input  logic                    software_irq_i,

    // Debug
    input  logic                    debug_req_i,
    output logic [NUM_CORES-1:0]    debug_ack_o,

    // Performance monitoring outputs from cores
    output logic [NUM_CORES-1:0] instruction_retired_per_core,
    output logic [NUM_CORES-1:0] core_active_o,
    output logic [NUM_CORES-1:0] pipeline_stall_per_core,
    output logic [NUM_CORES-1:0] branch_mispredicted_per_core,
    output logic [NUM_CORES-1:0] l1_icache_miss,
    output logic [NUM_CORES-1:0] l1_dcache_miss,
    output logic [31:0]             cache_miss_count_o,

    // Cache Topology
    input system_cache_topology_t cache_topology_config
);

    //-------------------------------------------------------------------------
    // Core Array Generation
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < NUM_CORES; i++) begin : gen_cores
            
            core_subsystem #(
                .CORE_ID(i),
                .EXECUTION_MODE(EXECUTION_MODE),
                .BRANCH_PREDICTOR_TYPE(BRANCH_PREDICTOR_TYPE),
                .L1_ICACHE_SIZE(L1_ICACHE_SIZE),
                .L1_DCACHE_SIZE(L1_DCACHE_SIZE)
            ) u_core_subsystem (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                
                // Core configuration
                .hart_id_i(i[31:0]),
                .boot_addr_i(DEFAULT_RESET_VECTOR),
                
                // Memory interfaces using proper modports
                .imem_if(l1_icache_if[i]),
                .dmem_if(l1_dcache_if[i]),
                
                // Cache coherency
                .coherency_if(coherency_if),
                
                // Interrupts
                .external_irq_i(external_irq_i[i]),
                .timer_irq_i(timer_irq_i),
                .software_irq_i(software_irq_i),
                
                // Debug
                .debug_req_i(debug_req_i),
                .debug_ack_o(debug_ack_o[i]),
                
                // Performance monitoring
                .instruction_retired_o(instruction_retired_per_core[i]),
                .core_active_o(core_active_o[i]),
                .pipeline_stall_o(pipeline_stall_per_core[i]),
                .branch_mispredicted_o(branch_mispredicted_per_core[i])
            );
            
        end : gen_cores
    endgenerate

    //-------------------------------------------------------------------------
    // Cache Cluster Manager
    //-------------------------------------------------------------------------
    cache_cluster_manager #(
        .NUM_CORES(NUM_CORES),
        .CACHE_TOPOLOGY(CACHE_TOPOLOGY_UNIFIED), // Default, can be overridden
        .L2_CACHE_SIZE(L2_CACHE_SIZE),
        .L3_CACHE_SIZE(L3_CACHE_SIZE)
    ) u_cache_cluster_manager (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Topology configuration
        .topology_config_i(cache_topology_config),
        
        // L1 cache interfaces from cores
        .l1_dcache_if(l1_dcache_if),
        .l1_icache_if(l1_icache_if),
        
        // External memory interfaces
        .mem_if(mem_controller_if),
        
        // Cache coherency interfaces
        .coherency_if(coherency_if),
        
        // Status and control outputs
        .l2_instance_active_o(/* connected to system status */),
        .l3_instance_active_o(/* connected to system status */),
        .cluster_status_o(/* connected to system status */),
        .cache_miss_count_o(cache_miss_count_o),
        .topology_valid_o(/* connected to system status */),
        .l1_icache_miss_o(l1_icache_miss),
        .l1_dcache_miss_o(l1_dcache_miss)
    );

endmodule : multi_core_cluster 