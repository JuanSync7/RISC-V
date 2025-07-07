//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: multi_core_system_refactored.sv
// Module: multi_core_system
//
// Project Name: RISC-V RV32IM Core
//
// Description:
//   Refactored multi-core RISC-V system.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

`include "components/multi_core_cluster.sv"
`include "components/multi_core_interconnect.sv"
`include "components/multi_core_management.sv"
`include "components/multi_core_monitoring.sv"

import riscv_core_pkg::*;


module multi_core_system #(
    // Parameters from original module
    parameter integer NUM_CORES = DEFAULT_NUM_CORES,
    parameter string EXECUTION_MODE = DEFAULT_EXECUTION_MODE,
    parameter string BRANCH_PREDICTOR_TYPE = DEFAULT_BRANCH_PREDICTOR_TYPE,
    parameter string DEFAULT_PROTOCOL = DEFAULT_MEMORY_PROTOCOL,
    parameter integer L1_ICACHE_SIZE = DEFAULT_L1_ICACHE_SIZE,
    parameter integer L1_DCACHE_SIZE = DEFAULT_L1_DCACHE_SIZE,
    parameter integer L2_CACHE_SIZE = DEFAULT_L2_CACHE_SIZE,
    parameter integer L3_CACHE_SIZE = DEFAULT_L3_CACHE_SIZE,
    parameter integer MSG_WIDTH = DEFAULT_MSG_WIDTH,
    parameter integer NUM_BARRIERS = DEFAULT_NUM_BARRIERS,
    parameter integer MAX_OUTSTANDING = DEFAULT_AXI4_MAX_OUTSTANDING
) (
    // Ports from original module
    input  logic clk_i,
    input  logic rst_ni,
    input  logic [NUM_CORES-1:0] external_irq_i,
    input  logic timer_irq_i,
    input  logic software_irq_i,
    input  logic debug_req_i,
    output logic [NUM_CORES-1:0] debug_ack_o,
    output logic [31:0] total_instructions_o,
    output logic [31:0] total_cycles_o,
    output logic [31:0] cache_miss_count_o,
    output logic [31:0] performance_status_o,
    output logic [NUM_CORES-1:0] core_active_o,
    input  logic [31:0] sys_config_i,
    output logic [31:0] sys_status_o,
    inout axi4_if.master axi4_if,
    inout chi_if.rn chi_if,
    inout tilelink_if.master tl_if
);

    // Internal interfaces
    memory_req_rsp_if l1_icache_if [NUM_CORES] (.clk(clk_i), .rst_n(rst_ni));
    memory_req_rsp_if l1_dcache_if [NUM_CORES] (.clk(clk_i), .rst_n(rst_ni));
    memory_req_rsp_if mem_controller_if [MAX_MEMORY_CONTROLLERS] (.clk(clk_i), .rst_n(rst_ni));
    cache_coherency_if coherency_if (.clk(clk_i), .rst_n(rst_ni));
    inter_core_comm_if #( .NUM_CORES(NUM_CORES), .MSG_WIDTH(MSG_WIDTH)) inter_core_if (.clk_i(clk_i), .rst_ni(rst_ni));
    sync_primitives_if #( .NUM_CORES(NUM_CORES), .NUM_BARRIERS(NUM_BARRIERS), .DATA_WIDTH(MSG_WIDTH)) sync_if (.clk_i(clk_i), .rst_ni(rst_ni));

    // Wires for submodule connections
    logic [NUM_CORES-1:0] instruction_retired_per_core;
    logic [NUM_CORES-1:0] pipeline_stall_per_core;
    logic [NUM_CORES-1:0] branch_mispredicted_per_core;
    logic [NUM_CORES-1:0] l1_icache_miss;
    logic [NUM_CORES-1:0] l1_dcache_miss;
    system_cache_topology_t cache_topology_config;
    logic [31:0] current_ipc_calculated;
    logic [7:0] cache_hit_rate_l1;
    logic pipeline_bottleneck;
    logic high_power_mode;
    logic good_bp;

    multi_core_cluster #(
        .NUM_CORES(NUM_CORES),
        .EXECUTION_MODE(EXECUTION_MODE),
        .BRANCH_PREDICTOR_TYPE(BRANCH_PREDICTOR_TYPE),
        .L1_ICACHE_SIZE(L1_ICACHE_SIZE),
        .L1_DCACHE_SIZE(L1_DCACHE_SIZE),
        .L2_CACHE_SIZE(L2_CACHE_SIZE),
        .L3_CACHE_SIZE(L3_CACHE_SIZE)
    ) u_multi_core_cluster (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .l1_icache_if(l1_icache_if),
        .l1_dcache_if(l1_dcache_if),
        .mem_controller_if(mem_controller_if),
        .coherency_if(coherency_if),
        .external_irq_i(external_irq_i),
        .timer_irq_i(timer_irq_i),
        .software_irq_i(software_irq_i),
        .debug_req_i(debug_req_i),
        .debug_ack_o(debug_ack_o),
        .instruction_retired_per_core(instruction_retired_per_core),
        .core_active_o(core_active_o),
        .pipeline_stall_per_core(pipeline_stall_per_core),
        .branch_mispredicted_per_core(branch_mispredicted_per_core),
        .l1_icache_miss(l1_icache_miss),
        .l1_dcache_miss(l1_dcache_miss),
        .cache_miss_count_o(cache_miss_count_o),
        .cache_topology_config(cache_topology_config)
    );

    multi_core_interconnect #(
        .NUM_CORES(NUM_CORES),
        .DEFAULT_PROTOCOL(DEFAULT_PROTOCOL),
        .MAX_OUTSTANDING(MAX_OUTSTANDING),
        .MSG_WIDTH(MSG_WIDTH),
        .NUM_BARRIERS(NUM_BARRIERS)
    ) u_multi_core_interconnect (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .sys_config_i(sys_config_i),
        .l1_icache_if(l1_icache_if),
        .l1_dcache_if(l1_dcache_if),
        .mem_controller_if(mem_controller_if),
        .axi4_if(axi4_if),
        .chi_if(chi_if),
        .tl_if(tl_if),
        .coherency_if(coherency_if),
        .inter_core_if(inter_core_if),
        .sync_if(sync_if)
    );

    multi_core_management #(
        .NUM_CORES(NUM_CORES),
        .L2_CACHE_SIZE(L2_CACHE_SIZE),
        .L3_CACHE_SIZE(L3_CACHE_SIZE),
        .MSG_WIDTH(MSG_WIDTH),
        .NUM_BARRIERS(NUM_BARRIERS)
    ) u_multi_core_management (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .sys_config_i(sys_config_i),
        .sys_status_o(sys_status_o),
        .axi4_if(axi4_if),
        .chi_if(chi_if),
        .tl_if(tl_if),
        .current_ipc_calculated(current_ipc_calculated),
        .cache_hit_rate_l1(cache_hit_rate_l1),
        .any_core_active(|core_active_o),
        .pipeline_bottleneck(pipeline_bottleneck),
        .high_power_mode(high_power_mode),
        .good_bp(good_bp),
        .core_active_i(core_active_o),
        .comm_if(inter_core_if),
        .sync_if(sync_if),
        .cache_topology_config(cache_topology_config)
    );

    multi_core_monitoring #(
        .NUM_CORES(NUM_CORES)
    ) u_multi_core_monitoring (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .core_active_i(core_active_o),
        .instruction_retired_per_core(instruction_retired_per_core),
        .branch_mispredicted_per_core(branch_mispredicted_per_core),
        .pipeline_stall_per_core(pipeline_stall_per_core),
        .l1_icache_miss(l1_icache_miss),
        .l1_dcache_miss(l1_dcache_miss),
        .cache_miss_count_i(cache_miss_count_o),
        .total_instructions_o(total_instructions_o),
        .total_cycles_o(total_cycles_o),
        .performance_status_o(performance_status_o),
        .current_ipc_calculated_o(current_ipc_calculated),
        .cache_hit_rate_l1_o(cache_hit_rate_l1),
        .pipeline_bottleneck_o(pipeline_bottleneck),
        .high_power_mode_o(high_power_mode),
        .good_bp_o(good_bp)
    );

endmodule : multi_core_system 