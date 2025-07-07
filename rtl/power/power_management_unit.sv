
`timescale 1ns / 1ps

import riscv_core_pkg::*;
import riscv_config_pkg::*;
`include "power_pkg.sv"

module power_management_unit #(
    parameter NUM_CORES = MAX_CORES,
    parameter NUM_POWER_DOMAINS = CONFIG_POWER_DOMAINS
) (
    input  logic                          clk_i,
    input  logic                          rst_ni,

    // CSR Interface
    input  logic                          csr_access_i,
    input  logic [11:0]                   csr_addr_i,
    input  logic                          csr_write_i,
    input  logic [31:0]                   csr_wdata_i,
    output logic [31:0]                   csr_rdata_o,

    // Core and Cache Inputs
    input  logic [NUM_CORES-1:0]          core_active_i,
    input  logic [NUM_CORES-1:0]          core_idle_i,
    input  logic [NUM_CORES-1:0] [31:0]   core_utilization_i,
    input  logic                          cache_active_i,
    input  logic [31:0]                   cache_miss_rate_i,
    input  logic                          thermal_alert_i,

    // Power Management Outputs
    output logic [NUM_CORES-1:0]          core_clk_en_o,
    output logic                          l2_cache_clk_en_o,
    output logic                          l3_cache_clk_en_o,
    output logic                          interconnect_clk_en_o,
    output logic [2:0]                    voltage_level_o,
    output logic [3:0]                    frequency_level_o,
    output logic                          dvfs_update_o,
    output logic [NUM_POWER_DOMAINS-1:0]  power_domain_en_o,
    output logic [NUM_POWER_DOMAINS-1:0]  retention_mode_o,
    output logic [31:0]                   throttling_event_count_o
);

    // Internal Signals
    power_config_t power_config;
    logic pm_enable;
    power_state_t current_power_state;
    logic [15:0] state_timer;

    pmu_csr #(
        .NUM_CORES(NUM_CORES)
    ) i_pmu_csr (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .csr_access_i(csr_access_i),
        .csr_addr_i(csr_addr_i),
        .csr_write_i(csr_write_i),
        .csr_wdata_i(csr_wdata_i),
        .csr_rdata_o(csr_rdata_o),
        .power_config_o(power_config),
        .pm_enable_o(pm_enable)
    );

    power_state_machine i_power_state_machine (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .pm_enable_i(pm_enable),
        .power_config_i(power_config),
        .core_active_i(core_active_i),
        .core_idle_i(core_idle_i),
        .thermal_alert_i(thermal_alert_i),
        .current_power_state_o(current_power_state),
        .state_timer_o(state_timer)
    );

    dvfs_controller #(
        .NUM_CORES(NUM_CORES)
    ) i_dvfs_controller (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .current_power_state_i(current_power_state),
        .core_utilization_i(core_utilization_i),
        .cache_miss_rate_i(cache_miss_rate_i),
        .voltage_level_o(voltage_level_o),
        .frequency_level_o(frequency_level_o),
        .dvfs_update_o(dvfs_update_o)
    );

    clock_gating_control #(
        .NUM_CORES(NUM_CORES)
    ) i_clock_gating_control (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .current_power_state_i(current_power_state),
        .power_config_i(power_config),
        .core_active_i(core_active_i),
        .cache_active_i(cache_active_i),
        .cache_miss_rate_i(cache_miss_rate_i),
        .core_clk_en_o(core_clk_en_o),
        .l2_cache_clk_en_o(l2_cache_clk_en_o),
        .l3_cache_clk_en_o(l3_cache_clk_en_o),
        .interconnect_clk_en_o(interconnect_clk_en_o)
    );

    power_domain_control #(
        .NUM_CORES(NUM_CORES),
        .NUM_POWER_DOMAINS(NUM_POWER_DOMAINS)
    ) i_power_domain_control (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .current_power_state_i(current_power_state),
        .power_config_i(power_config),
        .core_active_i(core_active_i),
        .l2_cache_clk_gate_i(l2_cache_clk_en_o),
        .l3_cache_clk_gate_i(l3_cache_clk_en_o),
        .interconnect_clk_gate_i(interconnect_clk_en_o),
        .state_timer_i(state_timer),
        .power_domain_en_o(power_domain_en_o),
        .retention_mode_o(retention_mode_o),
        .throttling_event_count_o(throttling_event_count_o)
    );

endmodule
