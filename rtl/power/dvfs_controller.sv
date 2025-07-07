
`timescale 1ns / 1ps

import riscv_core_pkg::*;
import riscv_config_pkg::*;
`include "power_pkg.sv"

module dvfs_controller #(
    parameter NUM_CORES = MAX_CORES
) (
    input  logic                          clk_i,
    input  logic                          rst_ni,
    input  power_state_t                  current_power_state_i,
    input  logic [NUM_CORES-1:0] [31:0]   core_utilization_i,
    input  logic [31:0]                   cache_miss_rate_i,
    output logic [2:0]                    voltage_level_o,
    output logic [3:0]                    frequency_level_o,
    output logic                          dvfs_update_o
);

    logic [2:0] target_voltage_r;
    logic [3:0] target_frequency_r;
    logic [31:0] dvfs_transition_count_r;
    logic dvfs_update_pending_r;

    logic [31:0] average_utilization_c;
    logic [7:0] performance_demand_c;

    always_comb begin : proc_workload_analysis
        logic [31:0] total_utilization = '0;
        for (int i = 0; i < NUM_CORES; i++) begin
            total_utilization += core_utilization_i[i];
        end
        average_utilization_c = total_utilization / NUM_CORES;

        if (current_power_state_i == POWER_THERMAL_THROTTLE) begin
            performance_demand_c = 8'h20;
        end else if (cache_miss_rate_i > 50) begin
            performance_demand_c = 8'hE0;
        end else {
            performance_demand_c = average_utilization_c[7:0];
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_dvfs_controller
        if (!rst_ni) begin
            target_voltage_r <= 3'b100;
            target_frequency_r <= 4'h8;
            dvfs_transition_count_r <= '0;
            dvfs_update_pending_r <= 1'b0;
        end else begin
            logic [2:0] new_voltage;
            logic [3:0] new_frequency;

            case (performance_demand_c[7:4])
                4'h0, 4'h1: begin
                    new_voltage = 3'b001;
                    new_frequency = 4'h2;
                end
                4'h2, 4'h3: begin
                    new_voltage = 3'b010;
                    new_frequency = 4'h4;
                end
                4'h4, 4'h5, 4'h6, 4'h7: begin
                    new_voltage = 3'b100;
                    new_frequency = 4'h8;
                end
                4'h8, 4'h9, 4'hA, 4'hB: begin
                    new_voltage = 3'b110;
                    new_frequency = 4'hC;
                end
                default: begin
                    new_voltage = 3'b111;
                    new_frequency = 4'hF;
                end
            endcase

            if ((new_voltage != target_voltage_r) || (new_frequency != target_frequency_r)) begin
                if (!dvfs_update_pending_r) begin
                    target_voltage_r <= new_voltage;
                    target_frequency_r <= new_frequency;
                    dvfs_update_pending_r <= 1'b1;
                    dvfs_transition_count_r <= dvfs_transition_count_r + 1;
                end
            end else begin
                dvfs_update_pending_r <= 1'b0;
            end
        end
    end

    assign voltage_level_o = target_voltage_r;
    assign frequency_level_o = target_frequency_r;
    assign dvfs_update_o = dvfs_update_pending_r;

endmodule
