
`timescale 1ns / 1ps

import riscv_core_pkg::*;
import riscv_config_pkg::*;
`include "power_pkg.sv"

module clock_gating_control #(
    parameter NUM_CORES = MAX_CORES
) (
    input  logic                          clk_i,
    input  logic                          rst_ni,
    input  power_state_t                  current_power_state_i,
    input  power_config_t                 power_config_i,
    input  logic [NUM_CORES-1:0]          core_active_i,
    input  logic                          cache_active_i,
    input  logic [31:0]                   cache_miss_rate_i,
    output logic [NUM_CORES-1:0]          core_clk_en_o,
    output logic                          l2_cache_clk_en_o,
    output logic                          l3_cache_clk_en_o,
    output logic                          interconnect_clk_en_o
);

    logic [NUM_CORES-1:0] core_clk_gate_r;
    logic l2_cache_clk_gate_r;
    logic l3_cache_clk_gate_r;
    logic interconnect_clk_gate_r;
    logic [15:0] state_timer_r; // This should be an input from the power_state_machine

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni) begin
            state_timer_r <= '0;
        end else begin
            state_timer_r <= state_timer_r + 1;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_clock_gating
        if (!rst_ni) begin
            core_clk_gate_r <= '1;
            l2_cache_clk_gate_r <= 1'b1;
            l3_cache_clk_gate_r <= 1'b1;
            interconnect_clk_gate_r <= 1'b1;
        end else begin
            for (int i = 0; i < NUM_CORES; i++) begin
                case (current_power_state_i)
                    POWER_ACTIVE: begin
                        core_clk_gate_r[i] <= core_active_i[i] || !power_config_i.aggressive_gating;
                    end
                    POWER_IDLE: begin
                        core_clk_gate_r[i] <= core_active_i[i];
                    end
                    POWER_SLEEP, POWER_DEEP_SLEEP: begin
                        core_clk_gate_r[i] <= 1'b0;
                    end
                    POWER_THERMAL_THROTTLE: begin
                        core_clk_gate_r[i] <= (state_timer_r[3:0] == i) && core_active_i[i];
                    end
                    default: begin
                        core_clk_gate_r[i] <= core_active_i[i];
                    end
                endcase
            end

            case (current_power_state_i)
                POWER_ACTIVE, POWER_IDLE: begin
                    l2_cache_clk_gate_r <= cache_active_i || !power_config_i.cache_gating_en;
                    l3_cache_clk_gate_r <= (cache_miss_rate_i > 10) || !power_config_i.cache_gating_en;
                end
                POWER_SLEEP: begin
                    l2_cache_clk_gate_r <= power_config_i.retention_mode;
                    l3_cache_clk_gate_r <= 1'b0;
                end
                POWER_DEEP_SLEEP: begin
                    l2_cache_clk_gate_r <= 1'b0;
                    l3_cache_clk_gate_r <= 1'b0;
                end
                default: begin
                    l2_cache_clk_gate_r <= cache_active_i;
                    l3_cache_clk_gate_r <= cache_active_i;
                end
            endcase

            interconnect_clk_gate_r <= (current_power_state_i == POWER_ACTIVE) ||
                                      (current_power_state_i == POWER_IDLE && |core_active_i);
        end
    end

    assign core_clk_en_o = core_clk_gate_r;
    assign l2_cache_clk_en_o = l2_cache_clk_gate_r;
    assign l3_cache_clk_en_o = l3_cache_clk_gate_r;
    assign interconnect_clk_en_o = interconnect_clk_gate_r;

endmodule
