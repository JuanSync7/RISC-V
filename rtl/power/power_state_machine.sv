
`timescale 1ns / 1ps

import riscv_core_pkg::*;
import riscv_config_pkg::*;
`include "power_pkg.sv"

module power_state_machine #(
    parameter NUM_CORES = MAX_CORES
) (
    input  logic                          clk_i,
    input  logic                          rst_ni,
    input  logic                          pm_enable_i,
    input  power_config_t                 power_config_i,
    input  logic [NUM_CORES-1:0]          core_active_i,
    input  logic [NUM_CORES-1:0]          core_idle_i,
    input  logic                          thermal_alert_i,
    output power_state_t                  current_power_state_o,
    output logic [15:0]                   state_timer_o
);

    power_state_t current_state_r, next_state_c;
    logic [15:0] state_timer_r;
    logic [31:0] idle_timeout_counter_r;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_power_state_fsm
        if (!rst_ni) begin
            current_state_r <= POWER_ACTIVE;
            state_timer_r <= '0;
            idle_timeout_counter_r <= '0;
        end else begin
            current_state_r <= next_state_c;

            if (current_state_r != next_state_c) begin
                state_timer_r <= '0;
                idle_timeout_counter_r <= '0;
            end else begin
                state_timer_r <= state_timer_r + 1;
                if (current_state_r == POWER_IDLE) begin
                    idle_timeout_counter_r <= idle_timeout_counter_r + 1;
                end
            end
        end
    end

    always_comb begin : proc_power_state_logic
        next_state_c = current_state_r;

        if (thermal_alert_i) begin
            next_state_c = POWER_THERMAL_THROTTLE;
        end else begin
            case (current_state_r)
                POWER_ACTIVE: begin
                    if (pm_enable_i && (&core_idle_i)) begin
                        next_state_c = POWER_IDLE;
                    end
                end

                POWER_IDLE: begin
                    if (|core_active_i) begin
                        next_state_c = POWER_ACTIVE;
                    end else if (idle_timeout_counter_r > power_config_i.idle_timeout) begin
                        next_state_c = POWER_SLEEP;
                    end
                end

                POWER_SLEEP: begin
                    if (|core_active_i) begin
                        next_state_c = POWER_ACTIVE;
                    end else if (state_timer_r > power_config_i.sleep_timeout) begin
                        next_state_c = POWER_DEEP_SLEEP;
                    end
                end

                POWER_DEEP_SLEEP: begin
                    if (|core_active_i) begin
                        next_state_c = POWER_ACTIVE;
                    end
                end

                POWER_THERMAL_THROTTLE: begin
                    if (!thermal_alert_i && state_timer_r > 1000) begin
                        next_state_c = POWER_ACTIVE;
                    end
                end

                default: begin
                    next_state_c = POWER_ACTIVE;
                end
            endcase
        end
    end

    assign current_power_state_o = current_state_r;
    assign state_timer_o = state_timer_r;

endmodule
