
`timescale 1ns / 1ps

`include "power_pkg.sv"

module power_domain_control #(
    parameter NUM_CORES = 1,
    parameter NUM_POWER_DOMAINS = 4
) (
    input  logic                          clk_i,
    input  logic                          rst_ni,
    input  power_state_t                  current_power_state_i,
    input  power_config_t                 power_config_i,
    input  logic [NUM_CORES-1:0]          core_active_i,
    input  logic                          l2_cache_clk_gate_i,
    input  logic                          l3_cache_clk_gate_i,
    input  logic                          interconnect_clk_gate_i,
    input  logic [15:0]                   state_timer_i,
    output logic [NUM_POWER_DOMAINS-1:0]  power_domain_en_o,
    output logic [NUM_POWER_DOMAINS-1:0]  retention_mode_o,
    output logic [31:0]                   throttling_event_count_o
);

    logic [NUM_POWER_DOMAINS-1:0] power_domain_en_r;
    logic [NUM_POWER_DOMAINS-1:0] retention_mode_r;
    logic [31:0] throttling_event_count_r;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_power_domains
        if (!rst_ni) begin
            power_domain_en_r <= '1;
            retention_mode_r <= '0;
            throttling_event_count_r <= '0;
        end else begin
            for (int i = 0; i < NUM_CORES; i++) begin
                case (current_power_state_i)
                    POWER_ACTIVE: begin
                        power_domain_en_r[i] <= 1'b1;
                        retention_mode_r[i] <= 1'b0;
                    end
                    POWER_IDLE: begin
                        power_domain_en_r[i] <= core_active_i[i] || !power_config_i.power_gating_en;
                        retention_mode_r[i] <= !core_active_i[i] && power_config_i.retention_mode;
                    end
                    POWER_SLEEP: begin
                        power_domain_en_r[i] <= core_active_i[i];
                        retention_mode_r[i] <= !core_active_i[i];
                    end
                    POWER_DEEP_SLEEP: begin
                        power_domain_en_r[i] <= 1'b0;
                        retention_mode_r[i] <= power_config_i.retention_mode;
                    end
                    POWER_THERMAL_THROTTLE: begin
                        power_domain_en_r[i] <= (state_timer_i[7:0] % NUM_CORES) == i;
                        retention_mode_r[i] <= 1'b0;
                        if ((state_timer_i[7:0] % NUM_CORES) == i && state_timer_i[7:0] != 0) begin
                            throttling_event_count_r <= throttling_event_count_r + 1;
                        end
                    end
                endcase
            end

            power_domain_en_r[NUM_CORES] <= l2_cache_clk_gate_i;
            power_domain_en_r[NUM_CORES+1] <= l3_cache_clk_gate_i;
            power_domain_en_r[NUM_CORES+2] <= interconnect_clk_gate_i;
            power_domain_en_r[NUM_CORES+3] <= (current_power_state_i != POWER_DEEP_SLEEP);

            retention_mode_r[NUM_CORES] <= (current_power_state_i == POWER_SLEEP) && power_config_i.retention_mode;
            retention_mode_r[NUM_CORES+1] <= (current_power_state_i == POWER_SLEEP) && power_config_i.retention_mode;
            retention_mode_r[NUM_CORES+2] <= 1'b0;
            retention_mode_r[NUM_CORES+3] <= (current_power_state_i == POWER_SLEEP) && power_config_i.retention_mode;
        end
    end

    assign power_domain_en_o = power_domain_en_r;
    assign retention_mode_o = retention_mode_r;
    assign throttling_event_count_o = throttling_event_count_r;

endmodule
