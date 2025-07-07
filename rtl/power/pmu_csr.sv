
`timescale 1ns / 1ps

`include "power_pkg.sv"

module pmu_csr #(
    parameter NUM_CORES = 1
) (
    input  logic                          clk_i,
    input  logic                          rst_ni,
    // CSR Interface
    input  logic                          csr_access_i,
    input  logic [11:0]                   csr_addr_i,
    input  logic                          csr_write_i,
    input  logic [31:0]                   csr_wdata_i,
    output logic [31:0]                   csr_rdata_o,

    output power_config_t                 power_config_o,
    output logic                          pm_enable_o
);

    power_config_t power_config_r;
    logic pm_enable_r;

    // CSR Registers
    localparam PMU_ENABLE_ADDR      = 12'hF00;
    localparam PMU_CONFIG_ADDR      = 12'hF01;
    localparam IDLE_TIMEOUT_ADDR    = 12'hF02;
    localparam SLEEP_TIMEOUT_ADDR   = 12'hF03;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            pm_enable_r <= 1'b0;
            power_config_r.aggressive_gating <= 1'b0;
            power_config_r.cache_gating_en   <= 1'b0;
            power_config_r.retention_mode    <= 1'b0;
            power_config_r.power_gating_en   <= 1'b0;
            power_config_r.idle_timeout      <= 32'd1000;
            power_config_r.sleep_timeout     <= 32'd10000;
        end else if (csr_access_i && csr_write_i) begin
            case (csr_addr_i)
                PMU_ENABLE_ADDR:
                    pm_enable_r <= csr_wdata_i[0];
                PMU_CONFIG_ADDR: begin
                    power_config_r.aggressive_gating <= csr_wdata_i[0];
                    power_config_r.cache_gating_en   <= csr_wdata_i[1];
                    power_config_r.retention_mode    <= csr_wdata_i[2];
                    power_config_r.power_gating_en   <= csr_wdata_i[3];
                end
                IDLE_TIMEOUT_ADDR:
                    power_config_r.idle_timeout <= csr_wdata_i;
                SLEEP_TIMEOUT_ADDR:
                    power_config_r.sleep_timeout <= csr_wdata_i;
            endcase
        end
    end

    always_comb begin
        csr_rdata_o = 32'b0;
        if (csr_access_i) begin
            case (csr_addr_i)
                PMU_ENABLE_ADDR:
                    csr_rdata_o = {31'b0, pm_enable_r};
                PMU_CONFIG_ADDR:
                    csr_rdata_o = {28'b0, power_config_r.power_gating_en, power_config_r.retention_mode, power_config_r.cache_gating_en, power_config_r.aggressive_gating};
                IDLE_TIMEOUT_ADDR:
                    csr_rdata_o = power_config_r.idle_timeout;
                SLEEP_TIMEOUT_ADDR:
                    csr_rdata_o = power_config_r.sleep_timeout;
            endcase
        end
    end

    assign power_config_o = power_config_r;
    assign pm_enable_o = pm_enable_r;

endmodule
