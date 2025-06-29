//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: qos_csr_regfile.sv
// Module: qos_csr_regfile
//
// Project Name: RISC-V RV32IM QoS CSR Configuration
// Target Devices: ASIC/FPGA
//
// Description:
//   CSR register file for software-configurable QoS parameters.
//   Provides runtime control over QoS policies, levels, and monitoring.
//   Integrates with RISC-V CSR address space using custom CSR addresses.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_config_pkg::*;
import riscv_types_pkg::*;
import riscv_qos_pkg::*;

module qos_csr_regfile #(
    parameter integer NUM_CORES = 4,
    parameter integer NUM_QOS_LEVELS = 16
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    // CSR Interface
    input  logic        csr_req_valid_i,
    input  logic [11:0] csr_addr_i,
    input  logic        csr_write_i,
    input  word_t       csr_wdata_i,
    output logic        csr_req_ready_o,
    
    output logic        csr_rsp_valid_o,
    output word_t       csr_rdata_o,
    output logic        csr_error_o,

    // QoS Configuration Outputs
    output qos_control_reg_t            qos_control_o,
    output logic [3:0]                  qos_levels_o [NUM_CORES],      // Per-core QoS levels
    output logic [7:0]                  qos_weights_o [NUM_CORES],     // Per-core weights
    output logic [15:0]                 qos_latency_limits_o [NUM_CORES], // Per-core latency limits
    output qos_arbiter_policy_e         arbiter_policy_o,
    output logic [7:0]                  bandwidth_allocation_o [NUM_CORES], // Bandwidth per core
    
    // QoS Status Inputs
    input  logic [31:0]                 qos_violations_i,
    input  logic [31:0]                 total_requests_i,
    input  logic [31:0]                 qos_hit_counts_i [NUM_QOS_LEVELS],
    input  logic [31:0]                 qos_miss_counts_i [NUM_QOS_LEVELS],
    input  logic [31:0]                 avg_latencies_i [NUM_QOS_LEVELS],
    
    // Debug Interface
    output logic                        qos_debug_enable_o,
    output logic [3:0]                  debug_qos_level_o,
    input  logic [31:0]                 debug_status_i
);

    //---------------------------------------------------------------------------
    // QoS CSR Address Map (Custom CSR space 0xBC0-0xBFF)
    //---------------------------------------------------------------------------
    localparam logic [11:0] CSR_QOS_CONTROL     = 12'hBC0;  // Global QoS control
    localparam logic [11:0] CSR_QOS_STATUS      = 12'hBC1;  // QoS status register
    localparam logic [11:0] CSR_QOS_VIOLATIONS  = 12'hBC2;  // QoS violation count
    localparam logic [11:0] CSR_QOS_REQUESTS    = 12'hBC3;  // Total request count
    
    // Per-core QoS configuration (0xBC4-0xBC7)
    localparam logic [11:0] CSR_QOS_CORE0_CFG   = 12'hBC4;  // Core 0 QoS config
    localparam logic [11:0] CSR_QOS_CORE1_CFG   = 12'hBC5;  // Core 1 QoS config  
    localparam logic [11:0] CSR_QOS_CORE2_CFG   = 12'hBC6;  // Core 2 QoS config
    localparam logic [11:0] CSR_QOS_CORE3_CFG   = 12'hBC7;  // Core 3 QoS config
    
    // QoS performance monitoring (0xBC8-0xBCF)
    localparam logic [11:0] CSR_QOS_PERF_BASE   = 12'hBC8;  // Base for performance CSRs
    
    // QoS bandwidth allocation (0xBD0-0xBD3)
    localparam logic [11:0] CSR_QOS_BW_CORE0    = 12'hBD0;  // Core 0 bandwidth
    localparam logic [11:0] CSR_QOS_BW_CORE1    = 12'hBD1;  // Core 1 bandwidth
    localparam logic [11:0] CSR_QOS_BW_CORE2    = 12'hBD2;  // Core 2 bandwidth
    localparam logic [11:0] CSR_QOS_BW_CORE3    = 12'hBD3;  // Core 3 bandwidth
    
    // QoS debug and monitoring (0xBD4-0xBDF)
    localparam logic [11:0] CSR_QOS_DEBUG       = 12'hBD4;  // Debug control
    localparam logic [11:0] CSR_QOS_MONITOR     = 12'hBD5;  // Monitoring control
    
    //---------------------------------------------------------------------------
    // CSR Storage Registers
    //---------------------------------------------------------------------------
    qos_control_reg_t qos_control_r;
    logic [31:0] qos_status_r;
    
    // Per-core configuration registers
    typedef struct packed {
        logic [3:0]  qos_level;        // [31:28] QoS level
        logic [7:0]  weight;           // [27:20] Arbitration weight  
        logic [15:0] latency_limit;    // [19:4]  Latency limit (cycles)
        logic [3:0]  reserved;         // [3:0]   Reserved
    } qos_core_config_t;
    
    qos_core_config_t qos_core_config_r [NUM_CORES];
    logic [7:0] bandwidth_allocation_r [NUM_CORES];
    
    // Debug and monitoring registers
    logic [31:0] qos_debug_r;
    logic [31:0] qos_monitor_r;
    
    // Performance monitoring registers (read-only)
    logic [31:0] qos_perf_hits_r [NUM_QOS_LEVELS];
    logic [31:0] qos_perf_misses_r [NUM_QOS_LEVELS];
    logic [31:0] qos_perf_latencies_r [NUM_QOS_LEVELS];

    //---------------------------------------------------------------------------
    // CSR Access Logic
    //---------------------------------------------------------------------------
    logic csr_addr_valid;
    logic csr_write_enable;
    logic csr_read_enable;
    
    assign csr_addr_valid = (csr_addr_i >= 12'hBC0) && (csr_addr_i <= 12'hBDF);
    assign csr_write_enable = csr_req_valid_i && csr_write_i && csr_addr_valid;
    assign csr_read_enable = csr_req_valid_i && !csr_write_i && csr_addr_valid;
    assign csr_req_ready_o = 1'b1; // Always ready
    
    //---------------------------------------------------------------------------
    // CSR Write Logic
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_csr_write
        if (!rst_ni) begin
            // Reset to default QoS configuration
            qos_control_r <= '{
                reserved: 16'h0,
                max_qos_level: 4'hF,
                arbiter_policy: QOS_ARBITER_WEIGHTED_RR,
                qos_enable: 1'b1,
                emergency_enable: 1'b1,
                monitoring_enable: 1'b1,
                bandwidth_control: 1'b1,
                latency_control: 1'b1,
                preemption_enable: 1'b1,
                real_time_mode: 1'b0,
                starvation_prevent: 1'b1,
                reset_counters: 1'b0
            };
            
            // Initialize per-core configurations
            for (int i = 0; i < NUM_CORES; i++) begin
                qos_core_config_r[i] <= '{
                    qos_level: QOS_LEVEL_MEDIUM_HIGH,
                    weight: 8'd100,
                    latency_limit: 16'd100,
                    reserved: 4'h0
                };
                bandwidth_allocation_r[i] <= 8'd25; // 25% per core
            end
            
            qos_debug_r <= 32'h0;
            qos_monitor_r <= 32'h0;
        end else if (csr_write_enable) begin
            case (csr_addr_i)
                CSR_QOS_CONTROL: begin
                    qos_control_r <= csr_wdata_i;
                end
                
                CSR_QOS_CORE0_CFG: qos_core_config_r[0] <= csr_wdata_i;
                CSR_QOS_CORE1_CFG: qos_core_config_r[1] <= csr_wdata_i;
                CSR_QOS_CORE2_CFG: qos_core_config_r[2] <= csr_wdata_i;
                CSR_QOS_CORE3_CFG: qos_core_config_r[3] <= csr_wdata_i;
                
                CSR_QOS_BW_CORE0: bandwidth_allocation_r[0] <= csr_wdata_i[7:0];
                CSR_QOS_BW_CORE1: bandwidth_allocation_r[1] <= csr_wdata_i[7:0];
                CSR_QOS_BW_CORE2: bandwidth_allocation_r[2] <= csr_wdata_i[7:0];
                CSR_QOS_BW_CORE3: bandwidth_allocation_r[3] <= csr_wdata_i[7:0];
                
                CSR_QOS_DEBUG: begin
                    qos_debug_r <= csr_wdata_i;
                end
                
                CSR_QOS_MONITOR: begin
                    qos_monitor_r <= csr_wdata_i;
                end
                
                default: begin
                    // Invalid address - do nothing
                end
            endcase
        end
    end
    
    //---------------------------------------------------------------------------
    // CSR Read Logic
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_csr_read
        if (!rst_ni) begin
            csr_rsp_valid_o <= 1'b0;
            csr_rdata_o <= 32'h0;
            csr_error_o <= 1'b0;
        end else begin
            csr_rsp_valid_o <= csr_read_enable;
            csr_error_o <= csr_req_valid_i && !csr_addr_valid;
            
            if (csr_read_enable) begin
                case (csr_addr_i)
                    CSR_QOS_CONTROL: begin
                        csr_rdata_o <= qos_control_r;
                    end
                    
                    CSR_QOS_STATUS: begin
                        csr_rdata_o <= {
                            16'h0,                              // [31:16] Reserved
                            qos_violations_i[15:8],             // [15:8]  Recent violations
                            4'h0,                              // [7:4]   Reserved
                            qos_control_r.qos_enable,         // [3]     QoS enabled
                            qos_control_r.emergency_enable,   // [2]     Emergency mode
                            qos_control_r.monitoring_enable,  // [1]     Monitoring active
                            |qos_violations_i                 // [0]     Any violations
                        };
                    end
                    
                    CSR_QOS_VIOLATIONS: begin
                        csr_rdata_o <= qos_violations_i;
                    end
                    
                    CSR_QOS_REQUESTS: begin
                        csr_rdata_o <= total_requests_i;
                    end
                    
                    CSR_QOS_CORE0_CFG: csr_rdata_o <= qos_core_config_r[0];
                    CSR_QOS_CORE1_CFG: csr_rdata_o <= qos_core_config_r[1];
                    CSR_QOS_CORE2_CFG: csr_rdata_o <= qos_core_config_r[2];
                    CSR_QOS_CORE3_CFG: csr_rdata_o <= qos_core_config_r[3];
                    
                    CSR_QOS_BW_CORE0: csr_rdata_o <= {24'h0, bandwidth_allocation_r[0]};
                    CSR_QOS_BW_CORE1: csr_rdata_o <= {24'h0, bandwidth_allocation_r[1]};
                    CSR_QOS_BW_CORE2: csr_rdata_o <= {24'h0, bandwidth_allocation_r[2]};
                    CSR_QOS_BW_CORE3: csr_rdata_o <= {24'h0, bandwidth_allocation_r[3]};
                    
                    CSR_QOS_DEBUG: begin
                        csr_rdata_o <= qos_debug_r;
                    end
                    
                    CSR_QOS_MONITOR: begin
                        csr_rdata_o <= qos_monitor_r;
                    end
                    
                    default: begin
                        if (csr_addr_i >= CSR_QOS_PERF_BASE && csr_addr_i < (CSR_QOS_PERF_BASE + NUM_QOS_LEVELS)) begin
                            // Performance monitoring registers
                            int perf_idx = csr_addr_i - CSR_QOS_PERF_BASE;
                            csr_rdata_o <= qos_hit_counts_i[perf_idx];
                        end else begin
                            csr_rdata_o <= 32'h0;
                        end
                    end
                endcase
            end else begin
                csr_rdata_o <= 32'h0;
            end
        end
    end
    
    //---------------------------------------------------------------------------
    // Performance Counter Updates
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_perf_counters
        if (!rst_ni) begin
            for (int i = 0; i < NUM_QOS_LEVELS; i++) begin
                qos_perf_hits_r[i] <= 32'h0;
                qos_perf_misses_r[i] <= 32'h0;
                qos_perf_latencies_r[i] <= 32'h0;
            end
        end else begin
            // Update performance counters from inputs
            for (int i = 0; i < NUM_QOS_LEVELS; i++) begin
                qos_perf_hits_r[i] <= qos_hit_counts_i[i];
                qos_perf_misses_r[i] <= qos_miss_counts_i[i];
                qos_perf_latencies_r[i] <= avg_latencies_i[i];
            end
            
            // Reset counters if requested
            if (qos_control_r.reset_counters) begin
                for (int i = 0; i < NUM_QOS_LEVELS; i++) begin
                    qos_perf_hits_r[i] <= 32'h0;
                    qos_perf_misses_r[i] <= 32'h0;
                    qos_perf_latencies_r[i] <= 32'h0;
                end
            end
        end
    end
    
    //---------------------------------------------------------------------------
    // Output Assignments
    //---------------------------------------------------------------------------
    assign qos_control_o = qos_control_r;
    assign arbiter_policy_o = qos_control_r.arbiter_policy;
    
    // Per-core QoS assignments
    always_comb begin : proc_output_assignments
        for (int i = 0; i < NUM_CORES; i++) begin
            qos_levels_o[i] = qos_core_config_r[i].qos_level;
            qos_weights_o[i] = qos_core_config_r[i].weight;
            qos_latency_limits_o[i] = qos_core_config_r[i].latency_limit;
            bandwidth_allocation_o[i] = bandwidth_allocation_r[i];
        end
    end
    
    // Debug outputs
    assign qos_debug_enable_o = qos_debug_r[0];
    assign debug_qos_level_o = qos_debug_r[7:4];

endmodule : qos_csr_regfile

`default_nettype wire 