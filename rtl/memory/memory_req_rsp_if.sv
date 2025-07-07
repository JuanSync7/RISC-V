//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: memory_req_rsp_if.sv
// Module: memory_req_rsp_if
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Protocol-agnostic memory request/response interface. Abstracts memory
//   protocol details from core logic, enabling easy switching between
//   AXI4, CHI, TileLink, etc.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_mem_types_pkg::*;
import riscv_qos_pkg::*;

// Memory request/response types are now defined in riscv_mem_types_pkg

//------------------------------------------------------------------------- 
// Enhanced Memory Request/Response Interface with QoS Support
//-------------------------------------------------------------------------
interface memory_req_rsp_if #(
    parameter int unsigned ADDR_WIDTH = riscv_mem_types_pkg::ADDR_WIDTH,
    parameter int unsigned DATA_WIDTH = riscv_mem_types_pkg::DATA_WIDTH
)(
    input logic clk,
    input logic rst_n
);

    // Memory Request Signals
    logic                     req_valid;
    memory_req_t              req;
    qos_config_t              req_qos_config;    // QoS configuration for request
    logic [3:0]               req_qos_level;     // Quick QoS level access
    logic                     req_urgent;        // Urgent request flag
    logic [7:0]               req_bandwidth_pct; // Bandwidth percentage requirement
    logic                     req_ready;

    // Memory Response Signals  
    logic                     rsp_valid;
    memory_rsp_t              rsp;
    qos_config_t              rsp_qos_config;    // QoS configuration for response
    logic [15:0]              rsp_latency;       // Actual response latency cycles
    logic                     rsp_qos_violation; // QoS violation indicator
    logic                     rsp_ready;

    // QoS Monitoring Signals
    logic [31:0]              qos_req_timestamp;  // Request timestamp for latency measurement
    logic [31:0]              qos_cycles_waited;  // Cycles spent waiting
    logic                     qos_deadline_miss;  // Deadline missed indicator
    logic [2:0]               qos_retry_count;    // Number of retries attempted

    //------------------------------------------------------------------------- 
    // Master Modport (for cores, caches)
    //-------------------------------------------------------------------------
    modport master (
        input  clk,
        input  rst_n,
        
        // Request Interface
        output req_valid,
        output req,
        output req_qos_config,
        output req_qos_level,
        output req_urgent,
        output req_bandwidth_pct,
        input  req_ready,
        
        // Response Interface
        input  rsp_valid,
        input  rsp,
        input  rsp_qos_config,
        input  rsp_latency,
        input  rsp_qos_violation,
        output rsp_ready,
        
        // QoS Monitoring (input only for master)
        input  qos_req_timestamp,
        input  qos_cycles_waited,
        input  qos_deadline_miss,
        input  qos_retry_count
    );

    //------------------------------------------------------------------------- 
    // Slave Modport (for memory controllers, interconnects)
    //-------------------------------------------------------------------------
    modport slave (
        input  clk,
        input  rst_n,
        
        // Request Interface
        input  req_valid,
        input  req,
        input  req_qos_config,
        input  req_qos_level,
        input  req_urgent,
        input  req_bandwidth_pct,
        output req_ready,
        
        // Response Interface
        output rsp_valid,
        output rsp,
        output rsp_qos_config,
        output rsp_latency,
        output rsp_qos_violation,
        input  rsp_ready,
        
        // QoS Monitoring (output for slave)
        output qos_req_timestamp,
        output qos_cycles_waited,
        output qos_deadline_miss,
        output qos_retry_count
    );

    //------------------------------------------------------------------------- 
    // Monitor Modport (for testbenches, performance monitoring)
    //-------------------------------------------------------------------------
    modport monitor (
        input  clk,
        input  rst_n,
        input  req_valid,
        input  req,
        input  req_qos_config,
        input  req_qos_level,
        input  req_urgent,
        input  req_bandwidth_pct,
        input  req_ready,
        input  rsp_valid,
        input  rsp,
        input  rsp_qos_config,
        input  rsp_latency,
        input  rsp_qos_violation,
        input  rsp_ready,
        input  qos_req_timestamp,
        input  qos_cycles_waited,
        input  qos_deadline_miss,
        input  qos_retry_count
    );

    //------------------------------------------------------------------------- 
    // QoS Helper Functions
    //-------------------------------------------------------------------------
    
    // Set QoS configuration from qos_config_t
    function automatic void set_qos_config(input qos_config_t qos_config);
        req_qos_config = qos_config;
        req_qos_level = qos_config.qos_level;
        req_urgent = qos_config.urgent;
        req_bandwidth_pct = qos_config.bandwidth_percent;
    endfunction

    // Get QoS priority for arbitration (higher number = higher priority)  
    function automatic logic [7:0] get_qos_priority();
        if (req_urgent) begin
            return 8'd255; // Maximum priority for urgent requests
        end else begin
            return {req_qos_level, 4'b0000}; // Scale QoS level to 8-bit priority
        end
    endfunction

    // Check if request meets QoS deadline
    function automatic logic check_qos_deadline(input logic [31:0] current_cycle);
        logic [31:0] elapsed_cycles;
        elapsed_cycles = current_cycle - qos_req_timestamp;
        return (elapsed_cycles <= req_qos_config.max_latency_cycles);
    endfunction

    // Get QoS weight for weighted arbitration
    function automatic logic [7:0] get_qos_weight();
        return req_qos_config.weight;
    endfunction

    //------------------------------------------------------------------------- 
    // QoS Assertions for Verification
    //-------------------------------------------------------------------------
    `ifdef SIMULATION
        // QoS level should be within valid range
        property qos_level_valid;
            @(posedge clk) req_valid |-> (req_qos_level inside {[QOS_LEVEL_BEST_EFFORT:QOS_LEVEL_CRITICAL]});
        endproperty
        assert property (qos_level_valid) else $error("Invalid QoS level: %0d", req_qos_level);

        // Urgent requests should have high QoS levels
        property urgent_implies_high_qos;
            @(posedge clk) (req_valid && req_urgent) |-> (req_qos_level >= QOS_LEVEL_HIGH);
        endproperty
        assert property (urgent_implies_high_qos) else $warning("Urgent request with low QoS level");

        // Response latency should be tracked for QoS monitoring
        property latency_tracking;
            @(posedge clk) (rsp_valid && req_qos_config.max_latency_cycles > 0) |-> (rsp_latency > 0);
        endproperty
        assert property (latency_tracking) else $warning("Missing latency tracking for QoS response");
    `endif

endinterface : memory_req_rsp_if

`default_nettype wire

//=============================================================================
// Dependencies: riscv_core_pkg.sv
//
// Performance:
//   - Critical Path: Interface handshake to data transfer
//   - Max Frequency: TBD
//   - Area: N/A (interface file)
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk)
//
// Testing:
//   - Testbench: TBD
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//=============================================================================