//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_verification_config_pkg.sv
// Module: riscv_verification_config_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   This package provides configurations specifically for the verification
//   environment, including clock periods, test timeouts, and target
//   performance metrics.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_verification_config_pkg;

    //---------------------------------------------------------------------------
    // 9. Verification Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_CLK_PERIOD = 10;             // 100MHz clock
    parameter integer DEFAULT_TIMEOUT_CYCLES = 1000;
    parameter integer DEFAULT_MAX_TEST_ITERATIONS = 100;
    
    parameter time CLOCK_PERIOD = 10ns;               // Default clock period for testbenches
    parameter integer TIMEOUT_CYCLES = 100000;        // Default test timeout in cycles
    
    //---------------------------------------------------------------------------
    // 10. Performance Configuration
    //---------------------------------------------------------------------------
    // Target frequencies (MHz)
    parameter integer TARGET_FREQ_ASIC = 1000;             // 1GHz for ASIC
    parameter integer TARGET_FREQ_FPGA = 100;              // 100MHz for FPGA
    
    parameter integer DEFAULT_PERF_MON_MEASUREMENT_WINDOW = 1024;
    parameter integer DEFAULT_PERF_MON_IPC_PRECISION = 1000;

    //---------------------------------------------------------------------------
    // 10. Performance Monitor Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_PERF_MON_WINDOW   = 1024; // Cycles in measurement window
    parameter integer DEFAULT_PERF_COUNTER_WIDTH = 32;   // Width of performance counters
    parameter integer DEFAULT_IPC_PRECISION     = 1000; // IPC calculation precision multiplier

    //---------------------------------------------------------------------------
    // 11. Performance Optimizer Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_OPT_WINDOW               = 2048; // Cycles for optimization window
    parameter integer DEFAULT_IPC_TARGET               = 85;   // Target IPC percentage
    parameter integer DEFAULT_CACHE_MISS_THRESHOLD     = 15;   // Cache miss rate threshold (percent)
    parameter integer DEFAULT_BRANCH_MISS_THRESHOLD    = 10;   // Branch misprediction rate threshold (percent)
    parameter integer DEFAULT_PIPELINE_STALL_THRESHOLD = 20;   // Pipeline stall rate threshold (percent)



    //---------------------------------------------------------------------------
    // Verification Threshold Configuration
    //---------------------------------------------------------------------------
    // Performance assertion thresholds
    parameter integer MAX_IPC_THRESHOLD = 2000;                     // Maximum reasonable IPC (2.0 * 1000)
    parameter integer MIN_L1_HIT_RATE = 700;                        // Minimum L1 cache hit rate (70%)
    parameter integer MAX_HIT_RATE = 1000;                          // Maximum hit rate (100%)
    
    // System integration validation thresholds
    parameter integer CORE_SCORE_PER_ACTIVE = 21;                   // Score contribution per active core
    parameter integer MAX_CORE_SCORE = 85;                          // Maximum core score when all active
    parameter integer PROTOCOL_SCORE_HEALTHY = 85;                  // Score when all protocols healthy
    parameter integer PERFORMANCE_SCORE_ADEQUATE = 85;              // Adequate performance score threshold
    parameter integer TIMING_VALIDATION_THRESHOLD = 200;            // Critical path delay threshold
    parameter integer SWITCH_EFFICIENCY_BASELINE = 100;             // Baseline for switch efficiency calculation
    
    // QoS verification parameters
    parameter integer DEFAULT_BANDWIDTH_PERCENT = 50;               // Default bandwidth allocation (50%)
    parameter integer QOS_PRIORITY_MAX = 255;                       // Maximum QoS priority value
    parameter integer QOS_PRIORITY_SCALE_SHIFT = 4;                 // Bit shift for QoS level to priority scaling
    
    // System monitoring windows
    parameter integer MONITOR_WINDOW_SIZE = 1024;                   // Default monitoring window size
    parameter integer TRANSACTION_RATE_SCALE = 1000;                // Scaling factor for transaction rate calculation

endpackage : riscv_verification_config_pkg

//=============================================================================
// Dependencies: None.
// Instantiated In: Not Applicable (Package)
//
// Performance:
//   - Critical Path: Not Applicable (Package)
//   - Max Frequency: Not Applicable (Package)
//   - Area:          Not Applicable (Package)
//
// Verification Coverage:
//   - Code Coverage:     Not Applicable (Package)
//   - Functional Coverage: Not Applicable (Package)
//   - Branch Coverage:   Not Applicable (Package)
//
// Synthesis:
//   - Target Technology: Not Applicable (Package)
//   - Synthesis Tool:    Not Applicable (Package)
//   - Clock Domains:     Not Applicable (Package)
//   - Constraints File:  Not Applicable (Package)
//
// Testing:
//   - Testbench:    This package is central to the verification environment and used in all testbenches.
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author                          | Description
//=============================================================================
// 1.0.0   | 2025-07-31 | DesignAI (designai@sondrel.com) | Initial creation and added standard footer.
//=============================================================================

`default_nettype wire 