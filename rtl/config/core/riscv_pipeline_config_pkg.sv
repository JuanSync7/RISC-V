//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_pipeline_config_pkg.sv
// Module: riscv_pipeline_config_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   This package defines the configuration for the processor's pipeline,
//   including branch prediction, out-of-order execution engine, and
//   functional unit latencies. Implementation-fixed constants are defined
//   in riscv_pipeline_types_pkg.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_pipeline_config_pkg;

    import riscv_core_config_pkg::*;

    //---------------------------------------------------------------------------
    // 6. Branch Predictor Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_BTB_ENTRIES = 512;
    parameter integer DEFAULT_BHT_ENTRIES = 1024;
    parameter integer DEFAULT_PHT_ENTRIES = 256;
    parameter integer DEFAULT_SELECTOR_ENTRIES = 512;
    parameter integer DEFAULT_GLOBAL_HISTORY_WIDTH = 8;
    parameter integer DEFAULT_RSB_ENTRIES = 16;
    parameter integer DEFAULT_NUM_BP_PREDICTORS = 4;
    
    // Branch predictor counter widths
    parameter integer BTB_COUNTER_WIDTH = 2;
    parameter integer BHT_COUNTER_WIDTH = 2;
    parameter integer PHT_COUNTER_WIDTH = 2;
    parameter integer SELECTOR_COUNTER_WIDTH = 2;
    parameter integer CONFIDENCE_WIDTH = 8;
    
    // Branch predictor type configuration
    parameter string DEFAULT_BRANCH_PREDICTOR_TYPE = "TOURNAMENT";  // STATIC, DYNAMIC, TOURNAMENT
    
    // Execution mode configuration
    parameter string DEFAULT_EXECUTION_MODE = "OUT_OF_ORDER";       // "IN_ORDER" or "OUT_OF_ORDER"
    
    //---------------------------------------------------------------------------
    // 7. Out-of-Order Engine Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_ROB_SIZE = 32;
    parameter integer DEFAULT_RS_SIZE = 16;
    parameter integer DEFAULT_PHYS_REGS = 64;
    
    // Functional unit counts
    parameter integer DEFAULT_NUM_ALU_UNITS = 2;
    parameter integer DEFAULT_NUM_MULT_UNITS = 1;
    parameter integer DEFAULT_NUM_DIV_UNITS = 1;
    
    // Division unit latency
    parameter integer DEFAULT_DIV_LATENCY = 32;
    parameter integer DEFAULT_MULT_LATENCY = 3;

    //---------------------------------------------------------------------------
    // 10. Performance Configuration
    //---------------------------------------------------------------------------
    // Pipeline configuration
    parameter integer DEFAULT_PIPELINE_STAGES = 5;         // IF, ID, EX, MEM, WB



endpackage : riscv_pipeline_config_pkg

//=============================================================================
// Dependencies: Imports riscv_core_config_pkg. Conceptually linked to 
//               riscv_pipeline_types_pkg.
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
//   - Testbench:    Utilized in pipeline and core integration testbenches.
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author                          | Description
//=============================================================================
// 1.0.0   | 2025-07-31 | DesignAI (designai@sondrel.com) | Initial creation and added standard footer.
//=============================================================================

`default_nettype wire