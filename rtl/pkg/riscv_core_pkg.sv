//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: riscv_core_pkg.sv
// Module: riscv_core_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Top-level package for the RV32IM RISC-V core. Imports all specialized
//   sub-packages to provide a single import for modules that require broad
//   access to all core types. The configuration package is imported first
//   to provide all parameterized values.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_core_pkg;

    // Configuration package (imported first - contains all parameters)
    import riscv_config_pkg::*;
    
    // Core architectural types and parameters
    import riscv_types_pkg::*;
    import riscv_core_types_pkg::*;
    
    // Memory hierarchy and coherency types
    import riscv_mem_types_pkg::*;
    import riscv_cache_types_pkg::*;
    import riscv_cache_topology_pkg::*;
    
    // Branch prediction types
    import riscv_bp_types_pkg::*;
    
    // Protocol adapter types
    import riscv_protocol_types_pkg::*;
    
    // Out-of-order execution types
    import riscv_ooo_types_pkg::*;
    
    // Exception and interrupt types
    import riscv_exception_pkg::*;
    
    // Verification types
    import riscv_verif_types_pkg::*;

    // Data Processing Unit types
    import riscv_dpu_types_pkg::*;
    import riscv_fpu_types_pkg::*;
    import riscv_vpu_types_pkg::*;

    //---------------------------------------------------------------------------
    // 1. Default Parameter Values (derived from riscv_config_pkg)
    //---------------------------------------------------------------------------
    parameter logic DEFAULT_ENABLE_FPU = CONFIG_ENABLE_FPU;
    parameter logic DEFAULT_ENABLE_VPU = CONFIG_ENABLE_VPU;
    parameter logic DEFAULT_ENABLE_ML_INFERENCE = CONFIG_ENABLE_ML_INFERENCE;
    parameter logic DEFAULT_ENABLE_MMU = CONFIG_ENABLE_MMU;
    parameter logic DEFAULT_ENABLE_QOS = CONFIG_ENABLE_QOS;
    parameter logic DEFAULT_ENABLE_DATA_ACCELERATOR = CONFIG_ENABLE_DATA_ACCELERATOR;
    parameter int MAX_CORES = CONFIG_NUM_CORES;
    parameter int DEFAULT_VALIDATION_DEPTH = CONFIG_DEFAULT_VALIDATION_DEPTH;
    parameter string DEFAULT_MEMORY_PROTOCOL = CONFIG_MEMORY_PROTOCOL;
    parameter int DEFAULT_AXI4_MAX_OUTSTANDING = CONFIG_AXI4_MAX_OUTSTANDING;
    parameter int DEFAULT_MSG_WIDTH = CONFIG_MSG_WIDTH;
    parameter int DEFAULT_NUM_BARRIERS = CONFIG_NUM_BARRIERS;

    //---------------------------------------------------------------------------
    // 2. Core Configuration Presets
    //---------------------------------------------------------------------------
    // Small configuration for area-constrained designs
    parameter ooo_config_t SMALL_OOO_CONFIG = '{
        rob_size: CONFIG_SMALL_ROB_SIZE,
        rs_size: CONFIG_SMALL_RS_SIZE,
        phys_regs: CONFIG_DEFAULT_PHYS_REGS,
        num_alu_units: CONFIG_DEFAULT_NUM_ALU_UNITS,
        num_mult_units: CONFIG_DEFAULT_NUM_MULT_UNITS,
        num_div_units: CONFIG_DEFAULT_NUM_DIV_UNITS,
        div_latency: CONFIG_DEFAULT_DIV_LATENCY
    };

    // Large configuration for high-performance designs
    parameter ooo_config_t LARGE_OOO_CONFIG = '{
        rob_size: CONFIG_LARGE_ROB_SIZE,
        rs_size: CONFIG_LARGE_RS_SIZE,
        phys_regs: CONFIG_DEFAULT_PHYS_REGS,
        num_alu_units: CONFIG_DEFAULT_NUM_ALU_UNITS,
        num_mult_units: CONFIG_DEFAULT_NUM_MULT_UNITS,
        num_div_units: CONFIG_DEFAULT_NUM_DIV_UNITS,
        div_latency: CONFIG_DEFAULT_DIV_LATENCY
    };

    // Small branch predictor configuration
    parameter bp_config_t SMALL_BP_CONFIG = '{
        btb_entries: CONFIG_SMALL_BTB_ENTRIES,
        bht_entries: CONFIG_SMALL_BHT_ENTRIES,
        pht_entries: CONFIG_DEFAULT_PHT_ENTRIES,
        selector_entries: CONFIG_DEFAULT_SELECTOR_ENTRIES,
        global_history_width: CONFIG_DEFAULT_GLOBAL_HISTORY_WIDTH,
        rsb_entries: CONFIG_DEFAULT_RSB_ENTRIES,
        predictor_type: PREDICTOR_TOURNAMENT
    };

    // Large branch predictor configuration
    parameter bp_config_t LARGE_BP_CONFIG = '{
        btb_entries: CONFIG_LARGE_BTB_ENTRIES,
        bht_entries: CONFIG_LARGE_BHT_ENTRIES,
        pht_entries: CONFIG_DEFAULT_PHT_ENTRIES,
        selector_entries: CONFIG_DEFAULT_SELECTOR_ENTRIES,
        global_history_width: CONFIG_DEFAULT_GLOBAL_HISTORY_WIDTH,
        rsb_entries: CONFIG_DEFAULT_RSB_ENTRIES,
        predictor_type: PREDICTOR_TOURNAMENT
    };

    //---------------------------------------------------------------------------
    // 2. Configuration Validation Functions
    //---------------------------------------------------------------------------
    function automatic logic validate_core_config(
        input ooo_config_t ooo_cfg,
        input bp_config_t bp_cfg
    );
        // Validate OoO configuration
        if (ooo_cfg.rob_size <= 0 || ooo_cfg.rs_size <= 0 || ooo_cfg.phys_regs <= 0) return 1'b0;
        if (ooo_cfg.num_alu_units <= 0 || ooo_cfg.num_mult_units <= 0 || ooo_cfg.num_div_units <= 0) return 1'b0;
        if (ooo_cfg.div_latency <= 0) return 1'b0;
        
        // Validate branch predictor configuration
        if (bp_cfg.btb_entries <= 0 || bp_cfg.bht_entries <= 0 || bp_cfg.pht_entries <= 0) return 1'b0;
        if (bp_cfg.selector_entries <= 0 || bp_cfg.global_history_width <= 0 || bp_cfg.rsb_entries <= 0) return 1'b0;
        
        return 1'b1;
    endfunction

    //---------------------------------------------------------------------------
    // 3. Performance Calculation Functions
    //---------------------------------------------------------------------------
    function automatic real calculate_estimated_area(
        input ooo_config_t ooo_cfg,
        input bp_config_t bp_cfg
    );
        real area = 0.0;
        
        // ROB area (rough estimate)
        area += ooo_cfg.rob_size * 100.0; // 100 gates per ROB entry
        
        // RS area
        area += ooo_cfg.rs_size * 150.0; // 150 gates per RS entry
        
        // Physical register file
        area += ooo_cfg.phys_regs * 32.0; // 32 gates per register
        
        // Branch predictor area
        area += bp_cfg.btb_entries * 50.0; // 50 gates per BTB entry
        area += bp_cfg.bht_entries * 10.0; // 10 gates per BHT entry
        area += bp_cfg.pht_entries * 10.0; // 10 gates per PHT entry
        
        return area;
    endfunction

    function automatic real calculate_estimated_power(
        input ooo_config_t ooo_cfg,
        input bp_config_t bp_cfg,
        input real frequency_mhz
    );
        real power = 0.0;
        
        // Base power
        power += 100.0; // Base core power (mW)
        
        // Frequency scaling
        power *= (frequency_mhz / 100.0); // Normalized to 100MHz
        
        // Configuration scaling
        power *= (1.0 + (ooo_cfg.rob_size / 32.0) * 0.1); // ROB scaling
        power *= (1.0 + (ooo_cfg.rs_size / 16.0) * 0.1);  // RS scaling
        
        return power;
    endfunction

endpackage : riscv_core_pkg

//=============================================================================
// Dependencies: None
//
// Performance:
//   - Critical Path: N/A (package file)
//   - Max Frequency: N/A
//   - Area: N/A
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: N/A (package file)
//
// Testing:
//   - Testbench: N/A (package file)
//   - Test Vectors: N/A
//   - Simulation Time: N/A
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//=============================================================================
