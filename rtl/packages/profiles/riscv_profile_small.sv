//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: riscv_profile_small.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: riscv_profile_small
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-28
// DESCRIPTION: Small profile configuration for area-constrained/FPGA designs.
// PRIMARY_PURPOSE: Provide optimized configuration for small implementations.
// ROLE_IN_SYSTEM: Defines complete system configuration for resource-limited targets.
// PROBLEM_SOLVED: Pre-configured settings for embedded/FPGA implementations.
// MODULE_TYPE: Package
// TARGET_TECHNOLOGY_PREF: FPGA
// RELATED_SPECIFICATION: RISC-V RV32IM
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

package riscv_profile_small;

    import riscv_base_pkg::*;
    import riscv_cache_config_pkg::*;

    //-------------------------------------------------------------------------
    // Profile Identification
    //-------------------------------------------------------------------------
    // AI_TAG: FEATURE - Small profile optimized for area and FPGA implementation
    
    parameter string PROFILE_NAME = "SMALL_FPGA";
    parameter string PROFILE_DESC = "Optimized for area-constrained and FPGA implementations";
    
    //-------------------------------------------------------------------------
    // Core Configuration
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Single-core in-order configuration
    parameter integer CONFIG_NUM_CORES = 1;
    parameter string  CONFIG_EXECUTION_MODE = "IN_ORDER";
    parameter string  CONFIG_CORE_MODE = "SINGLE_CORE";
    
    // Core architecture
    parameter integer CONFIG_XLEN = 32;  // RV32
    parameter integer CONFIG_ADDR_WIDTH = 32;
    parameter logic [31:0] CONFIG_RESET_VECTOR = 32'h0000_0000;
    
    // Pipeline configuration
    parameter integer CONFIG_PIPELINE_STAGES = 5;  // Standard 5-stage
    parameter logic   CONFIG_FORWARDING_ENABLE = 1'b1;
    parameter logic   CONFIG_HAZARD_DETECTION = 1'b1;
    
    //-------------------------------------------------------------------------
    // Cache Configuration (Using structured types)
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Small cache configuration for area optimization
    
    // L1 Instruction Cache - 8KB, 2-way
    parameter cache_config_t CONFIG_L1_ICACHE = '{
        size:            8 * 1024,           // 8KB
        ways:            2,                  // 2-way
        line_size:       32,                 // 32-byte lines
        replacement:     REPLACE_FIFO,       // Simple FIFO
        write_policy:    WRITE_THROUGH,      // Read-only
        write_allocate:  1'b0,               // N/A for I-cache
        ecc_enable:      1'b0,               // No ECC (save area)
        prefetch_enable: 1'b0,               // No prefetch
        lock_enable:     1'b0,               // No locking
        hit_latency:     1,                  // 1-cycle hit
        miss_penalty:    10,                 // 10-cycle miss
        fill_burst_size: 4                   // 4-beat burst
    };
    
    // L1 Data Cache - 8KB, 2-way
    parameter cache_config_t CONFIG_L1_DCACHE = '{
        size:            8 * 1024,           // 8KB
        ways:            2,                  // 2-way
        line_size:       32,                 // 32-byte lines
        replacement:     REPLACE_FIFO,       // Simple FIFO
        write_policy:    WRITE_THROUGH,      // Write through
        write_allocate:  1'b0,               // No write allocate
        ecc_enable:      1'b0,               // No ECC
        prefetch_enable: 1'b0,               // No prefetch
        lock_enable:     1'b0,               // No locking
        hit_latency:     1,                  // 1-cycle hit
        miss_penalty:    10,                 // 10-cycle miss
        fill_burst_size: 4                   // 4-beat burst
    };
    
    // L2 Cache - Optional, disabled for small profile
    parameter logic CONFIG_L2_ENABLE = 1'b0;
    parameter cache_config_t CONFIG_L2_CACHE = CONFIG_L2_CACHE_DEFAULT;  // Unused
    
    // L3 Cache - Not present
    parameter logic CONFIG_L3_ENABLE = 1'b0;
    parameter cache_config_t CONFIG_L3_CACHE = CONFIG_L3_CACHE_DEFAULT;  // Unused
    
    // Coherency - Not needed for single core
    parameter coherency_config_t CONFIG_COHERENCY = '{
        protocol:         COHERENCY_NONE,    // No coherency needed
        snoop_enable:     1'b0,              // No snooping
        directory_enable: 1'b0,              // No directory
        snoop_filter_size: 0,                // No snoop filter
        coherency_latency: 0                 // N/A
    };
    
    //-------------------------------------------------------------------------
    // Branch Prediction Configuration
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Simple branch prediction for area optimization
    parameter string CONFIG_BRANCH_PREDICTOR_TYPE = "BIMODAL";
    parameter integer CONFIG_BTB_ENTRIES = 32;     // Small BTB
    parameter integer CONFIG_BHT_ENTRIES = 128;    // Small BHT
    parameter integer CONFIG_PHT_ENTRIES = 0;      // Not used in bimodal
    parameter integer CONFIG_RSB_ENTRIES = 4;      // Small return stack
    
    //-------------------------------------------------------------------------
    // Memory System Configuration
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Simple memory interface configuration
    parameter string CONFIG_MEMORY_PROTOCOL = "AXI4_LITE";  // Simpler protocol
    parameter integer CONFIG_AXI_ID_WIDTH = 2;              // Minimal ID width
    parameter integer CONFIG_AXI_DATA_WIDTH = 32;           // 32-bit data
    parameter integer CONFIG_AXI_MAX_OUTSTANDING = 2;       // Limited outstanding
    
    // Memory timing (relaxed for FPGA)
    parameter integer CONFIG_MEMORY_LATENCY = 20;           // Higher latency OK
    parameter integer CONFIG_MEMORY_BURST_SIZE = 4;         // Small bursts
    
    //-------------------------------------------------------------------------
    // Functional Units Configuration
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Minimal functional units for area savings
    parameter integer CONFIG_NUM_ALU_UNITS = 1;    // Single ALU
    parameter integer CONFIG_NUM_MULT_UNITS = 1;   // Single multiplier
    parameter integer CONFIG_NUM_DIV_UNITS = 1;    // Single divider
    parameter integer CONFIG_DIV_LATENCY = 32;     // Standard division
    
    //-------------------------------------------------------------------------
    // Power and Clock Configuration
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - FPGA-optimized power configuration
    parameter logic CONFIG_CLOCK_GATING_ENABLE = 1'b0;     // No clock gating
    parameter logic CONFIG_POWER_GATING_ENABLE = 1'b0;     // No power gating
    parameter integer CONFIG_TARGET_FREQUENCY_MHZ = 50;     // Conservative 50MHz
    
    //-------------------------------------------------------------------------
    // Debug Configuration
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Minimal debug features
    parameter logic CONFIG_DEBUG_ENABLE = 1'b1;
    parameter integer CONFIG_DEBUG_BREAKPOINTS = 2;         // 2 breakpoints
    parameter integer CONFIG_DEBUG_WATCHPOINTS = 2;         // 2 watchpoints
    parameter logic CONFIG_TRACE_ENABLE = 1'b0;            // No trace (save area)
    
    //-------------------------------------------------------------------------
    // Verification Configuration
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Basic verification features
    parameter logic CONFIG_ASSERTIONS_ENABLE = 1'b1;
    parameter logic CONFIG_COVERAGE_ENABLE = 1'b0;         // Coverage off by default
    parameter integer CONFIG_TIMEOUT_CYCLES = 10000;       // Shorter timeout
    
    //-------------------------------------------------------------------------
    // FPGA-Specific Optimizations
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - FPGA technology mapping hints
    parameter logic CONFIG_USE_FPGA_PRIMITIVES = 1'b1;     // Use FPGA resources
    parameter logic CONFIG_USE_BLOCK_RAM = 1'b1;           // Use BRAM for caches
    parameter logic CONFIG_USE_DSP_SLICES = 1'b1;          // Use DSP for multiply
    parameter string CONFIG_FPGA_FAMILY = "XILINX_7SERIES"; // Target family
    
    //-------------------------------------------------------------------------
    // Feature Enables (Minimal for small profile)
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Feature selection for small implementation
    parameter logic CONFIG_M_EXTENSION = 1'b1;              // Include multiply/divide
    parameter logic CONFIG_C_EXTENSION = 1'b0;              // No compressed instructions
    parameter logic CONFIG_F_EXTENSION = 1'b0;              // No floating point
    parameter logic CONFIG_VIRTUAL_MEMORY = 1'b0;           // No MMU
    parameter logic CONFIG_HYPERVISOR = 1'b0;               // No hypervisor support
    
    //-------------------------------------------------------------------------
    // Profile Validation
    //-------------------------------------------------------------------------
    // AI_TAG: FUNCTION - Validate small profile configuration
    function automatic logic validate_small_profile();
        logic valid;
        valid = 1'b1;
        
        // Validate cache configurations
        if (!validate_cache_config(CONFIG_L1_ICACHE)) begin
            $error("Invalid L1 I-cache configuration");
            valid = 1'b0;
        end
        
        if (!validate_cache_config(CONFIG_L1_DCACHE)) begin
            $error("Invalid L1 D-cache configuration");
            valid = 1'b0;
        end
        
        // Check consistency
        if (CONFIG_NUM_CORES != 1) begin
            $error("Small profile must be single-core");
            valid = 1'b0;
        end
        
        if (CONFIG_TARGET_FREQUENCY_MHZ > 100) begin
            $warning("Target frequency may be too high for small FPGA");
        end
        
        return valid;
    endfunction
    
    // Perform validation at compile time
    initial begin
        assert(validate_small_profile()) 
            else $fatal("Small profile validation failed");
    end

endpackage : riscv_profile_small

//=============================================================================
// Dependencies: riscv_base_pkg, riscv_cache_config_pkg
//
// Instantiated In:
//   - System top-level configuration
//   - Build scripts for small targets
//
// Performance:
//   - Critical Path: N/A (package only)
//   - Max Frequency: 50MHz (target)
//   - Area: Optimized for minimal area
//
// Verification Coverage:
//   - Code Coverage: N/A
//   - Functional Coverage: N/A
//   - Branch Coverage: N/A
//
// Synthesis:
//   - Target Technology: FPGA (Xilinx 7-Series)
//   - Synthesis Tool: Vivado
//   - Clock Domains: 1
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: N/A
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author         | Description
//=============================================================================
// 1.0.0   | 2025-01-28 | DesignAI      | Initial release
//=============================================================================