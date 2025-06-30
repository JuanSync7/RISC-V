//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_memory_config_pkg.sv
// Module: riscv_memory_config_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   This package centralizes all memory-related configurations for the RISC-V
//   processor, including cache hierarchy, memory protocols, and prefetcher settings.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_memory_config_pkg;

    // It's expected that the core config is available
    import riscv_core_config_pkg::*;

    //---------------------------------------------------------------------------
    // 5. Cache System Configuration
    //---------------------------------------------------------------------------
    parameter integer TAG_BITS = 20;
    parameter integer INDEX_BITS = 6;
    parameter integer OFFSET_BITS = 6;
    parameter bit ENABLE_L2_CACHE = 1;                     // Enable L2 cache
    parameter bit ENABLE_L3_CACHE = 1;                     // Enable L3 cache
    
    // Cache sizes (in bytes)
    parameter integer DEFAULT_L1_ICACHE_SIZE = 16*1024;    // 16KB
    parameter integer DEFAULT_L1_DCACHE_SIZE = 16*1024;    // 16KB
    parameter integer DEFAULT_L2_CACHE_SIZE = 256*1024;    // 256KB
    parameter integer DEFAULT_L3_CACHE_SIZE = 2*1024*1024; // 2MB
    
    // Cache associativity
    parameter integer DEFAULT_L1_ICACHE_WAYS = 2;
    parameter integer DEFAULT_L1_DCACHE_WAYS = 2;
    parameter integer DEFAULT_L2_CACHE_WAYS = 8;
    parameter integer DEFAULT_L3_CACHE_WAYS = 16;
    
    // Cache line size
    parameter integer DEFAULT_CACHE_LINE_SIZE = 64;        // 64 bytes per line
    
    //---------------------------------------------------------------------------
    // 6. Cache Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_NUM_CACHE_LEVELS = 3;        // Number of cache levels to optimize

    // Instruction Cache (L1)
    parameter integer L1_ICACHE_SIZE = 16 * 1024;        // 16 KB
    
    //---------------------------------------------------------------------------
    // 8. Memory System Configuration
    //---------------------------------------------------------------------------
    // Prefetch unit configuration
    parameter integer DEFAULT_STRIDE_TABLE_SIZE = 64;
    parameter integer DEFAULT_PREFETCH_DISTANCE = 4;
    parameter integer DEFAULT_L2_PREFETCH_DEPTH = 2;
    parameter integer DEFAULT_L2_STRIDE_TABLE_SIZE = 16;
    parameter integer DEFAULT_L2_PREFETCH_CONFIDENCE_THRESHOLD = 3;
    
    // Memory protocol configuration
    parameter integer DEFAULT_AXI4_ID_WIDTH = 4;
    parameter integer DEFAULT_AXI4_ADDR_WIDTH = 32;
    parameter integer DEFAULT_AXI4_DATA_WIDTH = 32;
    parameter integer DEFAULT_AXI4_STRB_WIDTH = DEFAULT_AXI4_DATA_WIDTH/8;
    parameter integer DEFAULT_AXI4_USER_WIDTH = 1;
    parameter string DEFAULT_MEMORY_PROTOCOL = "AXI4";      // Default memory protocol
    parameter integer DEFAULT_AXI4_MAX_OUTSTANDING = 16;    // AXI4 outstanding transactions
    
    parameter integer DEFAULT_CHI_DATA_WIDTH = 128;
    parameter integer DEFAULT_CHI_ADDR_WIDTH = 48;
    parameter integer DEFAULT_CHI_NODEID_WIDTH = 7;
    parameter integer DEFAULT_CHI_TXNID_WIDTH = 8;
    
    parameter integer DEFAULT_TL_DATA_WIDTH = 64;
    parameter integer DEFAULT_TL_ADDR_WIDTH = 32;
    parameter integer DEFAULT_TL_SOURCE_WIDTH = 4;
    parameter integer DEFAULT_TL_SINK_WIDTH = 4;
    parameter integer DEFAULT_TL_SIZE_WIDTH = 4;
    
    // Inter-core communication
    parameter integer DEFAULT_MSG_WIDTH = 32;           // Inter-core message width
    parameter integer DEFAULT_NUM_BARRIERS = 8;         // Hardware barrier count
    
    //---------------------------------------------------------------------------
    // 14. Configuration Validation Functions
    //---------------------------------------------------------------------------
    // Function to validate cache configuration
    function automatic logic validate_cache_config(
        input integer cache_size,
        input integer line_size,
        input integer ways
    );
        // Cache size must be power of 2
        if ((cache_size & (cache_size - 1)) != 0) return 1'b0;
        // Line size must be power of 2 and >= 4 bytes
        if ((line_size & (line_size - 1)) != 0 || line_size < 4) return 1'b0;
        // Ways must be power of 2
        if ((ways & (ways - 1)) != 0) return 1'b0;
        // Cache size must be >= line_size * ways
        if (cache_size < (line_size * ways)) return 1'b0;
        return 1'b1;
    endfunction
    
    // Function to calculate cache parameters
    function automatic integer calc_cache_sets(
        input integer cache_size,
        input integer line_size,
        input integer ways
    );
        return cache_size / (line_size * ways);
    endfunction

    //-------------------------------------------------------------------------
    // Cache Configuration Parameters
    //-------------------------------------------------------------------------
    
    // AI_TAG: PARAM - Maximum number of cache clusters supported
    parameter integer MAX_CACHE_CLUSTERS = 4;
    parameter integer MAX_L2_INSTANCES = 4;
    parameter integer MAX_L3_INSTANCES = 2;
    parameter integer MAX_MEMORY_CONTROLLERS = 2;

    //---------------------------------------------------------------------------
    // Memory Address Map Configuration
    //---------------------------------------------------------------------------
    // Exception vector memory region
    parameter logic [31:0] EXCEPTION_VECTOR_BASE = 32'h0000_0000;
    parameter logic [31:0] EXCEPTION_VECTOR_SIZE = 32'h0000_1000;    // 4KB exception vector space
    
    // Peripheral memory region  
    parameter logic [31:0] PERIPHERAL_BASE = 32'hF000_0000;
    parameter logic [31:0] PERIPHERAL_SIZE = 32'h1000_0000;          // 256MB peripheral space
    
    // Cache writeback region
    parameter logic [31:0] CACHE_WB_BASE = 32'hFFFF_FF00;
    parameter logic [31:0] CACHE_WB_SIZE = 32'h0000_0100;            // 256B cache writeback region
    
    // Main memory region
    parameter logic [31:0] MAIN_MEMORY_BASE = 32'h1000_0000;
    parameter logic [31:0] MAIN_MEMORY_SIZE = 32'hE000_0000;         // ~3.5GB main memory
    
    //---------------------------------------------------------------------------
    // QoS Memory Latency Configuration  
    //---------------------------------------------------------------------------
    // Exception-related QoS latency limits (in cycles)
    parameter integer QOS_DEBUG_MAX_LATENCY = 5;                     // Debug access max latency
    parameter integer QOS_INTERRUPT_MAX_LATENCY = 10;                // Interrupt handling max latency
    parameter integer QOS_EXCEPTION_ACCESS_FAULT_LATENCY = 10;       // Access fault exception latency
    parameter integer QOS_EXCEPTION_BREAKPOINT_LATENCY = 5;          // Breakpoint exception latency  
    parameter integer QOS_EXCEPTION_ECALL_LATENCY = 15;              // ECALL exception latency
    parameter integer QOS_EXCEPTION_DEFAULT_LATENCY = 20;            // Default exception latency

endpackage : riscv_memory_config_pkg
