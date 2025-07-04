//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: riscv_cache_config_pkg.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: riscv_cache_config_pkg
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-28
// DESCRIPTION: Cache system configuration package with structured parameters.
// PRIMARY_PURPOSE: Centralize cache-related configuration parameters and types.
// ROLE_IN_SYSTEM: Provides cache configuration to all memory subsystem modules.
// PROBLEM_SOLVED: Enables flexible cache configuration with validation.
// MODULE_TYPE: Package
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V Privileged Specification v1.12
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

package riscv_cache_config_pkg;

    import riscv_base_pkg::*;

    //-------------------------------------------------------------------------
    // Cache Configuration Types
    //-------------------------------------------------------------------------
    // AI_TAG: FEATURE - Provides structured cache configuration with validation
    
    // Cache configuration structure
    typedef struct packed {
        // Basic parameters
        logic [31:0] size;           // Cache size in bytes
        logic [7:0]  ways;           // Number of ways (associativity)
        logic [7:0]  line_size;      // Cache line size in bytes
        
        // Policy configuration
        logic [2:0]  replacement;    // Replacement policy (see enum below)
        logic [2:0]  write_policy;   // Write policy (see enum below)
        logic        write_allocate; // Write allocate enable
        
        // Features
        logic        ecc_enable;     // ECC protection enable
        logic        prefetch_enable;// Hardware prefetch enable
        logic        lock_enable;    // Cache line locking enable
        
        // Performance tuning
        logic [7:0]  hit_latency;    // Hit latency in cycles
        logic [7:0]  miss_penalty;   // Miss penalty in cycles
        logic [7:0]  fill_burst_size;// Fill burst size
    } cache_config_t;
    
    // Cache coherency configuration
    typedef struct packed {
        logic [2:0]  protocol;       // Coherency protocol (see enum below)
        logic        snoop_enable;   // Snoop enable
        logic        directory_enable;// Directory-based coherence
        logic [15:0] snoop_filter_size;// Snoop filter entries
        logic [7:0]  coherency_latency;// Coherency operation latency
    } coherency_config_t;
    
    //-------------------------------------------------------------------------
    // Cache Policy Enumerations
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Cache replacement policy options
    typedef enum logic [2:0] {
        REPLACE_LRU      = 3'b000,  // Least Recently Used
        REPLACE_FIFO     = 3'b001,  // First In First Out
        REPLACE_RANDOM   = 3'b010,  // Random replacement
        REPLACE_PLRU     = 3'b011,  // Pseudo-LRU
        REPLACE_MRU      = 3'b100   // Most Recently Used (testing)
    } replacement_policy_e;
    
    // AI_TAG: PARAM_DESC - Cache write policy options
    typedef enum logic [2:0] {
        WRITE_THROUGH    = 3'b000,  // Write through
        WRITE_BACK       = 3'b001,  // Write back
        WRITE_AROUND     = 3'b010   // Write around (bypass cache)
    } write_policy_e;
    
    // AI_TAG: PARAM_DESC - Cache coherency protocol options
    typedef enum logic [2:0] {
        COHERENCY_NONE   = 3'b000,  // No coherency
        COHERENCY_MSI    = 3'b001,  // Modified-Shared-Invalid
        COHERENCY_MESI   = 3'b010,  // Modified-Exclusive-Shared-Invalid
        COHERENCY_MOESI  = 3'b011,  // Modified-Owned-Exclusive-Shared-Invalid
        COHERENCY_CHI    = 3'b100   // ARM CHI protocol
    } coherency_protocol_e;
    
    //-------------------------------------------------------------------------
    // Default Cache Configurations
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Default L1 instruction cache configuration
    parameter cache_config_t CONFIG_L1_ICACHE_DEFAULT = '{
        size:            32 * 1024,          // 32KB
        ways:            2,                  // 2-way set associative
        line_size:       64,                 // 64-byte cache lines
        replacement:     REPLACE_LRU,        // LRU replacement
        write_policy:    WRITE_THROUGH,      // Write through (read-only for I-cache)
        write_allocate:  1'b0,               // No write allocate (read-only)
        ecc_enable:      1'b1,               // ECC protection enabled
        prefetch_enable: 1'b1,               // Prefetch enabled
        lock_enable:     1'b0,               // No locking
        hit_latency:     1,                  // 1-cycle hit
        miss_penalty:    20,                 // 20-cycle miss penalty
        fill_burst_size: 8                   // 8-beat burst
    };
    
    // AI_TAG: PARAM_DESC - Default L1 data cache configuration
    parameter cache_config_t CONFIG_L1_DCACHE_DEFAULT = '{
        size:            32 * 1024,          // 32KB
        ways:            4,                  // 4-way set associative
        line_size:       64,                 // 64-byte cache lines
        replacement:     REPLACE_LRU,        // LRU replacement
        write_policy:    WRITE_BACK,         // Write back
        write_allocate:  1'b1,               // Write allocate enabled
        ecc_enable:      1'b1,               // ECC protection enabled
        prefetch_enable: 1'b1,               // Prefetch enabled
        lock_enable:     1'b0,               // No locking
        hit_latency:     1,                  // 1-cycle hit
        miss_penalty:    20,                 // 20-cycle miss penalty
        fill_burst_size: 8                   // 8-beat burst
    };
    
    // AI_TAG: PARAM_DESC - Default L2 cache configuration
    parameter cache_config_t CONFIG_L2_CACHE_DEFAULT = '{
        size:            256 * 1024,         // 256KB
        ways:            8,                  // 8-way set associative
        line_size:       64,                 // 64-byte cache lines
        replacement:     REPLACE_PLRU,       // Pseudo-LRU (lower complexity)
        write_policy:    WRITE_BACK,         // Write back
        write_allocate:  1'b1,               // Write allocate enabled
        ecc_enable:      1'b1,               // ECC protection enabled
        prefetch_enable: 1'b1,               // Prefetch enabled
        lock_enable:     1'b1,               // Locking supported
        hit_latency:     5,                  // 5-cycle hit
        miss_penalty:    50,                 // 50-cycle miss penalty
        fill_burst_size: 16                  // 16-beat burst
    };
    
    // AI_TAG: PARAM_DESC - Default L3 cache configuration
    parameter cache_config_t CONFIG_L3_CACHE_DEFAULT = '{
        size:            2 * 1024 * 1024,    // 2MB
        ways:            16,                 // 16-way set associative
        line_size:       64,                 // 64-byte cache lines
        replacement:     REPLACE_PLRU,       // Pseudo-LRU
        write_policy:    WRITE_BACK,         // Write back
        write_allocate:  1'b1,               // Write allocate enabled
        ecc_enable:      1'b1,               // ECC protection enabled
        prefetch_enable: 1'b1,               // Prefetch enabled
        lock_enable:     1'b1,               // Locking supported
        hit_latency:     20,                 // 20-cycle hit
        miss_penalty:    100,                // 100-cycle miss penalty
        fill_burst_size: 32                  // 32-beat burst
    };
    
    // AI_TAG: PARAM_DESC - Default coherency configuration
    parameter coherency_config_t CONFIG_COHERENCY_DEFAULT = '{
        protocol:         COHERENCY_MESI,    // MESI protocol
        snoop_enable:     1'b1,              // Snooping enabled
        directory_enable: 1'b0,              // Directory disabled (bus-based)
        snoop_filter_size: 1024,             // 1K entry snoop filter
        coherency_latency: 10                // 10-cycle coherency latency
    };
    
    //-------------------------------------------------------------------------
    // Configuration Presets
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Small configuration for area-constrained designs
    parameter cache_config_t CONFIG_L1_CACHE_SMALL = '{
        size:            8 * 1024,           // 8KB
        ways:            2,                  // 2-way
        line_size:       32,                 // 32-byte lines
        replacement:     REPLACE_FIFO,       // Simple FIFO
        write_policy:    WRITE_THROUGH,      // Write through
        write_allocate:  1'b0,               // No write allocate
        ecc_enable:      1'b0,               // No ECC (save area)
        prefetch_enable: 1'b0,               // No prefetch
        lock_enable:     1'b0,               // No locking
        hit_latency:     1,                  // 1-cycle hit
        miss_penalty:    10,                 // 10-cycle miss
        fill_burst_size: 4                   // 4-beat burst
    };
    
    // AI_TAG: PARAM_DESC - Large configuration for high-performance designs
    parameter cache_config_t CONFIG_L1_CACHE_LARGE = '{
        size:            64 * 1024,          // 64KB
        ways:            8,                  // 8-way
        line_size:       128,                // 128-byte lines
        replacement:     REPLACE_LRU,        // Full LRU
        write_policy:    WRITE_BACK,         // Write back
        write_allocate:  1'b1,               // Write allocate
        ecc_enable:      1'b1,               // ECC enabled
        prefetch_enable: 1'b1,               // Prefetch enabled
        lock_enable:     1'b1,               // Locking enabled
        hit_latency:     2,                  // 2-cycle hit
        miss_penalty:    30,                 // 30-cycle miss
        fill_burst_size: 16                  // 16-beat burst
    };
    
    //-------------------------------------------------------------------------
    // Validation Functions
    //-------------------------------------------------------------------------
    // AI_TAG: FUNCTION - Validate cache configuration parameters
    function automatic logic validate_cache_config(
        input cache_config_t config
    );
        logic valid;
        valid = 1'b1;
        
        // Size must be power of 2 and >= 1KB
        if ((config.size & (config.size - 1)) != 0 || config.size < 1024) begin
            valid = 1'b0;
        end
        
        // Ways must be power of 2 and <= 32
        if ((config.ways & (config.ways - 1)) != 0 || config.ways > 32) begin
            valid = 1'b0;
        end
        
        // Line size must be power of 2 and >= 16 bytes
        if ((config.line_size & (config.line_size - 1)) != 0 || config.line_size < 16) begin
            valid = 1'b0;
        end
        
        // Cache size must be >= ways * line_size
        if (config.size < (config.ways * config.line_size)) begin
            valid = 1'b0;
        end
        
        // Latency checks
        if (config.hit_latency == 0 || config.miss_penalty <= config.hit_latency) begin
            valid = 1'b0;
        end
        
        return valid;
    endfunction
    
    // AI_TAG: FUNCTION - Calculate cache parameters
    function automatic integer calc_cache_sets(
        input cache_config_t config
    );
        return config.size / (config.line_size * config.ways);
    endfunction
    
    function automatic integer calc_cache_index_bits(
        input cache_config_t config
    );
        return $clog2(calc_cache_sets(config));
    endfunction
    
    function automatic integer calc_cache_offset_bits(
        input cache_config_t config
    );
        return $clog2(config.line_size);
    endfunction
    
    function automatic integer calc_cache_tag_bits(
        input cache_config_t config,
        input integer addr_width = 32
    );
        integer index_bits, offset_bits;
        index_bits = calc_cache_index_bits(config);
        offset_bits = calc_cache_offset_bits(config);
        return addr_width - index_bits - offset_bits;
    endfunction
    
    //-------------------------------------------------------------------------
    // Cache Topology Configuration
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Cache topology options
    typedef enum logic [2:0] {
        TOPOLOGY_UNIFIED    = 3'b000,  // Unified cache hierarchy
        TOPOLOGY_CLUSTERED  = 3'b001,  // Clustered caches
        TOPOLOGY_NUMA       = 3'b010,  // NUMA-aware topology
        TOPOLOGY_DISTRIBUTED = 3'b011  // Distributed caches
    } cache_topology_e;
    
    // Cache cluster configuration
    typedef struct packed {
        logic [7:0]  clusters;           // Number of cache clusters
        logic [7:0]  cores_per_cluster;  // Cores per cluster
        logic        numa_enable;        // NUMA support
        logic        adaptive_cluster;   // Dynamic clustering
        logic [2:0]  interconnect_type;  // Interconnect type
    } cache_cluster_config_t;
    
    // AI_TAG: PARAM_DESC - Default cache topology configuration
    parameter cache_cluster_config_t CONFIG_CACHE_TOPOLOGY_DEFAULT = '{
        clusters:          1,            // Single cluster
        cores_per_cluster: 4,            // 4 cores per cluster
        numa_enable:       1'b0,         // NUMA disabled
        adaptive_cluster:  1'b0,         // Static clustering
        interconnect_type: 3'b000        // Bus interconnect
    };

endpackage : riscv_cache_config_pkg

//=============================================================================
// Dependencies: riscv_base_pkg
//
// Instantiated In:
//   - Memory subsystem modules
//   - Cache implementations
//   - System configuration packages
//
// Performance:
//   - Critical Path: N/A (package only)
//   - Max Frequency: N/A
//   - Area: N/A
//
// Verification Coverage:
//   - Code Coverage: N/A
//   - Functional Coverage: N/A
//   - Branch Coverage: N/A
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: N/A
//   - Clock Domains: N/A
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