//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_cache_types_pkg.sv
// Module: riscv_cache_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains all shared parameters, data types, and enumerations related to
//   the cache hierarchy (L1, L2, L3). This includes cache line structures,
//   state machines, and replacement policies.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_cache_types_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;
    import riscv_mem_types_pkg::*;

    //---------------------------------------------------------------------------
    // 1. Cache Configuration Parameters (now from config package)
    //---------------------------------------------------------------------------
    // All cache configuration parameters are now imported from riscv_config_pkg:
    // DEFAULT_L1_CACHE_SIZE, DEFAULT_L2_CACHE_SIZE, DEFAULT_L3_CACHE_SIZE
    // DEFAULT_L1_CACHE_WAYS, DEFAULT_L2_CACHE_WAYS, DEFAULT_L3_CACHE_WAYS
    // DEFAULT_CACHE_LINE_SIZE

    //---------------------------------------------------------------------------
    // 2. Cache Line Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic                    valid;      // Valid bit
        logic [TAG_BITS-1:0]     tag;        // Tag bits (calculated per cache)
        word_t                   data [DEFAULT_CACHE_LINE_SIZE/4-1:0];  // Data array
        logic                    dirty;      // Dirty bit for write-back
        logic                    lru;        // LRU bit (for 2-way cache)
    } cache_line_t;

    //---------------------------------------------------------------------------
    // 3. Cache State Machine
    //---------------------------------------------------------------------------
    typedef enum logic [2:0] {
        CACHE_IDLE,           // Ready for new requests
        CACHE_LOOKUP,         // Performing cache lookup
        CACHE_HIT,            // Cache hit, returning data
        CACHE_MISS,           // Cache miss, initiating fill
        CACHE_FILL,           // Filling cache line from memory
        CACHE_WRITEBACK,      // Writing back dirty line
        CACHE_FLUSH           // Flushing cache
    } cache_state_e;

    //---------------------------------------------------------------------------
    // 4. Cache Request Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        valid;
        addr_t       addr;
        logic [2:0]  size;
        logic        write;
        word_t       data;
        logic [3:0]  strb;
        logic [3:0]  id;
    } cache_req_t;

    //---------------------------------------------------------------------------
    // 5. Cache Response Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        valid;
        word_t       data;
        logic        hit;
        logic        error;
        logic [3:0]  id;
    } cache_rsp_t;

    //---------------------------------------------------------------------------
    // 6. Cache Statistics
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [31:0] hits;
        logic [31:0] misses;
        logic [31:0] evictions;
        logic [31:0] writebacks;
        logic [31:0] total_accesses;
    } cache_stats_t;

    //---------------------------------------------------------------------------
    // 7. Cache Configuration Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        integer size;
        integer ways;
        integer line_size;
        integer sets;
        integer index_bits;
        integer offset_bits;
        integer tag_bits;
    } cache_config_t;

    //---------------------------------------------------------------------------
    // 8. Cache Address Decomposition
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [TAG_BITS-1:0]     tag;
        logic [INDEX_BITS-1:0]   index;
        logic [OFFSET_BITS-1:0]  offset;
    } cache_addr_t;

    //---------------------------------------------------------------------------
    // 9. Cache Replacement Policy
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        REPLACEMENT_LRU,     // Least Recently Used
        REPLACEMENT_RANDOM,  // Random replacement
        REPLACEMENT_FIFO,    // First In, First Out
        REPLACEMENT_PLRU     // Pseudo-LRU
    } replacement_policy_e;

    //---------------------------------------------------------------------------
    // 10. Cache Write Policy
    //---------------------------------------------------------------------------
    typedef enum logic [0:0] {
        WRITE_THROUGH,       // Write-through
        WRITE_BACK          // Write-back
    } write_policy_e;

    //---------------------------------------------------------------------------
    // 11. Cache Allocation Policy
    //---------------------------------------------------------------------------
    typedef enum logic [0:0] {
        ALLOCATE_ON_WRITE,  // Allocate on write
        NO_ALLOCATE_ON_WRITE // No allocate on write
    } allocation_policy_e;

    //---------------------------------------------------------------------------
    // 12. Cache Coherency States (MESI)
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        CACHE_INVALID   = 2'b00,  // Invalid - no valid copy
        CACHE_SHARED    = 2'b01,  // Shared - multiple cores may have copy
        CACHE_EXCLUSIVE = 2'b10,  // Exclusive - only this core has copy
        CACHE_MODIFIED  = 2'b11   // Modified - this core has modified copy
    } cache_coherency_state_e;

    //---------------------------------------------------------------------------
    // 13. Cache Snoop Operations
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        SNOOP_NONE,
        SNOOP_READ,
        SNOOP_WRITE,
        SNOOP_INVALIDATE
    } snoop_op_e;

    //---------------------------------------------------------------------------
    // 14. Cache Performance Counters
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [31:0] read_hits;
        logic [31:0] read_misses;
        logic [31:0] write_hits;
        logic [31:0] write_misses;
        logic [31:0] evictions;
        logic [31:0] writebacks;
        logic [31:0] snoop_hits;
        logic [31:0] snoop_misses;
    } cache_perf_counters_t;

    //---------------------------------------------------------------------------
    // 15. Cache Configuration Functions
    //---------------------------------------------------------------------------
    function automatic cache_config_t create_cache_config(
        input integer size,
        input integer ways,
        input integer line_size
    );
        cache_config_t config;
        config.size = size;
        config.ways = ways;
        config.line_size = line_size;
        config.sets = size / (line_size * ways);
        config.index_bits = $clog2(config.sets);
        config.offset_bits = $clog2(line_size);
        config.tag_bits = ADDR_WIDTH - config.index_bits - config.offset_bits;
        return config;
    endfunction

    function automatic cache_addr_t decompose_cache_addr(
        input addr_t addr,
        input cache_config_t config
    );
        cache_addr_t result;
        result.offset = addr[config.offset_bits-1:0];
        result.index = addr[config.index_bits+config.offset_bits-1:config.offset_bits];
        result.tag = addr[ADDR_WIDTH-1:config.index_bits+config.offset_bits];
        return result;
    endfunction

    function automatic logic is_cache_aligned(
        input addr_t addr,
        input integer line_size
    );
        return (addr % line_size) == 0;
    endfunction

    function automatic integer get_cache_line_words(input integer line_size);
        return line_size / 4; // Assuming 4 bytes per word
    endfunction

endpackage : riscv_cache_types_pkg 