//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-28
//
// File: riscv_memory_types_pkg.sv
// Module: riscv_memory_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   This package contains memory system type definitions for the RISC-V
//   processor, including cache types, memory request/response structures,
//   and coherency protocol types.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_memory_types_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    localparam integer XLEN = CONFIG_XLEN;
    localparam integer ADDR_WIDTH = CONFIG_ADDR_WIDTH;
    localparam integer CORE_ID_WIDTH = $clog2(CONFIG_NUM_CORES);
    localparam integer DEFAULT_CACHE_LINE_SIZE = CONFIG_CACHE_LINE_SIZE;

    // Derived parameters for cache line structure (assuming a generic cache)
    // These are placeholders and should ideally be passed as parameters to cache modules
    // or derived within cache-specific packages.
    localparam integer INDEX_BITS = 6; // Example value, should be dynamic
    localparam integer OFFSET_BITS = $clog2(DEFAULT_CACHE_LINE_SIZE);
    localparam integer TAG_BITS = ADDR_WIDTH - INDEX_BITS - OFFSET_BITS;

    //-------------------------------------------------------------------------
    // Cache Coherence and Memory Types
    //-------------------------------------------------------------------------
    typedef enum logic [1:0] {
        I, // Invalid
        S, // Shared
        E, // Exclusive
        M  // Modified
    } cache_state_t;

    typedef enum logic [1:0] {
        COHERENCY_REQ_READ,
        COHERENCY_REQ_WRITE,
        COHERENCY_REQ_INVALIDATE,
        COHERENCY_REQ_UPGRADE
    } coherency_req_type_e;

    typedef struct packed {
        addr_t                      addr;           // Memory address
        logic                       write;          // 1=write, 0=read
        word_t                      data;           // Write data for the current beat
        logic [3:0]                 strb;           // Write strobes
        logic [3:0]                 id;             // Transaction ID
        logic [CORE_ID_WIDTH-1:0]   source_id;      // ID of the core/master initiating the request
        logic                       coherent;       // Request requires coherency management
        logic [7:0]                 burst_len;      // Number of beats in the burst (for cache lines)
        logic                       burst_last;     // Indicates the last beat of a request burst
        logic                       cacheable;      // Cacheable transaction
        logic [2:0]                 prot;           // Protection level
        logic [2:0]                 size;           // Deprecated in favor of burst, but kept for compatibility
    } memory_req_t;

    typedef struct packed {
        word_t                      data;           // Read data for the current beat
        logic [3:0]                 id;             // Transaction ID
        logic                       error;          // Error flag
        logic                       last;           // Indicates the last beat of a response burst
    } memory_rsp_t;

    //-------------------------------------------------------------------------
    // Cache System Types
    //-------------------------------------------------------------------------
    typedef struct packed {
        logic                    valid;      // Valid bit
        logic [TAG_BITS-1:0]     tag;        // Tag bits (calculated per cache)
        word_t                   data [DEFAULT_CACHE_LINE_SIZE/4-1:0];  // Data array
        logic                    dirty;      // Dirty bit for write-back
        logic                    lru;        // LRU bit (for 2-way cache)
    } cache_line_t;

    typedef enum logic [2:0] {
        CACHE_IDLE,           // Ready for new requests
        CACHE_LOOKUP,         // Performing cache lookup
        CACHE_HIT,            // Cache hit, returning data
        CACHE_MISS,           // Cache miss, initiating fill
        CACHE_FILL,           // Filling cache line from memory
        CACHE_WRITEBACK,      // Writing back dirty line
        CACHE_FLUSH           // Flushing cache
    } cache_state_e;

    typedef struct packed {
        logic        valid;
        addr_t       addr;
        logic [2:0]  size;
        logic        write;
        word_t       data;
        logic [3:0]  strb;
        logic [3:0]  id;
    } cache_req_t;

    typedef struct packed {
        logic        valid;
        word_t       data;
        logic        hit;
        logic        error;
        logic [3:0]  id;
    } cache_rsp_t;

    typedef struct packed {
        logic [31:0] hits;
        logic [31:0] misses;
        logic [31:0] evictions;
        logic [31:0] writebacks;
        logic [31:0] total_accesses;
    } cache_stats_t;

    typedef struct packed {
        integer size;
        integer ways;
        integer line_size;
        integer sets;
        integer index_bits;
        integer offset_bits;
        integer tag_bits;
    } cache_config_t;

    typedef struct packed {
        logic [TAG_BITS-1:0]     tag;
        logic [INDEX_BITS-1:0]   index;
        logic [OFFSET_BITS-1:0]  offset;
    } cache_addr_t;

    typedef enum logic [1:0] {
        REPLACEMENT_LRU,     // Least Recently Used
        REPLACEMENT_RANDOM,  // Random replacement
        REPLACEMENT_FIFO,    // First In, First Out
        REPLACEMENT_PLRU     // Pseudo-LRU
    } replacement_policy_e;

    typedef enum logic [0:0] {
        WRITE_THROUGH,       // Write-through
        WRITE_BACK          // Write-back
    } write_policy_e;

    typedef enum logic [0:0] {
        ALLOCATE_ON_WRITE,  // Allocate on write
        NO_ALLOCATE_ON_WRITE // No allocate on write
    } allocation_policy_e;

    typedef enum logic [1:0] {
        CACHE_INVALID   = 2'b00,  // Invalid - no valid copy
        CACHE_SHARED    = 2'b01,  // Shared - multiple cores may have copy
        CACHE_EXCLUSIVE = 2'b10,  // Exclusive - only this core has copy
        CACHE_MODIFIED  = 2'b11   // Modified - this core has modified copy
    } cache_coherency_state_e;

    typedef enum logic [1:0] {
        SNOOP_NONE,
        SNOOP_READ,
        SNOOP_WRITE,
        SNOOP_INVALIDATE
    } snoop_op_e;

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

    //-------------------------------------------------------------------------
    // Cache System Functions
    //-------------------------------------------------------------------------
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

endpackage : riscv_memory_types_pkg

`default_nettype wire 