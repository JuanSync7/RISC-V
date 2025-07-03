//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_mem_types_pkg.sv
// Module: riscv_mem_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains all shared parameters, data types, and enumerations related to
//   the memory hierarchy, including caches and coherency protocols.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_mem_types_pkg;

    import riscv_types_pkg::*;

    //---------------------------------------------------------------------------
    // 1. Memory and Cache Parameters
    //---------------------------------------------------------------------------
    parameter integer MAX_CORES = 4;
    parameter integer CORE_ID_WIDTH = $clog2(MAX_CORES);
    parameter integer CACHE_LINE_SIZE = 64; // Bytes

    //---------------------------------------------------------------------------
    // 2. Cache Coherence Definitions
    //---------------------------------------------------------------------------
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

    //---------------------------------------------------------------------------
    // 3. Memory Request/Response Structures
    //---------------------------------------------------------------------------
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

endpackage : riscv_mem_types_pkg
//=============================================================================
// Dependencies: riscv_types_pkg.sv
//
// Performance:
//   - Critical Path: N/A (package file)
//   - Max Frequency: N/A (package file)
//   - Area: N/A (package file)
//
// Verification Coverage:
//   - Code Coverage: N/A
//   - Functional Coverage: N/A
//   - Branch Coverage: N/A
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//
// Testing:
//   - Testbench: N/A
//   - Test Vectors: N/A
//   - Simulation Time: N/A
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.1.0   | 2025-01-27 | DesignAI           | Consolidated memory types to this package
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//============================================================================= 