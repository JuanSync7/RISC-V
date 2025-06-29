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
        addr_t                      addr;
        logic                       write;
        word_t                      data;
        logic [3:0]                 strb;
        logic [3:0]                 id;
        logic [CORE_ID_WIDTH-1:0]   source_id;
        logic                       coherent;
        logic [7:0]                 burst_len;
        logic                       burst_last;
    } memory_req_t;

    typedef struct packed {
        word_t                      data;
        logic [3:0]                 id;
        logic                       error;
        logic                       last;
    } memory_rsp_t;

endpackage : riscv_mem_types_pkg 