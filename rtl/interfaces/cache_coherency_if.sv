//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: cache_coherency_if.sv
// Module: cache_coherency_if
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Interface for managing cache coherency between multiple RISC-V cores
//   and the memory hierarchy. It defines the signals for coherency requests,
//   responses, and snooping, based on a MESI-like protocol.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

interface cache_coherency_if #(
    parameter int unsigned NUM_CORES = 4
) (
    input logic clk,
    input logic rst_n
);

    import riscv_mem_types_pkg::*;

    //---------------------------------------------------------------------------
    // Coherency Signals
    //---------------------------------------------------------------------------
    // From Core to Coherency Controller/L2 Cache
    logic                       req_valid   [NUM_CORES];
    logic                       req_ready   [NUM_CORES];
    addr_t                      req_addr    [NUM_CORES];
    coherency_req_type_e        req_type    [NUM_CORES];
    logic [CORE_ID_WIDTH-1:0]   req_source  [NUM_CORES];

    // From Coherency Controller to Core
    logic                       rsp_valid   [NUM_CORES];
    logic                       rsp_ready   [NUM_CORES];
    cache_state_t               rsp_state   [NUM_CORES];
    word_t                      rsp_data    [NUM_CORES][CACHE_LINE_SIZE/4];

    // Snoop signals from Coherency Controller to Core L1 caches
    logic                       snoop_valid [NUM_CORES];
    logic                       snoop_ready [NUM_CORES];
    addr_t                      snoop_addr  [NUM_CORES];
    coherency_req_type_e        snoop_type  [NUM_CORES];

    // Snoop response signals from Core L1 caches to Coherency Controller
    logic                       snoop_rsp_valid [NUM_CORES];
    logic                       snoop_rsp_data_en [NUM_CORES]; // Indicates the response contains data
    word_t                      snoop_rsp_data [NUM_CORES][CACHE_LINE_SIZE/4];


    //---------------------------------------------------------------------------
    // Modports
    //---------------------------------------------------------------------------

    // Modport for a core's L1 cache connecting to the coherency manager
    modport l1_cache_port (
        output req_valid,
        output req_addr,
        output req_type,
        output req_source,
        input  req_ready,

        input  rsp_valid,
        input  rsp_state,
        input  rsp_data,
        output rsp_ready,

        input  snoop_valid,
        input  snoop_addr,
        input  snoop_type,
        output snoop_ready,
        output snoop_rsp_valid,
        output snoop_rsp_data_en,
        output snoop_rsp_data
    );

    // Modport for the central coherency controller (e.g., in L2 cache)
    modport coherency_controller_port (
        input  req_valid,
        input  req_addr,
        input  req_type,
        input  req_source,
        output req_ready,

        output rsp_valid,
        output rsp_state,
        output rsp_data,
        input  rsp_ready,

        output snoop_valid,
        output snoop_addr,
        output snoop_type,
        input  snoop_ready,
        input  snoop_rsp_valid,
        input  snoop_rsp_data_en,
        input  snoop_rsp_data
    );

endinterface : cache_coherency_if

`default_nettype wire 