//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: sync_primitives_if.sv
// Module: sync_primitives_if
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Interface for hardware synchronization primitives, primarily hardware
//   barriers. This allows multiple cores to synchronize their execution at a
//   specific point in a program, managed by a central synchronization module.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Supports a configurable number of hardware barriers.
// AI_TAG: FEATURE - Supports a configurable number of synchronizing cores.
// AI_TAG: FEATURE - Provides full ready/valid handshake mechanism for barrier arrival and release.

import riscv_core_pkg::*;

interface sync_primitives_if #(
    parameter integer NUM_CORES    = MAX_CORES,     // AI_TAG: PARAM_DESC - The total number of cores participating in synchronization.
                                            // AI_TAG: PARAM_USAGE - Determines the dimension of the communication arrays.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be > 1.
    parameter integer NUM_BARRIERS = DEFAULT_NUM_BARRIERS,     // AI_TAG: PARAM_DESC - The number of available hardware barriers.
                                            // AI_TAG: PARAM_USAGE - Determines the width of the barrier ID signal.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2.
    parameter integer BARRIER_ID_WIDTH = (NUM_BARRIERS > 1) ? $clog2(NUM_BARRIERS) : 1, // AI_TAG: PARAM_DESC - The bit-width required to identify a barrier.
                                                                                       // AI_TAG: PARAM_USAGE - Automatically calculated from NUM_BARRIERS.
                                                                                       // AI_TAG: PARAM_CONSTRAINTS - N/A
    parameter integer DATA_WIDTH = XLEN
) (
    input logic clk_i,   // AI_TAG: PORT_DESC - Main system clock for the interface.
                         // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input logic rst_ni   // AI_TAG: PORT_DESC - Asynchronous, active-low reset.
                         // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
);

    //---------------------------------------------------------------------------
    // Barrier Synchronization Signals
    // A core must connect to the signals at the index corresponding to its CORE_ID.
    // Example for core 'i': arrive_valid_w[i], arrive_ready_w[i], etc.
    //---------------------------------------------------------------------------

    // From Core 'i' to Sync Manager: Core 'i' has arrived at barrier_id_w[i].
    logic [NUM_CORES-1:0]                   arrive_valid_w;     // AI_TAG: PORT_DESC - Core 'i' asserts to signal arrival at a barrier.
    logic [NUM_CORES-1:0]                   arrive_ready_w;     // AI_TAG: PORT_DESC - Sync Manager asserts when it can accept the arrival signal.
    logic [NUM_CORES-1:0] [BARRIER_ID_WIDTH-1:0] barrier_id_w;  // AI_TAG: PORT_DESC - The ID of the barrier the core has arrived at.

    // From Sync Manager to Core 'i': All cores have arrived, release from barrier.
    logic [NUM_CORES-1:0]                   release_valid_w;    // AI_TAG: PORT_DESC - Sync Manager asserts to release core 'i' from the barrier.
    logic [NUM_CORES-1:0]                   release_ready_w;    // AI_TAG: PORT_DESC - Core 'i' asserts to acknowledge release and continue execution.


    //---------------------------------------------------------------------------
    // Modports
    //---------------------------------------------------------------------------
    // NOTE: There is no 'core' modport. A core module should connect directly
    // to its indexed slice of the signals above. This avoids ambiguity and
    // provides a clean connection.

    // Modport for the central synchronization manager
    modport manager (
        input  arrive_valid_w,
        output arrive_ready_w,
        input  barrier_id_w,
        output release_valid_w,
        input  release_ready_w
    );

endinterface : sync_primitives_if

//=============================================================================
// Dependencies: None
//
// Performance:
//   - Critical Path: N/A (Interface definition only)
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
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: N/A
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.1.0   | 2025-06-28 | DesignAI           | Added full handshake, removed core modport for clarity, added docs.
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//=============================================================================

`default_nettype wire 