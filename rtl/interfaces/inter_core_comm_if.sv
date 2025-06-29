//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: inter_core_comm_if.sv
// Module: inter_core_comm_if
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Interface for direct inter-core communication. This interface defines
//   a point-to-point-like network between multiple cores and a central
//   routing/managing entity (the Core Manager). It allows any core to
//   send a message or interrupt signal to any other core in the system.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Provides dedicated send/receive channels for each core.
// AI_TAG: FEATURE - Supports configurable number of cores and message width.
// AI_TAG: FEATURE - Includes ready/valid handshake for all channels for robust flow control.

interface inter_core_comm_if #(
    parameter integer NUM_CORES     = 4,    // AI_TAG: PARAM_DESC - The total number of cores in the system.
                                            // AI_TAG: PARAM_USAGE - Determines the number of communication channels.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be > 1.
    parameter integer MSG_WIDTH     = 32,   // AI_TAG: PARAM_DESC - The bit-width of the message payload.
                                            // AI_TAG: PARAM_USAGE - Defines the width of the send_message and recv_message signals.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be > 0.
    parameter integer CORE_ID_WIDTH = $clog2(NUM_CORES) // AI_TAG: PARAM_DESC - The bit-width required to address any core.
                                                        // AI_TAG: PARAM_USAGE - Automatically calculated from NUM_CORES.
                                                        // AI_TAG: PARAM_CONSTRAINTS - N/A
) (
    input logic clk_i,   // AI_TAG: PORT_DESC - Main system clock for the interface.
                         // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input logic rst_ni   // AI_TAG: PORT_DESC - Asynchronous, active-low reset.
                         // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
);

    //---------------------------------------------------------------------------
    // Communication Signals from Core to Manager
    //---------------------------------------------------------------------------
    logic [NUM_CORES-1:0]                       send_valid_w;     // AI_TAG: PORT_DESC - Core 'i' asserts to indicate a valid message to send.
    logic [NUM_CORES-1:0] [CORE_ID_WIDTH-1:0]   send_dest_id_w;   // AI_TAG: PORT_DESC - The target core ID for the message from core 'i'.
    logic [NUM_CORES-1:0] [MSG_WIDTH-1:0]       send_message_w;   // AI_TAG: PORT_DESC - The message payload from core 'i'.
    logic [NUM_CORES-1:0]                       send_ready_w;     // AI_TAG: PORT_DESC - Manager asserts to indicate it's ready for a message from core 'i'.

    //---------------------------------------------------------------------------
    // Communication Signals from Manager to Core
    //---------------------------------------------------------------------------
    logic [NUM_CORES-1:0]                       recv_valid_w;     // AI_TAG: PORT_DESC - Manager asserts to indicate a valid message for core 'i'.
    logic [NUM_CORES-1:0] [CORE_ID_WIDTH-1:0]   recv_source_id_w; // AI_TAG: PORT_DESC - The source core ID of the message for core 'i'.
    logic [NUM_CORES-1:0] [MSG_WIDTH-1:0]       recv_message_w;   // AI_TAG: PORT_DESC - The message payload for core 'i'.
    logic [NUM_CORES-1:0]                       recv_ready_w;     // AI_TAG: PORT_DESC - Core 'i' asserts to indicate it's ready for a message from the manager.

    //---------------------------------------------------------------------------
    // Modports
    //---------------------------------------------------------------------------

    // Modport for a single core instance. A core 'i' connects to this modport.
    // Example Usage in core 'i': inter_core_comm_if.core[i] core_comm_if;
    modport core (
        output send_valid_w,
        output send_dest_id_w,
        output send_message_w,
        input  send_ready_w,

        input  recv_valid_w,
        input  recv_source_id_w,
        input  recv_message_w,
        output recv_ready_w
    );

    // Modport for the central communication manager/router.
    // It sees all channels from all cores.
    modport manager (
        input  send_valid_w,
        input  send_dest_id_w,
        input  send_message_w,
        output send_ready_w,

        output recv_valid_w,
        output recv_source_id_w,
        output recv_message_w,
        input  recv_ready_w
    );

endinterface : inter_core_comm_if

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
// 1.1.0   | 2025-06-28 | DesignAI           | Restructured for clarity, added arrayed modports and full flow control.
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//=============================================================================

`default_nettype wire 