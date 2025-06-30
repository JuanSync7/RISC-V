//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI
// Created: 2025-01-27
//
// File: tilelink_if.sv
// Module: tilelink_if
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   TileLink interface definition with appropriate modports for cache-coherent
//   interconnect protocol. Implements TileLink Coherent (TL-C) specification.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Complete TileLink Coherent (TL-C) protocol interface
// AI_TAG: FEATURE - Parameterizable data and address widths
// AI_TAG: FEATURE - Master/Client and Slave/Manager modports
// AI_TAG: FEATURE - Support for Get, Put, Acquire, Release, and Probe operations

import riscv_config_pkg::*;

interface tilelink_if #(
    parameter integer DATA_WIDTH = DEFAULT_TL_DATA_WIDTH,    // AI_TAG: PARAM_DESC - TileLink data bus width
                                         // AI_TAG: PARAM_USAGE - Sets width of data fields
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be 8, 16, 32, 64, 128, 256, or 512 bits
    parameter integer ADDR_WIDTH = DEFAULT_TL_ADDR_WIDTH,    // AI_TAG: PARAM_DESC - TileLink address bus width
                                         // AI_TAG: PARAM_USAGE - Sets width of address fields
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be between 12 and 64
    parameter integer SOURCE_WIDTH = DEFAULT_TL_SOURCE_WIDTH,   // AI_TAG: PARAM_DESC - TileLink source ID width
                                         // AI_TAG: PARAM_USAGE - Sets width of source ID for transaction tracking
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be between 1 and 16
    parameter integer SINK_WIDTH = DEFAULT_TL_SINK_WIDTH,     // AI_TAG: PARAM_DESC - TileLink sink ID width
                                         // AI_TAG: PARAM_USAGE - Sets width of sink ID for response tracking
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be between 1 and 16
    parameter integer SIZE_WIDTH = DEFAULT_TL_SIZE_WIDTH      // AI_TAG: PARAM_DESC - TileLink size field width
                                         // AI_TAG: PARAM_USAGE - Sets width of size encoding
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be between 2 and 8
) (
    input logic clk,      // AI_TAG: PORT_DESC - TileLink clock signal
                          // AI_TAG: PORT_CLK_DOMAIN - clk
    input logic resetn    // AI_TAG: PORT_DESC - TileLink active-low reset signal
                          // AI_TAG: PORT_CLK_DOMAIN - clk (async assert)
                          // AI_TAG: PORT_TIMING - Asynchronous
);

    // AI_TAG: INTERNAL_BLOCK - ChannelA - TileLink Channel A (request)
    // AI_TAG: INTERNAL_BLOCK - ChannelB - TileLink Channel B (probe)
    // AI_TAG: INTERNAL_BLOCK - ChannelC - TileLink Channel C (release)
    // AI_TAG: INTERNAL_BLOCK - ChannelD - TileLink Channel D (grant/response)
    // AI_TAG: INTERNAL_BLOCK - ChannelE - TileLink Channel E (grant ack)

    //---------------------------------------------------------------------
    // Channel A (Request Channel)
    //---------------------------------------------------------------------
    logic [2:0]                    a_opcode;      // Operation type
    logic [2:0]                    a_param;       // Operation parameter
    logic [SIZE_WIDTH-1:0]         a_size;        // Transfer size (log2 bytes)
    logic [SOURCE_WIDTH-1:0]       a_source;      // Source identifier
    logic [ADDR_WIDTH-1:0]         a_address;     // Target address
    logic [(DATA_WIDTH/8)-1:0]     a_mask;        // Byte mask
    logic [DATA_WIDTH-1:0]         a_data;        // Data payload
    logic                          a_corrupt;     // Data corruption
    logic                          a_valid;       // Channel A valid
    logic                          a_ready;       // Channel A ready

    //---------------------------------------------------------------------
    // Channel B (Probe Channel)
    //---------------------------------------------------------------------
    logic [2:0]                    b_opcode;      // Probe operation type
    logic [1:0]                    b_param;       // Probe parameter
    logic [SIZE_WIDTH-1:0]         b_size;        // Probe size (log2 bytes)
    logic [SOURCE_WIDTH-1:0]       b_source;      // Probe source identifier
    logic [ADDR_WIDTH-1:0]         b_address;     // Probe address
    logic                          b_corrupt;     // Probe corruption
    logic                          b_valid;       // Channel B valid
    logic                          b_ready;       // Channel B ready

    //---------------------------------------------------------------------
    // Channel C (Release Channel)
    //---------------------------------------------------------------------
    logic [2:0]                    c_opcode;      // Release operation type
    logic [2:0]                    c_param;       // Release parameter
    logic [SIZE_WIDTH-1:0]         c_size;        // Release size (log2 bytes)
    logic [SOURCE_WIDTH-1:0]       c_source;      // Release source identifier
    logic [ADDR_WIDTH-1:0]         c_address;     // Release address
    logic [DATA_WIDTH-1:0]         c_data;        // Release data payload
    logic                          c_corrupt;     // Release corruption
    logic                          c_valid;       // Channel C valid
    logic                          c_ready;       // Channel C ready

    //---------------------------------------------------------------------
    // Channel D (Grant/Response Channel)
    //---------------------------------------------------------------------
    logic [2:0]                    d_opcode;      // Response operation type
    logic [1:0]                    d_param;       // Response parameter
    logic [SIZE_WIDTH-1:0]         d_size;        // Response size (log2 bytes)
    logic [SOURCE_WIDTH-1:0]       d_source;      // Source identifier (echoed)
    logic [SINK_WIDTH-1:0]         d_sink;        // Sink identifier
    logic                          d_denied;      // Request was denied
    logic [DATA_WIDTH-1:0]         d_data;        // Response data
    logic                          d_corrupt;     // Data corruption
    logic                          d_valid;       // Channel D valid
    logic                          d_ready;       // Channel D ready

    //---------------------------------------------------------------------
    // Channel E (Grant Ack Channel)
    //---------------------------------------------------------------------
    logic [SINK_WIDTH-1:0]         e_sink;        // Grant ack sink identifier
    logic                          e_valid;       // Channel E valid
    logic                          e_ready;       // Channel E ready

    //---------------------------------------------------------------------
    // Master/Client Modport - Initiates transactions
    //---------------------------------------------------------------------
    modport master (
        // Clock and Reset
        input  clk, resetn,
        
        // Channel A (Output)
        output a_opcode, a_param, a_size, a_source, a_address,
        output a_mask, a_data, a_corrupt, a_valid,
        input  a_ready,
        
        // Channel B (Input)
        input  b_opcode, b_param, b_size, b_source, b_address,
        input  b_corrupt, b_valid,
        output b_ready,
        
        // Channel C (Output)
        output c_opcode, c_param, c_size, c_source, c_address,
        output c_data, c_corrupt, c_valid,
        input  c_ready,
        
        // Channel D (Input)
        input  d_opcode, d_param, d_size, d_source, d_sink,
        input  d_denied, d_data, d_corrupt, d_valid,
        output d_ready,

        // Channel E (Output)
        output e_sink, e_valid,
        input  e_ready
    );

    //---------------------------------------------------------------------
    // Slave/Manager Modport - Responds to transactions
    //---------------------------------------------------------------------
    modport slave (
        // Clock and Reset
        input  clk, resetn,
        
        // Channel A (Input)
        input  a_opcode, a_param, a_size, a_source, a_address,
        input  a_mask, a_data, a_corrupt, a_valid,
        output a_ready,
        
        // Channel B (Output)
        output b_opcode, b_param, b_size, b_source, b_address,
        output b_corrupt, b_valid,
        input  b_ready,
        
        // Channel C (Input)
        input  c_opcode, c_param, c_size, c_source, c_address,
        input  c_data, c_corrupt, c_valid,
        output c_ready,
        
        // Channel D (Output)
        output d_opcode, d_param, d_size, d_source, d_sink,
        output d_denied, d_data, d_corrupt, d_valid,
        input  d_ready,

        // Channel E (Input)
        input  e_sink, e_valid,
        output e_ready
    );

    //---------------------------------------------------------------------
    // Monitor Modport - Observes all transactions
    //---------------------------------------------------------------------
    modport monitor (
        // Clock and Reset
        input  clk, resetn,
        
        // All signals as inputs for monitoring
        input  a_opcode, a_param, a_size, a_source, a_address,
        input  a_mask, a_data, a_corrupt, a_valid, a_ready,
        input  b_opcode, b_param, b_size, b_source, b_address,
        input  b_corrupt, b_valid, b_ready,
        input  c_opcode, c_param, c_size, c_source, c_address,
        input  c_data, c_corrupt, c_valid, c_ready,
        input  d_opcode, d_param, d_size, d_source, d_sink,
        input  d_denied, d_data, d_corrupt, d_valid, d_ready,
        input  e_sink, e_valid, e_ready
    );

    //---------------------------------------------------------------------
    // Protocol Constants (Opcodes)
    //---------------------------------------------------------------------
    // Channel A Opcodes
    localparam logic [2:0] TL_A_GET             = 3'h4;    // Get request
    localparam logic [2:0] TL_A_PUT_FULL_DATA   = 3'h0;    // Put full data
    localparam logic [2:0] TL_A_PUT_PARTIAL_DATA = 3'h1;   // Put partial data
    localparam logic [2:0] TL_A_ARITHMETIC_DATA = 3'h2;    // Arithmetic operation
    localparam logic [2:0] TL_A_LOGICAL_DATA    = 3'h3;    // Logical operation
    localparam logic [2:0] TL_A_INTENT          = 3'h5;    // Hint/Intent
    localparam logic [2:0] TL_A_ACQUIRE_BLOCK   = 3'h6;    // Acquire block (for cache coherence)
    localparam logic [2:0] TL_A_ACQUIRE_PERM    = 3'h7;    // Acquire permissions (for cache coherence)
    
    // Channel B Opcodes
    localparam logic [2:0] TL_B_PROBE_BLOCK     = 3'h6;    // Probe block
    localparam logic [2:0] TL_B_PROBE_PERM      = 3'h7;    // Probe permissions

    // Channel C Opcodes
    localparam logic [2:0] TL_C_RELEASE_DATA    = 3'h0;    // Release data
    localparam logic [2:0] TL_C_PROBE_ACK       = 3'h4;    // Probe acknowledgement
    localparam logic [2:0] TL_C_PROBE_ACK_DATA  = 3'h5;    // Probe acknowledgement with data

    // Channel D Opcodes
    localparam logic [2:0] TL_D_ACCESS_ACK      = 3'h0;    // Access acknowledgment
    localparam logic [2:0] TL_D_ACCESS_ACK_DATA = 3'h1;    // Access ack with data
    localparam logic [2:0] TL_D_HINT_ACK        = 3'h2;    // Hint acknowledgment
    localparam logic [2:0] TL_D_GRANT           = 3'h4;    // Grant permissions
    local_param logic [2:0] TL_D_GRANT_DATA      = 3'h5;    // Grant with data
    local_param logic [2:0] TL_D_RELEASE_ACK     = 3'h6;    // Release acknowledgment

    //---------------------------------------------------------------------
    // Protocol Checker (Synthesis-aware)
    //---------------------------------------------------------------------
`ifdef SIMULATION
    // AI_TAG: ASSERTION - a_channel_a_valid_stable: Ensures Channel A valid remains stable
    // AI_TAG: ASSERTION_TYPE - Simulation
    // AI_TAG: ASSERTION_SEVERITY - Error
    property p_channel_a_valid_stable;
        @(posedge clk) disable iff (!resetn)
        a_valid && !a_ready |=> a_valid;
    endproperty
    a_channel_a_valid_stable: assert property (p_channel_a_valid_stable);

    // AI_TAG: ASSERTION - a_channel_b_valid_stable: Ensures Channel B valid remains stable
    property p_channel_b_valid_stable;
        @(posedge clk) disable iff (!resetn)
        b_valid && !b_ready |=> b_valid;
    endproperty
    a_channel_b_valid_stable: assert property (p_channel_b_valid_stable);

    // AI_TAG: ASSERTION - a_channel_c_valid_stable: Ensures Channel C valid remains stable
    property p_channel_c_valid_stable;
        @(posedge clk) disable iff (!resetn)
        c_valid && !c_ready |=> c_valid;
    endproperty
    a_channel_c_valid_stable: assert property (p_channel_c_valid_stable);

    // AI_TAG: ASSERTION - a_channel_d_valid_stable: Ensures Channel D valid remains stable
    property p_channel_d_valid_stable;
        @(posedge clk) disable iff (!resetn)
        d_valid && !d_ready |=> d_valid;
    endproperty
    a_channel_d_valid_stable: assert property (p_channel_d_valid_stable);

    // AI_TAG: ASSERTION - a_channel_e_valid_stable: Ensures Channel E valid remains stable
    property p_channel_e_valid_stable;
        @(posedge clk) disable iff (!resetn)
        e_valid && !e_ready |=> e_valid;
    endproperty
    a_channel_e_valid_stable: assert property (p_channel_e_valid_stable);

    // AI_TAG: ASSERTION - a_channel_a_signals_stable: Ensures Channel A signals stable when valid
    property p_channel_a_signals_stable;
        @(posedge clk) disable iff (!resetn)
        a_valid && !a_ready |=> $stable({a_opcode, a_param, a_size, a_source, 
                                        a_address, a_mask, a_data, a_corrupt});
    endproperty
    a_channel_a_signals_stable: assert property (p_channel_a_signals_stable);

    // AI_TAG: ASSERTION - a_channel_d_signals_stable: Ensures Channel D signals stable when valid
    property p_channel_d_signals_stable;
        @(posedge clk) disable iff (!resetn)
        d_valid && !d_ready |=> $stable({d_opcode, d_param, d_size, d_source,
                                        d_sink, d_denied, d_data, d_corrupt});
    endproperty
    a_channel_d_signals_stable: assert property (p_channel_d_signals_stable);

    // AI_TAG: ASSERTION - a_valid_opcode_a: Ensures valid opcodes on Channel A
    property p_valid_opcode_a;
        @(posedge clk) disable iff (!resetn)
        a_valid |-> (a_opcode inside {TL_A_GET, TL_A_PUT_FULL_DATA, TL_A_PUT_PARTIAL_DATA,
                                     TL_A_ARITHMETIC_DATA, TL_A_LOGICAL_DATA, TL_A_INTENT,
                                     TL_A_ACQUIRE_BLOCK, TL_A_ACQUIRE_PERM});
    endproperty
    a_valid_opcode_a: assert property (p_valid_opcode_a);

    // AI_TAG: ASSERTION - a_valid_opcode_d: Ensures valid opcodes on Channel D
    property p_valid_opcode_d;
        @(posedge clk) disable iff (!resetn)
        d_valid |-> (d_opcode inside {TL_D_ACCESS_ACK, TL_D_ACCESS_ACK_DATA, TL_D_HINT_ACK,
                                     TL_D_GRANT, TL_D_GRANT_DATA, TL_D_RELEASE_ACK});
    endproperty
    a_valid_opcode_d: assert property (p_valid_opcode_d);
`endif

endinterface : tilelink_if

`default_nettype wire 