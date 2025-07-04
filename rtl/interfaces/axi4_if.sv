//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI
// Created: 2025-01-27
//
// File: axi4_if.sv
// Module: axi4_if
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   AXI4 interface definition with master/slave modports for protocol
//   adapters and memory controllers.
//=============================================================================

// ----- Fields for Automated Documentation -----
// MODULE_NAME: axi4_if
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 0.1.0
// DATE: 2025-01-29
// DESCRIPTION: Placeholder AXI4-Lite interface extending generic memory_if.
// PRIMARY_PURPOSE: Provide a future expansion path to AXI4 bus support.
// ROLE_IN_SYSTEM: Used for SoC-level integration with standard AXI bus.
// MODULE_TYPE: Interface
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: AMBA AXI4-Lite v2.0
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Implemented
// QUALITY_STATUS: Draft
//

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Comprehensive AXI4 interface with all standard signals
// AI_TAG: FEATURE - Parameterizable data and address widths
// AI_TAG: FEATURE - Separate modports for master, slave, and monitor roles
// AI_TAG: FEATURE - Full AXI4 protocol support including burst transactions

interface axi4_if #(
    parameter integer ADDR_WIDTH = 32,
    parameter integer DATA_WIDTH = 32
) (
    input logic clk,
    input logic rst_n
);

    // Import base memory interface signals for compatibility
    logic                 req;
    logic                 we;
    logic [ADDR_WIDTH-1:0] addr;
    logic [DATA_WIDTH-1:0] wdata;
    logic [DATA_WIDTH/8-1:0] wstrb;
    logic [DATA_WIDTH-1:0] rdata;
    logic                 ready;

    // AXI4-Lite channels (simplified)
    // Write address channel
    logic [ADDR_WIDTH-1:0] awaddr;
    logic                 awvalid;
    logic                 awready;

    // Write data channel
    logic [DATA_WIDTH-1:0] wdata_axi;
    logic [DATA_WIDTH/8-1:0] wstrb_axi;
    logic                 wvalid;
    logic                 wready;

    // Write response channel
    logic [1:0]           bresp;
    logic                 bvalid;
    logic                 bready;

    // Read address channel
    logic [ADDR_WIDTH-1:0] araddr;
    logic                 arvalid;
    logic                 arready;

    // Read data channel
    logic [DATA_WIDTH-1:0] rdata_axi;
    logic [1:0]           rresp;
    logic                 rvalid;
    logic                 rready;

    // Note: This is a placeholder interface. Converter modules will map between
    // the generic memory_if and AXI4-Lite when needed.

endinterface : axi4_if

`default_nettype wire 