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

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Comprehensive AXI4 interface with all standard signals
// AI_TAG: FEATURE - Parameterizable data and address widths
// AI_TAG: FEATURE - Separate modports for master, slave, and monitor roles
// AI_TAG: FEATURE - Full AXI4 protocol support including burst transactions

interface axi4_if #(
    parameter integer DATA_WIDTH = 64,    // AI_TAG: PARAM_DESC - AXI4 data bus width
                                         // AI_TAG: PARAM_USAGE - Sets width of WDATA and RDATA signals
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be 32, 64, 128, 256, 512, or 1024
    parameter integer ADDR_WIDTH = 32,    // AI_TAG: PARAM_DESC - AXI4 address bus width
                                         // AI_TAG: PARAM_USAGE - Sets width of AWADDR and ARADDR signals
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be between 12 and 64
    parameter integer ID_WIDTH = 4,       // AI_TAG: PARAM_DESC - AXI4 transaction ID width
                                         // AI_TAG: PARAM_USAGE - Sets width of AWID, ARID, BID, RID signals
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be between 1 and 16
    parameter integer USER_WIDTH = 1      // AI_TAG: PARAM_DESC - AXI4 user signal width
                                         // AI_TAG: PARAM_USAGE - Sets width of AWUSER, ARUSER, WUSER, RUSER, BUSER signals
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be at least 1
) (
    input logic aclk,     // AI_TAG: PORT_DESC - AXI4 clock signal
                          // AI_TAG: PORT_CLK_DOMAIN - aclk
    input logic aresetn   // AI_TAG: PORT_DESC - AXI4 active-low reset signal
                          // AI_TAG: PORT_CLK_DOMAIN - aclk (async assert)
                          // AI_TAG: PORT_TIMING - Asynchronous
);

    // AI_TAG: INTERNAL_BLOCK - WriteAddressChannel - AXI4 write address channel signals
    // AI_TAG: INTERNAL_BLOCK - WriteDataChannel - AXI4 write data channel signals
    // AI_TAG: INTERNAL_BLOCK - WriteResponseChannel - AXI4 write response channel signals
    // AI_TAG: INTERNAL_BLOCK - ReadAddressChannel - AXI4 read address channel signals
    // AI_TAG: INTERNAL_BLOCK - ReadDataChannel - AXI4 read data channel signals

    //---------------------------------------------------------------------
    // Write Address Channel
    //---------------------------------------------------------------------
    logic [ID_WIDTH-1:0]    awid;      // Write address ID
    logic [ADDR_WIDTH-1:0]  awaddr;    // Write address
    logic [7:0]             awlen;     // Burst length
    logic [2:0]             awsize;    // Burst size
    logic [1:0]             awburst;   // Burst type
    logic                   awlock;    // Lock type
    logic [3:0]             awcache;   // Memory type
    logic [2:0]             awprot;    // Protection type
    logic [3:0]             awqos;     // Quality of Service
    logic [3:0]             awregion;  // Region identifier
    logic [USER_WIDTH-1:0]  awuser;    // User signal
    logic                   awvalid;   // Write address valid
    logic                   awready;   // Write address ready

    //---------------------------------------------------------------------
    // Write Data Channel
    //---------------------------------------------------------------------
    logic [DATA_WIDTH-1:0]      wdata;     // Write data
    logic [(DATA_WIDTH/8)-1:0]  wstrb;     // Write strobes
    logic                       wlast;     // Write last
    logic [USER_WIDTH-1:0]      wuser;     // User signal
    logic                       wvalid;    // Write valid
    logic                       wready;    // Write ready

    //---------------------------------------------------------------------
    // Write Response Channel
    //---------------------------------------------------------------------
    logic [ID_WIDTH-1:0]    bid;       // Response ID
    logic [1:0]             bresp;     // Write response
    logic [USER_WIDTH-1:0]  buser;     // User signal
    logic                   bvalid;    // Write response valid
    logic                   bready;    // Response ready

    //---------------------------------------------------------------------
    // Read Address Channel
    //---------------------------------------------------------------------
    logic [ID_WIDTH-1:0]    arid;      // Read address ID
    logic [ADDR_WIDTH-1:0]  araddr;    // Read address
    logic [7:0]             arlen;     // Burst length
    logic [2:0]             arsize;    // Burst size
    logic [1:0]             arburst;   // Burst type
    logic                   arlock;    // Lock type
    logic [3:0]             arcache;   // Memory type
    logic [2:0]             arprot;    // Protection type
    logic [3:0]             arqos;     // Quality of Service
    logic [3:0]             arregion;  // Region identifier
    logic [USER_WIDTH-1:0]  aruser;    // User signal
    logic                   arvalid;   // Read address valid
    logic                   arready;   // Read address ready

    //---------------------------------------------------------------------
    // Read Data Channel
    //---------------------------------------------------------------------
    logic [ID_WIDTH-1:0]    rid;       // Read ID
    logic [DATA_WIDTH-1:0]  rdata;     // Read data
    logic [1:0]             rresp;     // Read response
    logic                   rlast;     // Read last
    logic [USER_WIDTH-1:0]  ruser;     // User signal
    logic                   rvalid;    // Read valid
    logic                   rready;    // Read ready

    //---------------------------------------------------------------------
    // Master Modport - Initiates transactions
    //---------------------------------------------------------------------
    modport master (
        // Clock and Reset
        input  aclk, aresetn,
        
        // Write Address Channel
        output awid, awaddr, awlen, awsize, awburst, awlock,
        output awcache, awprot, awqos, awregion, awuser, awvalid,
        input  awready,
        
        // Write Data Channel
        output wdata, wstrb, wlast, wuser, wvalid,
        input  wready,
        
        // Write Response Channel
        input  bid, bresp, buser, bvalid,
        output bready,
        
        // Read Address Channel
        output arid, araddr, arlen, arsize, arburst, arlock,
        output arcache, arprot, arqos, arregion, aruser, arvalid,
        input  arready,
        
        // Read Data Channel
        input  rid, rdata, rresp, rlast, ruser, rvalid,
        output rready
    );

    //---------------------------------------------------------------------
    // Slave Modport - Responds to transactions
    //---------------------------------------------------------------------
    modport slave (
        // Clock and Reset
        input  aclk, aresetn,
        
        // Write Address Channel
        input  awid, awaddr, awlen, awsize, awburst, awlock,
        input  awcache, awprot, awqos, awregion, awuser, awvalid,
        output awready,
        
        // Write Data Channel
        input  wdata, wstrb, wlast, wuser, wvalid,
        output wready,
        
        // Write Response Channel
        output bid, bresp, buser, bvalid,
        input  bready,
        
        // Read Address Channel
        input  arid, araddr, arlen, arsize, arburst, arlock,
        input  arcache, arprot, arqos, arregion, aruser, arvalid,
        output arready,
        
        // Read Data Channel
        output rid, rdata, rresp, rlast, ruser, rvalid,
        input  rready
    );

    //---------------------------------------------------------------------
    // Monitor Modport - Observes all transactions
    //---------------------------------------------------------------------
    modport monitor (
        // Clock and Reset
        input  aclk, aresetn,
        
        // All signals as inputs for monitoring
        input  awid, awaddr, awlen, awsize, awburst, awlock,
        input  awcache, awprot, awqos, awregion, awuser, awvalid, awready,
        input  wdata, wstrb, wlast, wuser, wvalid, wready,
        input  bid, bresp, buser, bvalid, bready,
        input  arid, araddr, arlen, arsize, arburst, arlock,
        input  arcache, arprot, arqos, arregion, aruser, arvalid, arready,
        input  rid, rdata, rresp, rlast, ruser, rvalid, rready
    );

    //---------------------------------------------------------------------
    // Protocol Checker (Synthesis-aware)
    //---------------------------------------------------------------------
`ifdef SIMULATION
    // AI_TAG: ASSERTION - a_aw_valid_stable: Ensures AWVALID remains stable until AWREADY
    // AI_TAG: ASSERTION_TYPE - Simulation
    // AI_TAG: ASSERTION_SEVERITY - Error
    property p_aw_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        awvalid && !awready |=> awvalid;
    endproperty
    a_aw_valid_stable: assert property (p_aw_valid_stable);

    // AI_TAG: ASSERTION - a_w_valid_stable: Ensures WVALID remains stable until WREADY
    property p_w_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        wvalid && !wready |=> wvalid;
    endproperty
    a_w_valid_stable: assert property (p_w_valid_stable);

    // AI_TAG: ASSERTION - a_ar_valid_stable: Ensures ARVALID remains stable until ARREADY
    property p_ar_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        arvalid && !arready |=> arvalid;
    endproperty
    a_ar_valid_stable: assert property (p_ar_valid_stable);

    // AI_TAG: ASSERTION - a_b_valid_stable: Ensures BVALID remains stable until BREADY
    property p_b_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        bvalid && !bready |=> bvalid;
    endproperty
    a_b_valid_stable: assert property (p_b_valid_stable);

    // AI_TAG: ASSERTION - a_r_valid_stable: Ensures RVALID remains stable until RREADY
    property p_r_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        rvalid && !rready |=> rvalid;
    endproperty
    a_r_valid_stable: assert property (p_r_valid_stable);
`endif

endinterface : axi4_if

`default_nettype wire 