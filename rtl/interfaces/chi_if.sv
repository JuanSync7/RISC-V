//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI
// Created: 2025-01-27
//
// File: chi_if.sv
// Module: chi_if
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   CHI (Coherent Hub Interface) interface definition with appropriate modports
//   for ARM's coherence protocol. Implements CHI-B specification.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Complete CHI-B protocol interface implementation
// AI_TAG: FEATURE - Parameterizable data and address widths
// AI_TAG: FEATURE - Request Node (RN) and Home Node (HN) modports
// AI_TAG: FEATURE - Support for coherent and non-coherent transactions

interface chi_if #(
    parameter integer DATA_WIDTH = 128,   // AI_TAG: PARAM_DESC - CHI data bus width
                                         // AI_TAG: PARAM_USAGE - Sets width of data channels
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be 128, 256, or 512 bits
    parameter integer ADDR_WIDTH = 48,    // AI_TAG: PARAM_DESC - CHI address bus width
                                         // AI_TAG: PARAM_USAGE - Sets width of address fields
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be between 32 and 52
    parameter integer NODEID_WIDTH = 7,   // AI_TAG: PARAM_DESC - CHI Node ID width
                                         // AI_TAG: PARAM_USAGE - Sets width of source and target node IDs
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be between 4 and 11
    parameter integer TXNID_WIDTH = 8     // AI_TAG: PARAM_DESC - CHI Transaction ID width
                                         // AI_TAG: PARAM_USAGE - Sets width of transaction ID fields
                                         // AI_TAG: PARAM_CONSTRAINTS - Must be between 4 and 12
) (
    input logic clk,      // AI_TAG: PORT_DESC - CHI clock signal
                          // AI_TAG: PORT_CLK_DOMAIN - clk
    input logic resetn    // AI_TAG: PORT_DESC - CHI active-low reset signal
                          // AI_TAG: PORT_CLK_DOMAIN - clk (async assert)
                          // AI_TAG: PORT_TIMING - Asynchronous
);

    // AI_TAG: INTERNAL_BLOCK - RequestChannel - CHI request channel (REQ)
    // AI_TAG: INTERNAL_BLOCK - ResponseChannel - CHI response channel (RSP)
    // AI_TAG: INTERNAL_BLOCK - DataChannel - CHI data channel (DAT)
    // AI_TAG: INTERNAL_BLOCK - SnoopChannel - CHI snoop channel (SNP)

    //---------------------------------------------------------------------
    // Request Channel (REQ)
    //---------------------------------------------------------------------
    logic [ADDR_WIDTH-1:0]  req_addr;          // Request address
    logic [6:0]             req_opcode;        // Request opcode
    logic [2:0]             req_size;          // Request size
    logic [NODEID_WIDTH-1:0] req_srcid;        // Source node ID
    logic [TXNID_WIDTH-1:0] req_txnid;         // Transaction ID
    logic [NODEID_WIDTH-1:0] req_tgtid;        // Target node ID
    logic                   req_ns;            // Non-secure
    logic                   req_allowretry;   // Allow retry
    logic [1:0]             req_order;        // Ordering requirement
    logic [3:0]             req_memattr;      // Memory attributes
    logic                   req_lpid_valid;   // Logical partition ID valid
    logic [4:0]             req_lpid;         // Logical partition ID
    logic                   req_excl;         // Exclusive access
    logic                   req_expcompack;   // Expect CompAck
    logic                   reqflitpend;      // Request flit pending
    logic                   reqflitv;         // Request flit valid
    logic                   reqlcrdv;         // Request link credit valid

    //---------------------------------------------------------------------
    // Response Channel (RSP)
    //---------------------------------------------------------------------
    logic [NODEID_WIDTH-1:0] rsp_srcid;       // Source node ID
    logic [TXNID_WIDTH-1:0] rsp_txnid;        // Transaction ID
    logic [NODEID_WIDTH-1:0] rsp_tgtid;       // Target node ID
    logic [4:0]             rsp_opcode;       // Response opcode
    logic [2:0]             rsp_resperr;      // Response error
    logic                   rsp_resp;         // Response type
    logic [1:0]             rsp_fwdstate;     // Forward state
    logic [2:0]             rsp_cbusy;        // Cache busy
    logic [NODEID_WIDTH-1:0] rsp_dbid;        // Data buffer ID
    logic [1:0]             rsp_pcrdtype;     // Protocol credit type
    logic                   rspflitpend;      // Response flit pending
    logic                   rspflitv;         // Response flit valid
    logic                   rsplcrdv;         // Response link credit valid

    //---------------------------------------------------------------------
    // Data Channel (DAT)
    //---------------------------------------------------------------------
    logic [NODEID_WIDTH-1:0] dat_srcid;       // Source node ID
    logic [TXNID_WIDTH-1:0] dat_txnid;        // Transaction ID
    logic [NODEID_WIDTH-1:0] dat_tgtid;       // Target node ID
    logic [NODEID_WIDTH-1:0] dat_homenid;     // Home node ID
    logic [3:0]             dat_opcode;       // Data opcode
    logic [1:0]             dat_resperr;      // Response error
    logic                   dat_resp;         // Response type
    logic [1:0]             dat_fwdstate;     // Forward state
    logic [2:0]             dat_cbusy;        // Cache busy
    logic [NODEID_WIDTH-1:0] dat_dbid;        // Data buffer ID
    logic [1:0]             dat_ccid;         // Cache clean/dirty ID
    logic [1:0]             dat_dataid;       // Data ID
    logic [DATA_WIDTH-1:0]  dat_data;         // Data
    logic [(DATA_WIDTH/8)-1:0] dat_datacheck; // Data check bits
    logic                   dat_poison;       // Data poison
    logic                   datflitpend;      // Data flit pending
    logic                   datflitv;         // Data flit valid
    logic                   datlcrdv;         // Data link credit valid

    //---------------------------------------------------------------------
    // Snoop Channel (SNP)
    //---------------------------------------------------------------------
    logic [ADDR_WIDTH-1:0]  snp_addr;         // Snoop address
    logic [NODEID_WIDTH-1:0] snp_srcid;       // Source node ID
    logic [TXNID_WIDTH-1:0] snp_txnid;        // Transaction ID
    logic [NODEID_WIDTH-1:0] snp_fwdnid;      // Forward node ID
    logic [TXNID_WIDTH-1:0] snp_fwdtxnid;     // Forward transaction ID
    logic [4:0]             snp_opcode;       // Snoop opcode
    logic                   snp_ns;           // Non-secure
    logic                   snp_rettosrc;     // Return to source
    logic                   snp_tracetag;     // Trace tag
    logic                   snpflitpend;      // Snoop flit pending
    logic                   snpflitv;         // Snoop flit valid
    logic                   snplcrdv;         // Snoop link credit valid

    //---------------------------------------------------------------------
    // Request Node (RN) Modport - Initiates coherent transactions
    //---------------------------------------------------------------------
    modport rn (
        // Clock and Reset
        input  clk, resetn,
        
        // Request Channel (Output)
        output req_addr, req_opcode, req_size, req_srcid, req_txnid,
        output req_tgtid, req_ns, req_allowretry, req_order, req_memattr,
        output req_lpid_valid, req_lpid, req_excl, req_expcompack,
        output reqflitpend, reqflitv,
        input  reqlcrdv,
        
        // Response Channel (Input)
        input  rsp_srcid, rsp_txnid, rsp_tgtid, rsp_opcode, rsp_resperr,
        input  rsp_resp, rsp_fwdstate, rsp_cbusy, rsp_dbid, rsp_pcrdtype,
        input  rspflitpend, rspflitv,
        output rsplcrdv,
        
        // Data Channel (Bidirectional)
        output dat_srcid, dat_txnid, dat_tgtid, dat_homenid, dat_opcode,
        output dat_resperr, dat_resp, dat_fwdstate, dat_cbusy, dat_dbid,
        output dat_ccid, dat_dataid, dat_data, dat_datacheck, dat_poison,
        output datflitpend, datflitv,
        input  datlcrdv,
        
        // Snoop Channel (Input)
        input  snp_addr, snp_srcid, snp_txnid, snp_fwdnid, snp_fwdtxnid,
        input  snp_opcode, snp_ns, snp_rettosrc, snp_tracetag,
        input  snpflitpend, snpflitv,
        output snplcrdv
    );

    //---------------------------------------------------------------------
    // Home Node (HN) Modport - Manages coherency and memory
    //---------------------------------------------------------------------
    modport hn (
        // Clock and Reset
        input  clk, resetn,
        
        // Request Channel (Input)
        input  req_addr, req_opcode, req_size, req_srcid, req_txnid,
        input  req_tgtid, req_ns, req_allowretry, req_order, req_memattr,
        input  req_lpid_valid, req_lpid, req_excl, req_expcompack,
        input  reqflitpend, reqflitv,
        output reqlcrdv,
        
        // Response Channel (Output)
        output rsp_srcid, rsp_txnid, rsp_tgtid, rsp_opcode, rsp_resperr,
        output rsp_resp, rsp_fwdstate, rsp_cbusy, rsp_dbid, rsp_pcrdtype,
        output rspflitpend, rspflitv,
        input  rsplcrdv,
        
        // Data Channel (Bidirectional)
        input  dat_srcid, dat_txnid, dat_tgtid, dat_homenid, dat_opcode,
        input  dat_resperr, dat_resp, dat_fwdstate, dat_cbusy, dat_dbid,
        input  dat_ccid, dat_dataid, dat_data, dat_datacheck, dat_poison,
        input  datflitpend, datflitv,
        output datlcrdv,
        
        // Snoop Channel (Output)
        output snp_addr, snp_srcid, snp_txnid, snp_fwdnid, snp_fwdtxnid,
        output snp_opcode, snp_ns, snp_rettosrc, snp_tracetag,
        output snpflitpend, snpflitv,
        input  snplcrdv
    );

    //---------------------------------------------------------------------
    // Monitor Modport - Observes all transactions
    //---------------------------------------------------------------------
    modport monitor (
        // Clock and Reset
        input  clk, resetn,
        
        // All signals as inputs for monitoring
        input  req_addr, req_opcode, req_size, req_srcid, req_txnid,
        input  req_tgtid, req_ns, req_allowretry, req_order, req_memattr,
        input  req_lpid_valid, req_lpid, req_excl, req_expcompack,
        input  reqflitpend, reqflitv, reqlcrdv,
        
        input  rsp_srcid, rsp_txnid, rsp_tgtid, rsp_opcode, rsp_resperr,
        input  rsp_resp, rsp_fwdstate, rsp_cbusy, rsp_dbid, rsp_pcrdtype,
        input  rspflitpend, rspflitv, rsplcrdv,
        
        input  dat_srcid, dat_txnid, dat_tgtid, dat_homenid, dat_opcode,
        input  dat_resperr, dat_resp, dat_fwdstate, dat_cbusy, dat_dbid,
        input  dat_ccid, dat_dataid, dat_data, dat_datacheck, dat_poison,
        input  datflitpend, datflitv, datlcrdv,
        
        input  snp_addr, snp_srcid, snp_txnid, snp_fwdnid, snp_fwdtxnid,
        input  snp_opcode, snp_ns, snp_rettosrc, snp_tracetag,
        input  snpflitpend, snpflitv, snplcrdv
    );

    //---------------------------------------------------------------------
    // Protocol Checker (Synthesis-aware)
    //---------------------------------------------------------------------
`ifdef SIMULATION
    // AI_TAG: ASSERTION - a_req_valid_stable: Ensures REQ flit remains stable
    // AI_TAG: ASSERTION_TYPE - Simulation
    // AI_TAG: ASSERTION_SEVERITY - Error
    property p_req_valid_stable;
        @(posedge clk) disable iff (!resetn)
        reqflitv && !reqlcrdv |=> reqflitv;
    endproperty
    a_req_valid_stable: assert property (p_req_valid_stable);

    // AI_TAG: ASSERTION - a_rsp_valid_stable: Ensures RSP flit remains stable
    property p_rsp_valid_stable;
        @(posedge clk) disable iff (!resetn)
        rspflitv && !rsplcrdv |=> rspflitv;
    endproperty
    a_rsp_valid_stable: assert property (p_rsp_valid_stable);

    // AI_TAG: ASSERTION - a_dat_valid_stable: Ensures DAT flit remains stable
    property p_dat_valid_stable;
        @(posedge clk) disable iff (!resetn)
        datflitv && !datlcrdv |=> datflitv;
    endproperty
    a_dat_valid_stable: assert property (p_dat_valid_stable);

    // AI_TAG: ASSERTION - a_snp_valid_stable: Ensures SNP flit remains stable
    property p_snp_valid_stable;
        @(posedge clk) disable iff (!resetn)
        snpflitv && !snplcrdv |=> snpflitv;
    endproperty
    a_snp_valid_stable: assert property (p_snp_valid_stable);
`endif

endinterface : chi_if

`default_nettype wire 