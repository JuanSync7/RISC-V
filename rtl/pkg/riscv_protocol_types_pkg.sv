//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_protocol_types_pkg.sv
// Module: riscv_protocol_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains all shared parameters, data types, and enumerations related to
//   memory protocol adapters (AXI4, CHI, TileLink, etc.). This includes
//   protocol-specific structures and state machines.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_protocol_types_pkg;

    import riscv_types_pkg::*;
    import riscv_config_pkg::*;
    import riscv_protocol_constants_pkg::*;

    //---------------------------------------------------------------------------
    // 1. Protocol Configuration Parameters
    //---------------------------------------------------------------------------
    parameter integer AXI4_ID_WIDTH = CONFIG_AXI4_ID_WIDTH;
    parameter integer AXI4_ADDR_WIDTH = CONFIG_AXI4_ADDR_WIDTH;
    parameter integer AXI4_DATA_WIDTH = CONFIG_AXI4_DATA_WIDTH;
    parameter integer AXI4_STRB_WIDTH = CONFIG_AXI4_DATA_WIDTH/8;

    //---------------------------------------------------------------------------
    // 2. Protocol Types
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        PROTOCOL_AXI4,
        PROTOCOL_CHI,
        PROTOCOL_TILELINK,
        PROTOCOL_APB
    } protocol_type_e;

    //---------------------------------------------------------------------------
    // 3. AXI4 State Machine
    //---------------------------------------------------------------------------
    typedef enum logic [2:0] {
        AXI4_IDLE,           // Waiting for request
        AXI4_READ_ADDR,      // Sending read address
        AXI4_READ_DATA,      // Receiving read data
        AXI4_WRITE_ADDR,     // Sending write address
        AXI4_WRITE_DATA,     // Sending write data
        AXI4_WRITE_RESP      // Receiving write response
    } axi4_state_e;

    //---------------------------------------------------------------------------
    // 4. AXI4 Transaction Tracking
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [AXI4_ID_WIDTH-1:0] id;
        addr_t                     addr;
        logic [2:0]               size;
        logic                     write;
        word_t                    data;
        logic [AXI4_STRB_WIDTH-1:0] strb;
        logic [2:0]               prot;
        logic                     cacheable;
    } axi4_transaction_t;

    //---------------------------------------------------------------------------
    // 5. Protocol Performance Counters
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [31:0] read_transactions;
        logic [31:0] write_transactions;
        logic [31:0] read_latency_cycles;
        logic [31:0] write_latency_cycles;
        logic [31:0] protocol_errors;
        logic [31:0] timeout_errors;
    } protocol_perf_counters_t;

    //---------------------------------------------------------------------------
    // 6. Protocol Error Types
    //---------------------------------------------------------------------------
    typedef enum logic [3:0] {
        PROTOCOL_ERR_NONE,
        PROTOCOL_ERR_TIMEOUT,
        PROTOCOL_ERR_SLVERR,
        PROTOCOL_ERR_DECERR,
        PROTOCOL_ERR_BURST_LEN,
        PROTOCOL_ERR_ADDR_ALIGN,
        PROTOCOL_ERR_SIZE_MISMATCH
    } protocol_error_e;

    //---------------------------------------------------------------------------
    // 7. Burst Types
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        BURST_FIXED,     // Fixed address burst
        BURST_INCR,      // Incrementing address burst
        BURST_WRAP       // Wrapping address burst
    } burst_type_e;

    //---------------------------------------------------------------------------
    // 8. Cache Attributes
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [3:0] arcache;  // Read cache attributes
        logic [3:0] awcache;  // Write cache attributes
        logic [2:0] arprot;   // Read protection
        logic [2:0] awprot;   // Write protection
        logic       aruser;   // Read user signal
        logic       awuser;   // Write user signal
    } cache_attributes_t;

    //---------------------------------------------------------------------------
    // 9. Protocol Conversion Functions
    //---------------------------------------------------------------------------
    // Convert memory request to AXI4 address
    function automatic addr_t convert_to_axi4_addr(addr_t mem_addr);
        return mem_addr;
    endfunction

    // Convert memory size to AXI4 size
    function automatic logic [2:0] convert_to_axi4_size(logic [2:0] mem_size);
        case (mem_size)
            3'b000: return 3'b000; // 1 byte
            3'b001: return 3'b001; // 2 bytes
            3'b010: return 3'b010; // 4 bytes
            3'b011: return 3'b011; // 8 bytes
            3'b100: return 3'b100; // 16 bytes
            3'b101: return 3'b101; // 32 bytes
            3'b110: return 3'b110; // 64 bytes
            3'b111: return 3'b111; // 128 bytes
            default: return 3'b010; // Default to 4 bytes
        endcase
    endfunction

    // Convert memory strobe to AXI4 strobe
    function automatic logic [AXI4_STRB_WIDTH-1:0] convert_to_axi4_strb(logic [3:0] mem_strb);
        return mem_strb;
    endfunction

endpackage : riscv_protocol_types_pkg 