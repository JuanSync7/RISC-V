//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: riscv_dpu_types_pkg.sv
// Module: riscv_dpu_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains data types and structures for the Data Processing Unit (DPU)
//   interface.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_dpu_types_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    // DPU Request structure
    typedef struct packed {
        logic        valid;
        logic [6:0]  opcode; // DPU operation code
        word_t       data;   // Input data
        addr_t       addr;   // Address for memory-mapped operations
    } dpu_req_t;

    // DPU Response structure
    typedef struct packed {
        logic        valid;
        word_t       data;   // Output data
        logic        error;  // Error indicator
    } dpu_rsp_t;

endpackage : riscv_dpu_types_pkg
