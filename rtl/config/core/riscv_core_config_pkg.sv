//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_core_config_pkg.sv
// Module: riscv_core_config_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   This package contains the fundamental configuration for the RISC-V core
//   architecture, including data widths and user-configurable parameters.
//   Fixed RISC-V specification constants are defined in riscv_core_types_pkg.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_core_config_pkg;

    //---------------------------------------------------------------------------
    // 1. Core Architecture Configuration
    //---------------------------------------------------------------------------
    parameter integer XLEN = 32;                    // Data width (32 for RV32, 64 for RV64)
    parameter integer ADDR_WIDTH = 32;              // Address width
    parameter integer REG_COUNT = 32;               // Number of architectural registers
    parameter integer REG_ADDR_WIDTH = $clog2(REG_COUNT);
    
    // Reset vector configuration
    parameter logic [ADDR_WIDTH-1:0] DEFAULT_RESET_VECTOR = 32'h0000_0000;

endpackage : riscv_core_config_pkg

`default_nettype wire