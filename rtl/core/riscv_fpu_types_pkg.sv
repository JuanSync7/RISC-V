//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: riscv_fpu_types_pkg.sv
// Module: riscv_fpu_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains data types and structures for the Floating Point Unit (FPU) interface.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_fpu_types_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    // FPU Operation Codes
    typedef enum logic [3:0] {
        FPU_ADD,    // Floating-point add
        FPU_SUB,    // Floating-point subtract
        FPU_MUL,    // Floating-point multiply
        FPU_DIV,    // Floating-point divide
        FPU_SQRT,   // Floating-point square root
        FPU_F2I,    // Float to Integer conversion
        FPU_I2F,    // Integer to Float conversion
        FPU_FMA     // Fused Multiply-Add (A * B + C)
    } fpu_op_e;

    // FPU Request structure
    typedef struct packed {
        logic        valid;
        fpu_op_e     opcode;
        word_t       operand1;
        word_t       operand2;
        word_t       operand3; // Added for FMA operation
        logic [4:0]  rd_addr; // Destination register address
        logic [4:0]  rs1_addr; // Source register 1 address
        logic [4:0]  rs2_addr; // Source register 2 address
    } fpu_req_t;

    // FPU Response structure
    typedef struct packed {
        logic        valid;
        word_t       data;
        logic        error;
        logic [4:0]  rd_addr; // Destination register address
    } fpu_rsp_t;

endpackage : riscv_fpu_types_pkg
