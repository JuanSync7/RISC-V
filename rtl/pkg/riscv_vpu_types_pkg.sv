//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: riscv_vpu_types_pkg.sv
// Module: riscv_vpu_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains data types and structures for the Vector Processing Unit (VPU) interface.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_vpu_types_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    // AI_TAG: PARAM_DESC - MAX_VECTOR_LENGTH - Maximum number of elements in a vector.
    // AI_TAG: PARAM_USAGE - Defines the maximum parallelism for vector operations.
    // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2.
    parameter integer MAX_VECTOR_LENGTH = CONFIG_MAX_VECTOR_LENGTH; // Example: 8 elements per vector

    // VPU Operation Codes
    typedef enum logic [3:0] {
        VPU_ADD,    // Vector add
        VPU_SUB,    // Vector subtract
        VPU_MUL,    // Vector multiply
        VPU_DIV,    // Vector divide
        VPU_LOAD,   // Vector load from memory
        VPU_STORE,  // Vector store to memory
        VPU_REDUCE_SUM, // Vector reduction: sum of elements
        VPU_REDUCE_MIN, // Vector reduction: minimum element
        VPU_REDUCE_MAX, // Vector reduction: maximum element
        VPU_PERMUTE   // Vector permutation/reordering
    } vpu_op_e;

    // VPU Request structure
    typedef struct packed {
        logic        valid;          // Request valid
        vpu_op_e     opcode;         // VPU operation code
        logic [($clog2(MAX_VECTOR_LENGTH))-1:0] vector_length; // Number of active elements
        word_t       operand1_vector [MAX_VECTOR_LENGTH]; // First vector operand
        word_t       operand2_vector [MAX_VECTOR_LENGTH]; // Second vector operand (if applicable)
        addr_t       addr;           // Base address for vector load/store
        logic [4:0]  rd_addr;        // Destination register address (for scalar results or control)
        logic [4:0]  rs1_addr;       // Source register 1 address (for scalar operands or control)
        logic [4:0]  rs2_addr;       // Source register 2 address (for scalar operands or control)
    } vpu_req_t;

    // VPU Response structure
    typedef struct packed {
        logic        valid;          // Response valid
        word_t       result_vector [MAX_VECTOR_LENGTH]; // Result vector
        logic        error;          // Error indicator
        logic [4:0]  rd_addr;        // Destination register address (for scalar results or control)
    } vpu_rsp_t;

endpackage : riscv_vpu_types_pkg
