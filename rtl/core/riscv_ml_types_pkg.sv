//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: riscv_ml_types_pkg.sv
// Module: riscv_ml_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains data types and structures for the Machine Learning Inference Unit (MLIU) interface.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_ml_types_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    // MLIU Operation Codes
    typedef enum logic [3:0] {
        MLIU_MATRIX_MUL,    // Matrix Multiplication
        MLIU_CONVOLUTION,   // Convolutional Layer
        MLIU_ACTIVATION,    // Activation Function
        MLIU_POOLING,
        MLIU_RELU,          // Rectified Linear Unit activation
        MLIU_SIGMOID,       // Sigmoid activation
        MLIU_TANH,          // Tanh activation
        MLIU_MAX_POOL,      // Max Pooling
        MLIU_AVG_POOL       // Average Pooling
    } mliu_op_e;

    // MLIU Request structure
    typedef struct packed {
        logic        valid;
        mliu_op_e    opcode;
        word_t       operand1; // Input data / pointer
        word_t       operand2; // Weights / kernel / pointer
        logic [4:0]  rd_addr;    // Destination register address
    } mliu_req_t;

    // MLIU Response structure
    typedef struct packed {
        logic        valid;
        word_t       data;
        logic        error;
        logic [4:0]  rd_addr; // Destination register address
    } mliu_rsp_t;

endpackage : riscv_ml_types_pkg
