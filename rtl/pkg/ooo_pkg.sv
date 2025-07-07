//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-06
//
// File: ooo_pkg.sv
// Package: ooo_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Package defining common data types and parameters for the Out-of-Order (OoO)
//   execution engine.
//=============================================================================

package ooo_pkg;

    import riscv_config_pkg::*;

    // Parameters (can be overridden by top-level modules)
    parameter integer DATA_WIDTH     = XLEN;
    parameter integer PC_WIDTH       = ADDR_WIDTH;
    parameter integer REG_ADDR_WIDTH = riscv_config_pkg::REG_ADDR_WIDTH;
    parameter integer RS_SIZE        = DEFAULT_RS_SIZE; // Reservation Station size
    parameter integer ROB_SIZE       = DEFAULT_ROB_SIZE; // Re-Order Buffer size

    localparam integer ROB_ADDR_WIDTH = $clog2(ROB_SIZE);

    // Typedef for dispatching instructions from Decode/Rename to RS/ROB
    typedef struct packed {
        logic                       valid;
        logic [PC_WIDTH-1:0]        pc;
        logic [31:0]                opcode; // Full instruction opcode/data
        logic [DATA_WIDTH-1:0]      v_rs1;  // Value of operand 1 if available
        logic                       q_rs1_valid; // Is operand 1 waiting for a result?
        logic [ROB_ADDR_WIDTH-1:0]  q_rs1;  // ROB tag for operand 1
        logic [DATA_WIDTH-1:0]      v_rs2;  // Value of operand 2 if available
        logic                       q_rs2_valid; // Is operand 2 waiting for a result?
        logic [ROB_ADDR_WIDTH-1:0]  q_rs2;  // ROB tag for operand 2
        logic [REG_ADDR_WIDTH-1:0]  rd_addr; // Destination register address
        logic                       rd_write_en; // Does this instruction write to rd?
        logic [ROB_ADDR_WIDTH-1:0]  rob_tag; // ROB tag assigned to this instruction
    } ooo_dispatch_t;

    // Typedef for issuing instructions from RS to Functional Units
    typedef struct packed {
        logic                       valid;
        logic [31:0]                opcode;
        logic [DATA_WIDTH-1:0]      v_rs1;
        logic [DATA_WIDTH-1:0]      v_rs2;
        logic [ROB_ADDR_WIDTH-1:0]  rob_tag;
    } ooo_issue_t;

    // Typedef for results from Functional Units to ROB/CDB
    typedef struct packed {
        logic                       valid;
        logic [ROB_ADDR_WIDTH-1:0]  rob_tag;
        logic [DATA_WIDTH-1:0]      data;
        logic                       exception_valid;
        logic [31:0]                exception_cause;
    } ooo_result_t;

    // Typedef for committing instructions from ROB to Architectural Register File
    typedef struct packed {
        logic                       valid;
        logic [PC_WIDTH-1:0]        pc;
        logic [REG_ADDR_WIDTH-1:0]  rd_addr;
        logic [DATA_WIDTH-1:0]      result;
        logic                       exception_valid;
        logic [31:0]                exception_cause;
    } ooo_commit_t;

endpackage : ooo_pkg
