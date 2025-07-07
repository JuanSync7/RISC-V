//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-28
//
// File: riscv_core_types_pkg.sv
// Module: riscv_core_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   This package contains fundamental core type definitions for the RISC-V
//   processor, including basic data types, instruction structures, and
//   RISC-V specification constants that are implementation-fixed.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_core_types_pkg;

    import riscv_config_pkg::*;

    //-------------------------------------------------------------------------
    // Base Data Type Definitions
    //-------------------------------------------------------------------------
    typedef logic [CONFIG_XLEN-1:0]           word_t;
    typedef logic [CONFIG_ADDR_WIDTH-1:0]     addr_t;
    typedef logic [CONFIG_REG_ADDR_WIDTH-1:0] reg_addr_t;

    //-------------------------------------------------------------------------
    // Instruction Types
    //-------------------------------------------------------------------------
    typedef struct packed {
        logic [6:0]  opcode;
        logic [2:0]  funct3;
        logic [6:0]  funct7;
        logic [4:0]  rs1;
        logic [4:0]  rs2;
        logic [4:0]  rd;
        logic [11:0] immediate;
    } instruction_fields_t;

    //---------------------------------------------------------------------------
    // RISC-V Instruction Encoding Constants (Fixed by RISC-V Specification)
    //---------------------------------------------------------------------------
    // Opcodes (RISC-V specification)
    parameter logic [6:0] OPCODE_LUI    = 7'b0110111;
    parameter logic [6:0] OPCODE_AUIPC  = 7'b0010111;
    parameter logic [6:0] OPCODE_JAL    = 7'b1101111;
    parameter logic [6:0] OPCODE_JALR   = 7'b1100111;
    parameter logic [6:0] OPCODE_BRANCH = 7'b1100011;
    parameter logic [6:0] OPCODE_LOAD   = 7'b0000011;
    parameter logic [6:0] OPCODE_STORE  = 7'b0100011;
    parameter logic [6:0] OPCODE_OP_IMM = 7'b0010011;
    parameter logic [6:0] OPCODE_OP     = 7'b0110011;
    parameter logic [6:0] OPCODE_FENCE  = 7'b0001111;
    parameter logic [6:0] OPCODE_SYSTEM = 7'b1110011;
    
    // Function codes
    parameter logic [6:0] FUNCT7_M_EXT = 7'b0000001;
    
    // Common instruction encodings
    parameter logic [31:0] NOP_INSTRUCTION = 32'h00000013;  // addi x0, x0, 0
    
    //---------------------------------------------------------------------------
    // Exception and Interrupt Constants (Fixed by RISC-V Specification)
    //---------------------------------------------------------------------------
    // Exception cause codes (RISC-V specification)
    parameter logic [31:0] CAUSE_MISALIGNED_FETCH       = 32'h0;
    parameter logic [31:0] CAUSE_FETCH_ACCESS           = 32'h1;
    parameter logic [31:0] CAUSE_ILLEGAL_INSTRUCTION    = 32'h2;
    parameter logic [31:0] CAUSE_BREAKPOINT             = 32'h3;
    parameter logic [31:0] CAUSE_MISALIGNED_LOAD        = 32'h4;
    parameter logic [31:0] CAUSE_LOAD_ACCESS            = 32'h5;
    parameter logic [31:0] CAUSE_MISALIGNED_STORE       = 32'h6;
    parameter logic [31:0] CAUSE_STORE_ACCESS           = 32'h7;
    parameter logic [31:0] CAUSE_ECALL_U                = 32'h8;
    parameter logic [31:0] CAUSE_ECALL_S                = 32'h9;
    parameter logic [31:0] CAUSE_ECALL_M                = 32'hB;
    parameter logic [31:0] CAUSE_INSTRUCTION_PAGE_FAULT = 32'hC;
    parameter logic [31:0] CAUSE_LOAD_PAGE_FAULT        = 32'hD;
    parameter logic [31:0] CAUSE_STORE_PAGE_FAULT       = 32'hF;
    parameter logic [31:0] EXC_CAUSE_DIV_BY_ZERO        = 32'h10; // Custom cause
    parameter logic [31:0] EXC_CAUSE_ARITH_OVERFLOW     = 32'h11; // Custom cause
    
    // Interrupt base (MSB is 1)
    parameter logic [31:0] CAUSE_INTERRUPT              = 32'h80000000;
    parameter logic [31:0] CAUSE_M_SOFTWARE_INTERRUPT   = (CAUSE_INTERRUPT | 3);
    parameter logic [31:0] CAUSE_M_TIMER_INTERRUPT      = (CAUSE_INTERRUPT | 7);
    parameter logic [31:0] CAUSE_M_EXTERNAL_INTERRUPT   = (CAUSE_INTERRUPT | 11);
    
    // CSR addresses (RISC-V specification)
    parameter logic [11:0] MSTATUS_ADDR  = 12'h300;
    parameter logic [11:0] MISA_ADDR     = 12'h301;
    parameter logic [11:0] MIE_ADDR      = 12'h304;
    parameter logic [11:0] MTVEC_ADDR    = 12'h305;
    parameter logic [11:0] MSCRATCH_ADDR = 12'h340;
    parameter logic [11:0] MEPC_ADDR     = 12'h341;
    parameter logic [11:0] MCAUSE_ADDR   = 12'h342;
    parameter logic [11:0] MTVAL_ADDR    = 12'h343;
    parameter logic [11:0] MIP_ADDR      = 12'h344;
    parameter logic [11:0] MHARTID_ADDR  = 12'hF14;

    //---------------------------------------------------------------------------
    // Exception Priorities (Implementation-Fixed)
    //---------------------------------------------------------------------------
    parameter integer PRIO_DIV_ZERO         = 10;
    parameter integer PRIO_ARITH_OVERFLOW   = 9;
    parameter integer PRIO_MISALIGNED_FETCH = 12;
    parameter integer PRIO_FETCH_FAULT      = 11;
    parameter integer PRIO_MISALIGNED_MEM   = 12;
    parameter integer PRIO_MEM_FAULT        = 11;

endpackage : riscv_core_types_pkg

`default_nettype wire 