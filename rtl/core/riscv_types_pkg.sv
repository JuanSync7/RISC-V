//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_types_pkg.sv
// Module: riscv_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains fundamental data types, enumerations, and structures that define
//   the core RISC-V architecture and its in-order pipeline.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_types_pkg;

    import riscv_config_pkg::*;
    import riscv_exception_pkg::*;

    //---------------------------------------------------------------------------
    // 1. Core Architectural Parameters (now from config package)
    //---------------------------------------------------------------------------
    // These are now imported from riscv_config_pkg:
    // XLEN, ADDR_WIDTH, REG_COUNT, REG_ADDR_WIDTH
    // OPCODE_*, FUNCT7_M_EXT

    //---------------------------------------------------------------------------
    // 2. Base Data Type Definitions
    //---------------------------------------------------------------------------
    typedef logic [XLEN-1:0]           word_t;
    typedef logic [ADDR_WIDTH-1:0]     addr_t;
    typedef logic [REG_ADDR_WIDTH-1:0] reg_addr_t;

    //---------------------------------------------------------------------------
    // 3. Control Signal Enumerations
    //---------------------------------------------------------------------------
    typedef enum logic [4:0] {
        ALU_OP_ADD, ALU_OP_SUB, ALU_OP_XOR, ALU_OP_OR, ALU_OP_AND,
        ALU_OP_SLL, ALU_OP_SRL, ALU_OP_SRA, ALU_OP_SLT, ALU_OP_SLTU,
        ALU_OP_LUI, ALU_OP_COPY_A, ALU_OP_COPY_B
    } alu_op_e;

    typedef enum logic [0:0] { ALU_A_SEL_RS1, ALU_A_SEL_PC } alu_src_a_sel_e;
    typedef enum logic [0:0] { ALU_B_SEL_RS2, ALU_B_SEL_IMM } alu_src_b_sel_e;
    typedef enum logic [1:0] { WB_SEL_ALU, WB_SEL_MEM, WB_SEL_PC_P4, WB_SEL_CSR } wb_mux_sel_e;

    //---------------------------------------------------------------------------
    // 4. Pipeline Stage Data Structures
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        valid;
        addr_t       pc;
        word_t       instruction;
        logic [4:0]  rs1_addr;
        logic [4:0]  rs2_addr;
        logic [4:0]  rd_addr;
        word_t       rs1_data;
        word_t       rs2_data;
        word_t       immediate;
        alu_op_e     alu_op;
        alu_src_a_sel_e alu_src_a_sel;
        alu_src_b_sel_e alu_src_b_sel;
        wb_mux_sel_e wb_sel;
        logic        mem_read;
        logic        mem_write;
        logic [2:0]  mem_size;
        logic [3:0]  mem_strb;
        logic        branch;
        logic        jump;
        logic        csr_read;
        logic        csr_write;
        logic [11:0] csr_addr;
    } decode_data_t;

    typedef struct packed {
        logic        valid;
        addr_t       pc;
        word_t       alu_result;
        word_t       rs2_data;
        logic [4:0]  rd_addr;
        wb_mux_sel_e wb_sel;
        logic        mem_read;
        logic        mem_write;
        logic [2:0]  mem_size;
        logic [3:0]  mem_strb;
        logic        branch;
        logic        jump;
        logic        csr_read;
        logic        csr_write;
        logic [11:0] csr_addr;
    } execute_data_t;

    typedef struct packed {
        logic        valid;
        addr_t       pc;
        word_t       mem_data;
        word_t       alu_result;
        logic [4:0]  rd_addr;
        wb_mux_sel_e wb_sel;
        logic        csr_read;
        logic        csr_write;
        logic [11:0] csr_addr;
    } memory_data_t;

    typedef struct packed {
        logic        valid;
        addr_t       pc;
        word_t       result;
        logic [4:0]  rd_addr;
        logic        csr_read;
        logic        csr_write;
        logic [11:0] csr_addr;
    } writeback_data_t;

    //---------------------------------------------------------------------------
    // 5. Hazard Detection Types
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        data_hazard;
        logic        control_hazard;
        logic        structural_hazard;
        logic [4:0]  rs1_addr;
        logic [4:0]  rs2_addr;
        logic [4:0]  rd_addr;
    } hazard_info_t;

    //---------------------------------------------------------------------------
    // 6. Forwarding Types
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        rs1_forward;
        logic        rs2_forward;
        logic [1:0]  rs1_forward_stage;
        logic [1:0]  rs2_forward_stage;
        word_t       rs1_forward_data;
        word_t       rs2_forward_data;
    } forwarding_info_t;

    //---------------------------------------------------------------------------
    // 7. Branch Predictor Definitions
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        predict_taken;
        addr_t       predict_target;
        logic        btb_hit;
    } branch_prediction_t;

    typedef struct packed {
        logic        update_valid;
        addr_t       update_pc;
        logic        actual_taken;
        addr_t       actual_target;
        logic        is_branch;
    } branch_update_t;

    //---------------------------------------------------------------------------
    // 8. Memory Interface Types
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [3:0]  id;
        addr_t       addr;
        logic [2:0]  size;
        logic        write;
        word_t       data;
        logic [3:0]  strb;
        logic        cacheable;
        logic [2:0]  prot;
    } memory_req_t;

    typedef struct packed {
        word_t       data;
        logic [3:0]  id;
        logic        error;
        logic        last;
    } memory_rsp_t;

    //---------------------------------------------------------------------------
    // 9. Instruction Types
    //---------------------------------------------------------------------------
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
    // 10. Performance Counter Types
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [31:0] cycles;
        logic [31:0] instructions;
        logic [31:0] branches;
        logic [31:0] branch_mispredicts;
        logic [31:0] cache_misses;
        logic [31:0] cache_hits;
        logic [31:0] stalls;
    } perf_counters_t;

endpackage : riscv_types_pkg 