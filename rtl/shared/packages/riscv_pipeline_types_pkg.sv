//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-28
//
// File: riscv_pipeline_types_pkg.sv
// Module: riscv_pipeline_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   This package contains pipeline type definitions for the RISC-V processor,
//   including ALU operations, pipeline data structures, hazard detection,
//   branch prediction types, and implementation-fixed pipeline constants.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_pipeline_types_pkg;

    import riscv_core_config_pkg::*;
    import riscv_pipeline_config_pkg::*;

    //-------------------------------------------------------------------------
    // Pipeline Data Types
    //-------------------------------------------------------------------------
    typedef enum logic [4:0] {
        ALU_OP_ADD, ALU_OP_SUB, ALU_OP_XOR, ALU_OP_OR, ALU_OP_AND,
        ALU_OP_SLL, ALU_OP_SRL, ALU_OP_SRA, ALU_OP_SLT, ALU_OP_SLTU,
        ALU_OP_LUI, ALU_OP_COPY_A, ALU_OP_COPY_B
    } alu_op_e;

    typedef enum logic [0:0] { ALU_A_SEL_RS1, ALU_A_SEL_PC } alu_src_a_sel_e;
    typedef enum logic [0:0] { ALU_B_SEL_RS2, ALU_B_SEL_IMM } alu_src_b_sel_e;
    typedef enum logic [1:0] { WB_SEL_ALU, WB_SEL_MEM, WB_SEL_PC_P4, WB_SEL_CSR } wb_mux_sel_e;

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

    typedef struct packed {
        logic        data_hazard;
        logic        control_hazard;
        logic        structural_hazard;
        logic [4:0]  rs1_addr;
        logic [4:0]  rs2_addr;
        logic [4:0]  rd_addr;
    } hazard_info_t;

    typedef struct packed {
        logic        rs1_forward;
        logic        rs2_forward;
        logic [1:0]  rs1_forward_stage;
        logic [1:0]  rs2_forward_stage;
        word_t       rs1_forward_data;
        word_t       rs2_forward_data;
    } forwarding_info_t;

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
    // Performance Counter Types
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

    //---------------------------------------------------------------------------
    // Pipeline Control Constants (Implementation-Fixed)
    //---------------------------------------------------------------------------
    // Data Forwarding Selector Values
    parameter logic [1:0] FWD_SEL_REG = 2'b00;  // Select value from register file
    parameter logic [1:0] FWD_SEL_MEM = 2'b01;  // Forward from Memory stage result
    parameter logic [1:0] FWD_SEL_WB  = 2'b10;  // Forward from Writeback stage result

    //---------------------------------------------------------------------------
    // Branch Predictor Counter Constants (Implementation-Fixed)
    //---------------------------------------------------------------------------
    // Initial counter values for branch predictors
    parameter logic [1:0] BTB_COUNTER_INIT = 2'b01;                 // Weakly not-taken initial state
    parameter logic [1:0] BHT_COUNTER_INIT = 2'b01;                 // Weakly not-taken initial state
    parameter logic [1:0] PHT_COUNTER_INIT = 2'b01;                 // Weakly not-taken initial state
    parameter logic [1:0] SELECTOR_COUNTER_INIT = 2'b01;            // Initial selector state
    
    // Counter bounds (strongly not-taken to strongly taken)
    parameter logic [1:0] COUNTER_STRONGLY_NOT_TAKEN = 2'b00;       // Strongly not-taken
    parameter logic [1:0] COUNTER_WEAKLY_NOT_TAKEN = 2'b01;         // Weakly not-taken
    parameter logic [1:0] COUNTER_WEAKLY_TAKEN = 2'b10;             // Weakly taken
    parameter logic [1:0] COUNTER_STRONGLY_TAKEN = 2'b11;           // Strongly taken

endpackage : riscv_pipeline_types_pkg

`default_nettype wire 