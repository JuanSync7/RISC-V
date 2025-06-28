////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-27
// Design Name:   RV32IM Core
// Module Name:   riscv_core_pkg
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   Central package for the RV32IM RISC-V core.
//                Contains all shared parameters, data types, enumerations,
//                and pipeline register structures used throughout the design.
//
// Dependencies:  None
//
// Revision:
// Revision 1.1.0 - Updated pipeline structs for hazard detection and added
//                  control signals for M-extension and CSR operations.
// Revision 1.0.0 - File Created
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps
`default_nettype none

package riscv_core_pkg;

    //---------------------------------------------------------------------------
    // 1. Core Architectural Parameters
    //---------------------------------------------------------------------------
    // AI_TAG: PARAMETER - XLEN - Defines the native data width of the processor (32-bit for RV32).
    parameter integer XLEN = 32;

    // AI_TAG: PARAMETER - ADDR_WIDTH - Defines the width of memory addresses (PC, data addresses).
    parameter integer ADDR_WIDTH = 32;

    // AI_TAG: PARAMETER - REG_COUNT - Number of general-purpose architectural registers.
    parameter integer REG_COUNT = 32;

    // AI_TAG: PARAMETER - REG_ADDR_WIDTH - Width of the register address bus.
    parameter integer REG_ADDR_WIDTH = $clog2(REG_COUNT);


    //---------------------------------------------------------------------------
    // 2. Base Data Type Definitions
    //---------------------------------------------------------------------------
    // AI_TAG: TYPEDEF - word_t - Standard data word type for the processor.
    typedef logic [XLEN-1:0]           word_t;
    // AI_TAG: TYPEDEF - addr_t - Standard address type for PC and memory accesses.
    typedef logic [ADDR_WIDTH-1:0]     addr_t;
    // AI_TAG: TYPEDEF - reg_addr_t - Type for addressing the register file.
    typedef logic [REG_ADDR_WIDTH-1:0] reg_addr_t;


    //---------------------------------------------------------------------------
    // 3. RISC-V Instruction Field Definitions
    //---------------------------------------------------------------------------
    localparam logic [6:0] OPCODE_LUI    = 7'b0110111;
    localparam logic [6:0] OPCODE_AUIPC  = 7'b0010111;
    localparam logic [6:0] OPCODE_JAL    = 7'b1101111;
    localparam logic [6:0] OPCODE_JALR   = 7'b1100111;
    localparam logic [6:0] OPCODE_BRANCH = 7'b1100011;
    localparam logic [6:0] OPCODE_LOAD   = 7'b0000011;
    localparam logic [6:0] OPCODE_STORE  = 7'b0100011;
    localparam logic [6:0] OPCODE_OP_IMM = 7'b0010011;
    localparam logic [6:0] OPCODE_OP     = 7'b0110011;
    localparam logic [6:0] OPCODE_FENCE  = 7'b0001111;
    localparam logic [6:0] OPCODE_SYSTEM = 7'b1110011;

    // AI_TAG: CONSTANT - FUNCT7_M_EXT - Funct7 field for RV32M integer mul/div instructions.
    localparam logic [6:0] FUNCT7_M_EXT = 7'b0000001;


    //---------------------------------------------------------------------------
    // 4. Control Signal Enumerations
    //---------------------------------------------------------------------------
    typedef enum logic [4:0] {
        ALU_OP_ADD, 
        ALU_OP_SUB, 
        ALU_OP_XOR, 
        ALU_OP_OR, 
        ALU_OP_AND,
        ALU_OP_SLL, 
        ALU_OP_SRL, 
        ALU_OP_SRA, 
        ALU_OP_SLT, 
        ALU_OP_SLTU,
        ALU_OP_LUI, 
        ALU_OP_COPY_A, 
        ALU_OP_COPY_B
    } alu_op_e;

    typedef enum logic [0:0] { ALU_A_SEL_RS1, ALU_A_SEL_PC } alu_src_a_sel_e;
    typedef enum logic [0:0] { ALU_B_SEL_RS2, ALU_B_SEL_IMM } alu_src_b_sel_e;
    typedef enum logic [1:0] { WB_SEL_ALU, WB_SEL_MEM, WB_SEL_PC_P4, WB_SEL_CSR } wb_mux_sel_e;


    //---------------------------------------------------------------------------
    // 5. Pipeline Stage Control Structure
    //---------------------------------------------------------------------------
    // AI_TAG: TYPEDEF - ctrl_signals_t - A structure containing all control signals
    // generated in Decode and passed down the pipeline.
    typedef struct packed {
        // Main ALU Control
        alu_op_e        alu_op;
        alu_src_a_sel_e alu_src_a_sel;
        alu_src_b_sel_e alu_src_b_sel;

        // Write-back Control
        wb_mux_sel_e    wb_mux_sel;
        logic           reg_write_en;

        // Memory Control
        logic           mem_read_en;
        logic           mem_write_en;

        // Branch Control
        logic           is_branch;

        // Unit Enables
        logic           mult_en;        // AI_TAG: NEW - Enable for the multiplication unit.
        logic           div_en;         // AI_TAG: NEW - Enable for the (future) division unit.
        logic           csr_cmd_en;     // AI_TAG: NEW - Enable for a CSR command execution.

        // Decoded Fields to pass through
        logic [2:0]     funct3;
    } ctrl_signals_t;


    //---------------------------------------------------------------------------
    // 6. Pipeline Register Structures
    //---------------------------------------------------------------------------
    typedef struct packed {
        addr_t pc;
        word_t instr;
        logic  valid;
    } if_id_reg_t;

    // AI_TAG: TYPEDEF - id_ex_reg_t - Decode -> Execute Pipeline Register.
    // NOTE: Added rs1_addr and rs2_addr for hazard detection.
    typedef struct packed {
        addr_t         pc;
        word_t         rs1_data;
        word_t         rs2_data;
        word_t         immediate;
        reg_addr_t     rd_addr;
        reg_addr_t     rs1_addr;       // AI_TAG: CRITICAL_UPDATE - Needed for forwarding logic.
        reg_addr_t     rs2_addr;       // AI_TAG: CRITICAL_UPDATE - Needed for forwarding logic.
        ctrl_signals_t ctrl;
    } id_ex_reg_t;

    typedef struct packed {
        word_t         alu_result;
        word_t         store_data;
        reg_addr_t     rd_addr;
        ctrl_signals_t ctrl;
    } ex_mem_reg_t;

    typedef struct packed {
        word_t         wb_data;
        reg_addr_t     rd_addr;
        logic          reg_write_en;
        wb_mux_sel_e   wb_mux_sel;
    } mem_wb_reg_t;


    //---------------------------------------------------------------------------
    // 7. CSR Definitions (M-Mode)
    //---------------------------------------------------------------------------
    parameter logic [11:0] MSTATUS_ADDR = 12'h300;
    parameter logic [11:0] MISA_ADDR    = 12'h301;
    parameter logic [11:0] MIE_ADDR     = 12'h304;
    parameter logic [11:0] MTVEC_ADDR   = 12'h305;
    parameter logic [11:0] MSCRATCH_ADDR= 12'h340;
    parameter logic [11:0] MEPC_ADDR    = 12'h341;
    parameter logic [11:0] MCAUSE_ADDR  = 12'h342;
    parameter logic [11:0] MTVAL_ADDR   = 12'h343;
    parameter logic [11:0] MIP_ADDR     = 12'h344;
    parameter logic [11:0] MHARTID_ADDR = 12'hF14;


endpackage : riscv_core_pkg

`default_nettype wire