//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: riscv_core_pkg.sv
// Module: riscv_core_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Central package for the RV32IM RISC-V core. Contains all shared parameters,
//   data types, enumerations, and pipeline register structures used throughout
//   the design.
//=============================================================================

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

    // AI_TAG: TYPEDEF - Updated pipeline register structures with exception info
    typedef struct packed {
        word_t         alu_result;
        word_t         store_data;
        reg_addr_t     rd_addr;
        logic          alu_overflow;   // AI_TAG: NEW - Overflow flag from ALU for exception handling
        exception_info_t exception;    // AI_TAG: NEW - Exception information
        ctrl_signals_t ctrl;
    } ex_mem_reg_t;

    typedef struct packed {
        word_t         wb_data;
        reg_addr_t     rd_addr;
        logic          reg_write_en;
        wb_mux_sel_e   wb_mux_sel;
        exception_info_t exception;    // AI_TAG: NEW - Exception information
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

    //---------------------------------------------------------------------------
    // 8. Branch Predictor Definitions
    //---------------------------------------------------------------------------
    // AI_TAG: TYPEDEF - branch_prediction_t - Branch prediction result structure
    typedef struct packed {
        logic        predict_taken;    // Prediction result (1=taken, 0=not-taken)
        addr_t       predict_target;   // Predicted branch target address
        logic        btb_hit;          // BTB hit indicator
    } branch_prediction_t;

    // AI_TAG: TYPEDEF - branch_update_t - Branch update information structure
    typedef struct packed {
        logic        update_valid;     // Update is valid
        addr_t       update_pc;        // PC of the branch being updated
        logic        actual_taken;     // Actual branch outcome
        addr_t       actual_target;    // Actual branch target
        logic        is_branch;        // Instruction is a branch
    } branch_update_t;

    // AI_TAG: CONSTANT - BPU_DEFAULT_BTB_ENTRIES - Default BTB size
    parameter integer BPU_DEFAULT_BTB_ENTRIES = 64;
    
    // AI_TAG: CONSTANT - BPU_DEFAULT_BHT_ENTRIES - Default BHT size
    parameter integer BPU_DEFAULT_BHT_ENTRIES = 256;

    //---------------------------------------------------------------------------
    // 9. Exception Handling Definitions
    //---------------------------------------------------------------------------
    // AI_TAG: TYPEDEF - exception_cause_t - Exception cause codes as per RISC-V spec
    typedef logic [31:0] exception_cause_t;

    // AI_TAG: CONSTANT - Exception Cause Codes (M-mode)
    // Interrupts (bit 31 = 1)
    parameter exception_cause_t EXC_CAUSE_M_SOFTWARE_INTERRUPT = 32'h80000003;
    parameter exception_cause_t EXC_CAUSE_M_TIMER_INTERRUPT    = 32'h80000007;
    parameter exception_cause_t EXC_CAUSE_M_EXTERNAL_INTERRUPT = 32'h8000000B;

    // Exceptions (bit 31 = 0)
    parameter exception_cause_t EXC_CAUSE_INSTR_ADDR_MISALIGNED = 32'h00000000;
    parameter exception_cause_t EXC_CAUSE_INSTR_ACCESS_FAULT   = 32'h00000001;
    parameter exception_cause_t EXC_CAUSE_ILLEGAL_INSTRUCTION  = 32'h00000002;
    parameter exception_cause_t EXC_CAUSE_BREAKPOINT          = 32'h00000003;
    parameter exception_cause_t EXC_CAUSE_LOAD_ADDR_MISALIGNED = 32'h00000004;
    parameter exception_cause_t EXC_CAUSE_LOAD_ACCESS_FAULT   = 32'h00000005;
    parameter exception_cause_t EXC_CAUSE_STORE_ADDR_MISALIGNED = 32'h00000006;
    parameter exception_cause_t EXC_CAUSE_STORE_ACCESS_FAULT  = 32'h00000007;
    parameter exception_cause_t EXC_CAUSE_ECALL_M            = 32'h0000000B;
    parameter exception_cause_t EXC_CAUSE_INSTR_PAGE_FAULT   = 32'h0000000C;
    parameter exception_cause_t EXC_CAUSE_LOAD_PAGE_FAULT    = 32'h0000000D;
    parameter exception_cause_t EXC_CAUSE_STORE_PAGE_FAULT   = 32'h0000000F;

    // AI_TAG: TYPEDEF - exception_type_e - Exception type enumeration
    typedef enum logic [1:0] {
        EXC_TYPE_NONE = 2'b00,
        EXC_TYPE_INTERRUPT = 2'b01,
        EXC_TYPE_EXCEPTION = 2'b10,
        EXC_TYPE_RESERVED = 2'b11
    } exception_type_e;

    // AI_TAG: TYPEDEF - exception_priority_e - Exception priority encoding
    typedef enum logic [3:0] {
        PRIO_NONE = 4'd0,
        PRIO_INTERRUPT = 4'd1,
        PRIO_LOAD_FAULT = 4'd2,
        PRIO_STORE_FAULT = 4'd3,
        PRIO_INSTR_FAULT = 4'd4,
        PRIO_BREAKPOINT = 4'd5,
        PRIO_ECALL = 4'd6,
        PRIO_MISALIGNED = 4'd7,
        PRIO_ILLEGAL = 4'd8,
        PRIO_DIV_ZERO = 4'd9,
        PRIO_OVERFLOW = 4'd10
    } exception_priority_e;

    // AI_TAG: TYPEDEF - exception_info_t - Exception information structure
    typedef struct packed {
        logic              valid;           // Exception is valid
        exception_type_e   exc_type;        // Exception type (interrupt/exception)
        exception_cause_t  cause;           // Exception cause code
        addr_t             pc;              // PC where exception occurred
        word_t             tval;            // Exception-specific value
        exception_priority_e priority;      // Exception priority
    } exception_info_t;

    // AI_TAG: TYPEDEF - interrupt_info_t - Interrupt information structure
    typedef struct packed {
        logic              m_software_interrupt;  // Machine software interrupt
        logic              m_timer_interrupt;     // Machine timer interrupt
        logic              m_external_interrupt;  // Machine external interrupt
        logic              interrupt_pending;     // Any interrupt is pending
        exception_cause_t  interrupt_cause;       // Highest priority interrupt cause
    } interrupt_info_t;

    // AI_TAG: TYPEDEF - trap_vector_t - Trap vector information
    typedef struct packed {
        addr_t             base_addr;       // Base address from mtvec
        logic [1:0]        mode;            // Vector mode (00=direct, 01=vectored)
        addr_t             vector_addr;     // Calculated vector address
    } trap_vector_t;

endpackage : riscv_core_pkg

//=============================================================================
// Dependencies: None
//
// Performance:
//   - Critical Path: N/A (package file)
//   - Max Frequency: N/A
//   - Area: N/A
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: N/A (package file)
//
// Testing:
//   - Testbench: N/A (package file)
//   - Test Vectors: N/A
//   - Simulation Time: N/A
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//=============================================================================
// NOTE: `default_nettype wire is set below for legacy compatibility. Prefer keeping `none` throughout the project and explicitly typing all signals. Remove if not required.
`default_nettype wire
