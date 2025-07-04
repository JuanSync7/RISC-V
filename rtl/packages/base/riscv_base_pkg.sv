//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: riscv_base_pkg.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: riscv_base_pkg
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-28
// DESCRIPTION: Base RISC-V ISA constants and architectural definitions.
// PRIMARY_PURPOSE: Define immutable RISC-V specification constants.
// ROLE_IN_SYSTEM: Foundation layer for all RISC-V packages and modules.
// PROBLEM_SOLVED: Centralizes RISC-V ISA definitions to ensure consistency.
// MODULE_TYPE: Package
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V ISA Specification v2.2
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

package riscv_base_pkg;

    //-------------------------------------------------------------------------
    // RISC-V Architecture Constants (Immutable)
    //-------------------------------------------------------------------------
    // AI_TAG: FEATURE - Defines fundamental RISC-V ISA constants per specification v2.2
    
    // Base architecture width
    localparam integer CONST_XLEN_RV32 = 32;  // RV32 architecture
    localparam integer CONST_XLEN_RV64 = 64;  // RV64 architecture
    
    // Register file constants
    localparam integer CONST_REG_COUNT = 32;
    localparam integer CONST_REG_ADDR_WIDTH = $clog2(CONST_REG_COUNT);
    localparam integer CONST_REG_ZERO = 0;  // x0 always zero
    
    //-------------------------------------------------------------------------
    // RISC-V Instruction Encoding Constants
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - RISC-V instruction format field widths
    localparam integer CONST_OPCODE_WIDTH = 7;
    localparam integer CONST_FUNCT3_WIDTH = 3;
    localparam integer CONST_FUNCT7_WIDTH = 7;
    localparam integer CONST_RS1_WIDTH = 5;
    localparam integer CONST_RS2_WIDTH = 5;
    localparam integer CONST_RD_WIDTH = 5;
    
    // Instruction format bit positions
    localparam integer CONST_OPCODE_LSB = 0;
    localparam integer CONST_OPCODE_MSB = 6;
    localparam integer CONST_RD_LSB = 7;
    localparam integer CONST_RD_MSB = 11;
    localparam integer CONST_FUNCT3_LSB = 12;
    localparam integer CONST_FUNCT3_MSB = 14;
    localparam integer CONST_RS1_LSB = 15;
    localparam integer CONST_RS1_MSB = 19;
    localparam integer CONST_RS2_LSB = 20;
    localparam integer CONST_RS2_MSB = 24;
    localparam integer CONST_FUNCT7_LSB = 25;
    localparam integer CONST_FUNCT7_MSB = 31;
    
    //-------------------------------------------------------------------------
    // RISC-V Opcodes (7-bit)
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Standard RISC-V opcode definitions
    typedef enum logic [6:0] {
        OPCODE_LUI    = 7'b0110111,  // Load Upper Immediate
        OPCODE_AUIPC  = 7'b0010111,  // Add Upper Immediate to PC
        OPCODE_JAL    = 7'b1101111,  // Jump and Link
        OPCODE_JALR   = 7'b1100111,  // Jump and Link Register
        OPCODE_BRANCH = 7'b1100011,  // Branch operations
        OPCODE_LOAD   = 7'b0000011,  // Load operations
        OPCODE_STORE  = 7'b0100011,  // Store operations
        OPCODE_OP_IMM = 7'b0010011,  // Integer immediate operations
        OPCODE_OP     = 7'b0110011,  // Integer register operations
        OPCODE_FENCE  = 7'b0001111,  // Memory ordering
        OPCODE_SYSTEM = 7'b1110011   // System operations
    } opcode_e;
    
    //-------------------------------------------------------------------------
    // Function Codes (funct3)
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - RISC-V funct3 encoding for various instruction types
    
    // Branch funct3 codes
    typedef enum logic [2:0] {
        FUNCT3_BEQ  = 3'b000,  // Branch Equal
        FUNCT3_BNE  = 3'b001,  // Branch Not Equal
        FUNCT3_BLT  = 3'b100,  // Branch Less Than (signed)
        FUNCT3_BGE  = 3'b101,  // Branch Greater Equal (signed)
        FUNCT3_BLTU = 3'b110,  // Branch Less Than (unsigned)
        FUNCT3_BGEU = 3'b111   // Branch Greater Equal (unsigned)
    } branch_funct3_e;
    
    // Load funct3 codes
    typedef enum logic [2:0] {
        FUNCT3_LB  = 3'b000,  // Load Byte
        FUNCT3_LH  = 3'b001,  // Load Halfword
        FUNCT3_LW  = 3'b010,  // Load Word
        FUNCT3_LBU = 3'b100,  // Load Byte Unsigned
        FUNCT3_LHU = 3'b101   // Load Halfword Unsigned
    } load_funct3_e;
    
    // Store funct3 codes
    typedef enum logic [2:0] {
        FUNCT3_SB = 3'b000,  // Store Byte
        FUNCT3_SH = 3'b001,  // Store Halfword
        FUNCT3_SW = 3'b010   // Store Word
    } store_funct3_e;
    
    // ALU immediate funct3 codes
    typedef enum logic [2:0] {
        FUNCT3_ADDI  = 3'b000,  // Add Immediate
        FUNCT3_SLTI  = 3'b010,  // Set Less Than Immediate
        FUNCT3_SLTIU = 3'b011,  // Set Less Than Immediate Unsigned
        FUNCT3_XORI  = 3'b100,  // XOR Immediate
        FUNCT3_ORI   = 3'b110,  // OR Immediate
        FUNCT3_ANDI  = 3'b111,  // AND Immediate
        FUNCT3_SLLI  = 3'b001,  // Shift Left Logical Immediate
        FUNCT3_SRLI  = 3'b101   // Shift Right Logical/Arithmetic Immediate
    } alu_imm_funct3_e;
    
    // ALU register funct3 codes
    typedef enum logic [2:0] {
        FUNCT3_ADD  = 3'b000,  // Add/Sub
        FUNCT3_SLL  = 3'b001,  // Shift Left Logical
        FUNCT3_SLT  = 3'b010,  // Set Less Than
        FUNCT3_SLTU = 3'b011,  // Set Less Than Unsigned
        FUNCT3_XOR  = 3'b100,  // XOR
        FUNCT3_SRL  = 3'b101,  // Shift Right Logical/Arithmetic
        FUNCT3_OR   = 3'b110,  // OR
        FUNCT3_AND  = 3'b111   // AND
    } alu_reg_funct3_e;
    
    // System funct3 codes
    typedef enum logic [2:0] {
        FUNCT3_PRIV   = 3'b000,  // Privileged instructions
        FUNCT3_CSRRW  = 3'b001,  // CSR Read/Write
        FUNCT3_CSRRS  = 3'b010,  // CSR Read/Set
        FUNCT3_CSRRC  = 3'b011,  // CSR Read/Clear
        FUNCT3_CSRRWI = 3'b101,  // CSR Read/Write Immediate
        FUNCT3_CSRRSI = 3'b110,  // CSR Read/Set Immediate
        FUNCT3_CSRRCI = 3'b111   // CSR Read/Clear Immediate
    } system_funct3_e;
    
    //-------------------------------------------------------------------------
    // Function Codes (funct7)
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - RISC-V funct7 encoding for instruction variants
    localparam logic [6:0] FUNCT7_BASE     = 7'b0000000;  // Base encoding
    localparam logic [6:0] FUNCT7_ALT      = 7'b0100000;  // Alternative encoding
    localparam logic [6:0] FUNCT7_M_EXT    = 7'b0000001;  // M-extension encoding
    
    //-------------------------------------------------------------------------
    // Special Instructions
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Common RISC-V instruction encodings
    localparam logic [31:0] CONST_NOP_INST = 32'h00000013;  // addi x0, x0, 0
    localparam logic [31:0] CONST_EBREAK   = 32'h00100073;  // ebreak
    localparam logic [31:0] CONST_ECALL    = 32'h00000073;  // ecall
    localparam logic [31:0] CONST_FENCE    = 32'h0000000F;  // fence
    localparam logic [31:0] CONST_FENCE_I  = 32'h0000100F;  // fence.i
    localparam logic [31:0] CONST_WFI      = 32'h10500073;  // wfi
    
    //-------------------------------------------------------------------------
    // M-Extension Function Codes
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - RV32M multiplication and division funct3 codes
    typedef enum logic [2:0] {
        FUNCT3_MUL    = 3'b000,  // Multiply
        FUNCT3_MULH   = 3'b001,  // Multiply High (signed×signed)
        FUNCT3_MULHSU = 3'b010,  // Multiply High (signed×unsigned)
        FUNCT3_MULHU  = 3'b011,  // Multiply High (unsigned×unsigned)
        FUNCT3_DIV    = 3'b100,  // Divide (signed)
        FUNCT3_DIVU   = 3'b101,  // Divide (unsigned)
        FUNCT3_REM    = 3'b110,  // Remainder (signed)
        FUNCT3_REMU   = 3'b111   // Remainder (unsigned)
    } m_ext_funct3_e;
    
    //-------------------------------------------------------------------------
    // Exception Cause Codes
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - RISC-V standard exception cause codes
    typedef enum logic [31:0] {
        CAUSE_MISALIGNED_FETCH       = 32'h00000000,
        CAUSE_FETCH_ACCESS          = 32'h00000001,
        CAUSE_ILLEGAL_INSTRUCTION   = 32'h00000002,
        CAUSE_BREAKPOINT            = 32'h00000003,
        CAUSE_MISALIGNED_LOAD       = 32'h00000004,
        CAUSE_LOAD_ACCESS           = 32'h00000005,
        CAUSE_MISALIGNED_STORE      = 32'h00000006,
        CAUSE_STORE_ACCESS          = 32'h00000007,
        CAUSE_ECALL_U               = 32'h00000008,
        CAUSE_ECALL_S               = 32'h00000009,
        CAUSE_ECALL_M               = 32'h0000000B,
        CAUSE_FETCH_PAGE_FAULT      = 32'h0000000C,
        CAUSE_LOAD_PAGE_FAULT       = 32'h0000000D,
        CAUSE_STORE_PAGE_FAULT      = 32'h0000000F,
        // Interrupt causes (MSB set)
        CAUSE_M_SOFTWARE_INT        = 32'h80000003,
        CAUSE_M_TIMER_INT           = 32'h80000007,
        CAUSE_M_EXTERNAL_INT        = 32'h8000000B
    } exception_cause_e;
    
    //-------------------------------------------------------------------------
    // CSR Addresses
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - RISC-V Control and Status Register addresses
    
    // Machine-level CSRs
    typedef enum logic [11:0] {
        CSR_MSTATUS    = 12'h300,  // Machine status
        CSR_MISA       = 12'h301,  // Machine ISA
        CSR_MIE        = 12'h304,  // Machine interrupt enable
        CSR_MTVEC      = 12'h305,  // Machine trap vector
        CSR_MSCRATCH   = 12'h340,  // Machine scratch
        CSR_MEPC       = 12'h341,  // Machine exception PC
        CSR_MCAUSE     = 12'h342,  // Machine cause
        CSR_MTVAL      = 12'h343,  // Machine trap value
        CSR_MIP        = 12'h344,  // Machine interrupt pending
        CSR_MHARTID    = 12'hF14   // Machine hart ID
    } csr_addr_e;
    
    //-------------------------------------------------------------------------
    // Privilege Levels
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - RISC-V privilege level encoding
    typedef enum logic [1:0] {
        PRIV_U = 2'b00,  // User mode
        PRIV_S = 2'b01,  // Supervisor mode
        PRIV_M = 2'b11   // Machine mode
    } privilege_level_e;
    
    //-------------------------------------------------------------------------
    // Memory Access Types
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Memory access size encoding
    typedef enum logic [1:0] {
        MEM_SIZE_BYTE = 2'b00,  // 8-bit access
        MEM_SIZE_HALF = 2'b01,  // 16-bit access
        MEM_SIZE_WORD = 2'b10   // 32-bit access
    } mem_size_e;
    
    //-------------------------------------------------------------------------
    // Instruction Types
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - RISC-V instruction format types
    typedef enum logic [2:0] {
        INST_TYPE_R = 3'b000,  // Register type
        INST_TYPE_I = 3'b001,  // Immediate type
        INST_TYPE_S = 3'b010,  // Store type
        INST_TYPE_B = 3'b011,  // Branch type
        INST_TYPE_U = 3'b100,  // Upper immediate type
        INST_TYPE_J = 3'b101   // Jump type
    } inst_type_e;
    
    //-------------------------------------------------------------------------
    // Utility Functions
    //-------------------------------------------------------------------------
    // AI_TAG: FUNCTION - Sign extension utility
    function automatic logic [31:0] sign_extend(
        input logic [31:0] value,
        input integer width
    );
        logic sign_bit;
        sign_bit = value[width-1];
        sign_extend = {{(32-width){sign_bit}}, value[width-1:0]};
    endfunction
    
    // AI_TAG: FUNCTION - Zero extension utility
    function automatic logic [31:0] zero_extend(
        input logic [31:0] value,
        input integer width
    );
        zero_extend = {{(32-width){1'b0}}, value[width-1:0]};
    endfunction

endpackage : riscv_base_pkg

//=============================================================================
// Dependencies: None (base package)
//
// Instantiated In:
//   - All RISC-V packages and modules
//
// Performance:
//   - Critical Path: N/A (package only)
//   - Max Frequency: N/A
//   - Area: N/A
//
// Verification Coverage:
//   - Code Coverage: N/A
//   - Functional Coverage: N/A
//   - Branch Coverage: N/A
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: N/A
//   - Clock Domains: N/A
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: N/A
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author         | Description
//=============================================================================
// 1.0.0   | 2025-01-28 | DesignAI      | Initial release
//=============================================================================