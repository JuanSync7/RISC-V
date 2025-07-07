//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_ooo_types_pkg.sv
// Module: riscv_ooo_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains all shared parameters, data types, and enumerations related to
//   the out-of-order execution engine. This includes definitions for the
//   Reorder Buffer, Reservation Stations, and the Common Data Bus.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_ooo_types_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;
    import riscv_exception_pkg::*;
    import riscv_core_types_pkg::*;

    //---------------------------------------------------------------------------
    // 1. Out-of-Order Engine Parameters (now from config package)
    //---------------------------------------------------------------------------
    // All OoO parameters are now imported from riscv_config_pkg:
    // DEFAULT_ROB_SIZE, DEFAULT_RS_SIZE, DEFAULT_PHYS_REGS
    // DEFAULT_NUM_ALU_UNITS, DEFAULT_NUM_MULT_UNITS, DEFAULT_NUM_DIV_UNITS
    // DEFAULT_DIV_LATENCY

    //---------------------------------------------------------------------------
    // 2. Type Definitions for OoO Identifiers
    //---------------------------------------------------------------------------
    typedef logic [$clog2(CONFIG_ROB_SIZE)-1:0]   rob_tag_t;
    typedef logic [$clog2(CONFIG_RS_SIZE)-1:0]    rs_tag_t;
    typedef logic [$clog2(CONFIG_PHYS_REGS)-1:0]  phys_reg_addr_t;
    typedef logic [REG_ADDR_WIDTH-1:0]             arch_reg_addr_t;

    //---------------------------------------------------------------------------
    // 3. Reorder Buffer Entry Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        valid;          // Entry is valid
        logic        ready;          // Result is ready
        logic        exception;      // Exception occurred
        logic [31:0] exception_cause; // Exception cause
        addr_t       pc;             // Program counter
        word_t       result;         // Execution result
        arch_reg_addr_t rd_addr;     // Destination register
        logic        reg_write;      // Write to register file
        logic        mem_read;       // Memory read operation
        logic        mem_write;      // Memory write operation
        logic        branch;         // Branch instruction
        logic        jump;           // Jump instruction
        logic        csr_read;       // CSR read operation
        logic        csr_write;      // CSR write operation
        logic [11:0] csr_addr;       // CSR address
    } rob_entry_t;

    //---------------------------------------------------------------------------
    // 4. Reservation Station Entry Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        busy;           // Entry is busy
        logic        valid;          // Entry is valid
        word_t       instruction;    // Instruction
        addr_t       pc;             // Program counter
        rob_tag_t    rob_tag;        // ROB tag
        arch_reg_addr_t rd_addr;     // Destination register
        word_t       rs1_data;       // RS1 data (if ready)
        word_t       rs2_data;       // RS2 data (if ready)
        logic        rs1_ready;      // RS1 is ready
        logic        rs2_ready;      // RS2 is ready
        rob_tag_t    rs1_tag;        // RS1 ROB tag (if not ready)
        rob_tag_t    rs2_tag;        // RS2 ROB tag (if not ready)
        logic        mem_read;       // Memory read operation
        logic        mem_write;      // Memory write operation
        logic        branch;         // Branch instruction
        logic        jump;           // Jump instruction
        logic        csr_read;       // CSR read operation
        logic        csr_write;      // CSR write operation
        logic [11:0] csr_addr;       // CSR address
    } rs_entry_t;

    //---------------------------------------------------------------------------
    // 5. Common Data Bus Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        valid;          // Result is valid
        rob_tag_t    rob_tag;        // ROB tag
        word_t       result;         // Execution result
        logic        exception;      // Exception occurred
        logic [31:0] exception_cause; // Exception cause
        logic [3:0]  fu_id;          // Functional unit ID
    } cdb_entry_t;

    //---------------------------------------------------------------------------
    // 6. Register Renaming Table Entry
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        busy;           // Register is busy
        rob_tag_t    rob_tag;        // ROB tag for this register
        word_t       data;           // Register data (if ready)
        logic        ready;          // Data is ready
    } rename_table_entry_t;

    //---------------------------------------------------------------------------
    // 7. Functional Unit Types
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        FU_ALU,      // Arithmetic Logic Unit
        FU_MULT,     // Multiplier
        FU_DIV,      // Divider
        FU_MEM       // Memory Unit
    } fu_type_e;

    //---------------------------------------------------------------------------
    // 8. Instruction Issue Types
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        ISSUE_READY,     // Instruction ready to issue
        ISSUE_WAITING,   // Waiting for operands
        ISSUE_BLOCKED,   // Blocked by structural hazard
        ISSUE_EXECUTING  // Currently executing
    } issue_state_e;

    //---------------------------------------------------------------------------
    // 9. OoO Performance Counters
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [31:0] instructions_issued;
        logic [31:0] instructions_executed;
        logic [31:0] instructions_committed;
        logic [31:0] cycles;
        logic [31:0] stalls;
        logic [31:0] branch_mispredicts;
        logic [31:0] exceptions;
        logic [31:0] rob_full_stalls;
        logic [31:0] rs_full_stalls;
        logic [31:0] cdb_full_stalls;
    } ooo_perf_counters_t;

    //---------------------------------------------------------------------------
    // 10. OoO Configuration Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        integer rob_size;
        integer rs_size;
        integer phys_regs;
        integer num_alu_units;
        integer num_mult_units;
        integer num_div_units;
        integer div_latency;
    } ooo_config_t;

    //---------------------------------------------------------------------------
    // 11. OoO State Machine
    //---------------------------------------------------------------------------
    typedef enum logic [2:0] {
        OOO_IDLE,        // Idle state
        OOO_ISSUE,       // Issuing instructions
        OOO_EXECUTE,     // Executing instructions
        OOO_COMMIT,      // Committing instructions
        OOO_FLUSH,       // Flushing pipeline
        OOO_EXCEPTION    // Handling exception
    } ooo_state_e;

    //---------------------------------------------------------------------------
    // 12. OoO Functions
    //---------------------------------------------------------------------------
    function automatic logic is_alu_instruction(input word_t instruction);
        logic [6:0] opcode;
        logic [6:0] funct7;
        
        opcode = instruction[6:0];
        funct7 = instruction[31:25];
        
        case (opcode)
            OPCODE_OP_IMM: return 1'b1;
            OPCODE_OP: return (funct7 != FUNCT7_M_EXT);
            default: return 1'b0;
        endcase
    endfunction

    function automatic logic is_mult_instruction(input word_t instruction);
        logic [6:0] opcode;
        logic [6:0] funct7;
        logic [2:0] funct3;
        
        opcode = instruction[6:0];
        funct7 = instruction[31:25];
        funct3 = instruction[14:12];
        
        return (opcode == OPCODE_OP) && (funct7 == FUNCT7_M_EXT) && 
               (funct3 == 3'b000 || funct3 == 3'b001 || funct3 == 3'b010 || funct3 == 3'b011);
    endfunction

    function automatic logic is_div_instruction(input word_t instruction);
        logic [6:0] opcode;
        logic [6:0] funct7;
        logic [2:0] funct3;
        
        opcode = instruction[6:0];
        funct7 = instruction[31:25];
        funct3 = instruction[14:12];
        
        return (opcode == OPCODE_OP) && (funct7 == FUNCT7_M_EXT) && 
               (funct3 == 3'b100 || funct3 == 3'b101 || funct3 == 3'b110 || funct3 == 3'b111);
    endfunction

    function automatic logic is_memory_instruction(input word_t instruction);
        logic [6:0] opcode;
        
        opcode = instruction[6:0];
        return (opcode == OPCODE_LOAD) || (opcode == OPCODE_STORE);
    endfunction

    function automatic fu_type_e get_fu_type(input word_t instruction);
        if (is_alu_instruction(instruction)) return FU_ALU;
        else if (is_mult_instruction(instruction)) return FU_MULT;
        else if (is_div_instruction(instruction)) return FU_DIV;
        else if (is_memory_instruction(instruction)) return FU_MEM;
        else return FU_ALU; // Default to ALU
    endfunction

    function automatic integer get_fu_latency(input fu_type_e fu_type);
        case (fu_type)
            FU_ALU: return 1;
            FU_MULT: return 3;
            FU_DIV: return DEFAULT_DIV_LATENCY;
            FU_MEM: return 2;
            default: return 1;
        endcase
    endfunction

endpackage : riscv_ooo_types_pkg