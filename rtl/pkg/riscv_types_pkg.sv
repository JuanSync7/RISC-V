//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V Core
//
// File: riscv_types_pkg.sv
//
// MODULE_NAME: riscv_types_pkg
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-07-07
// DESCRIPTION: Contains fixed, internal type definitions for the RISC-V core.
//              This package should not be modified by the user.
// MODULE_TYPE: Package
//=============================================================================

package riscv_types_pkg;
    import riscv_config_pkg::*;

    // -- Basic Types --
    typedef logic [CONFIG_XLEN-1:0] word_t;
    typedef logic [CONFIG_REG_ADDR_WIDTH-1:0] reg_addr_t;
    typedef logic [31:0]            inst_t;
    typedef logic [CONFIG_ADDR_WIDTH-1:0] addr_t;

    // -- ALU Operations --
    typedef enum logic [3:0] {
        ALU_ADD, ALU_SUB, ALU_XOR, ALU_OR, ALU_AND,
        ALU_SLL, ALU_SRL, ALU_SRA, ALU_SLT, ALU_SLTU
    } alu_op_e;

    // -- Pipeline Stage Structs --
    typedef struct packed {
        addr_t   pc;
        inst_t   inst;
        logic    valid;
    } fetch_decode_t;

    typedef struct packed {
        addr_t      pc;
        word_t      operand_a;
        word_t      operand_b;
        reg_addr_t  rd_addr;
        alu_op_e    alu_op;
        logic       is_branch;
        logic       is_jump;
        logic       is_mem_read;
        logic       is_mem_write;
        logic       valid;
    } decode_execute_t;

    // ... other pipeline structs to be defined as needed ...

endpackage