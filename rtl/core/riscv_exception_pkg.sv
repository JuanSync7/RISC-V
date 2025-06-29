//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_exception_pkg.sv
// Module: riscv_exception_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains all shared parameters, data types, and constants related to
//   the RISC-V exception and interrupt handling mechanism.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_exception_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    //---------------------------------------------------------------------------
    // 1. Exception Cause Definitions (now from config package)
    //---------------------------------------------------------------------------
    // All exception cause codes are now imported from riscv_config_pkg:
    // CAUSE_*, MSTATUS_ADDR, MISA_ADDR, etc.

    //---------------------------------------------------------------------------
    // 2. Exception Information Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        valid;
        logic [31:0] cause;
        addr_t       pc;
        word_t       tval;
        logic        interrupt;
        logic        exception;
    } exception_info_t;

    //---------------------------------------------------------------------------
    // 3. Interrupt Vector Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        software_int;
        logic        timer_int;
        logic        external_int;
        logic [15:0] reserved;
    } interrupt_vector_t;

    //---------------------------------------------------------------------------
    // 4. CSR Register Structures
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [1:0]  mpp;      // Machine previous privilege mode
        logic [1:0]  mpie;     // Machine previous interrupt enable
        logic        mie;      // Machine interrupt enable
        logic        mprv;     // Machine privilege mode
        logic [1:0]  xs;       // Extension status
        logic [1:0]  fs;       // Floating-point status
        logic [3:0]  mxl;      // Machine XLEN
        logic [15:0] reserved;
    } mstatus_t;

    typedef struct packed {
        logic [25:0] base;     // Base address for trap vector
        logic [1:0]  mode;     // Trap vector mode
        logic [3:0]  reserved;
    } mtvec_t;

    typedef struct packed {
        logic        msie;     // Machine software interrupt enable
        logic        mtie;     // Machine timer interrupt enable
        logic        meie;     // Machine external interrupt enable
        logic [29:0] reserved;
    } mie_t;

    typedef struct packed {
        logic        msip;     // Machine software interrupt pending
        logic        mtip;     // Machine timer interrupt pending
        logic        meip;     // Machine external interrupt pending
        logic [29:0] reserved;
    } mip_t;

    //---------------------------------------------------------------------------
    // 5. Exception Priority and Handling
    //---------------------------------------------------------------------------
    typedef enum logic [3:0] {
        PRIORITY_NONE = 4'd0,
        PRIORITY_SOFTWARE = 4'd1,
        PRIORITY_TIMER = 4'd2,
        PRIORITY_EXTERNAL = 4'd3,
        PRIORITY_INSTRUCTION_FAULT = 4'd4,
        PRIORITY_LOAD_FAULT = 4'd5,
        PRIORITY_STORE_FAULT = 4'd6,
        PRIORITY_ECALL = 4'd7,
        PRIORITY_BREAKPOINT = 4'd8
    } exception_priority_e;

    //---------------------------------------------------------------------------
    // 6. Exception Handler States
    //---------------------------------------------------------------------------
    typedef enum logic [2:0] {
        EXCEPTION_IDLE,
        EXCEPTION_SAVE_CONTEXT,
        EXCEPTION_UPDATE_CSR,
        EXCEPTION_JUMP_TO_HANDLER,
        EXCEPTION_RESTORE_CONTEXT,
        EXCEPTION_RETURN
    } exception_state_e;

    //---------------------------------------------------------------------------
    // 7. Exception Cause Validation
    //---------------------------------------------------------------------------
    function automatic logic is_valid_exception_cause(input logic [31:0] cause);
        case (cause)
            CAUSE_MISALIGNED_FETCH,
            CAUSE_FETCH_ACCESS,
            CAUSE_ILLEGAL_INSTRUCTION,
            CAUSE_BREAKPOINT,
            CAUSE_MISALIGNED_LOAD,
            CAUSE_LOAD_ACCESS,
            CAUSE_MISALIGNED_STORE,
            CAUSE_STORE_ACCESS,
            CAUSE_ECALL_U,
            CAUSE_ECALL_S,
            CAUSE_ECALL_M,
            CAUSE_INSTRUCTION_PAGE_FAULT,
            CAUSE_LOAD_PAGE_FAULT,
            CAUSE_STORE_PAGE_FAULT: return 1'b1;
            default: return 1'b0;
        endcase
    endfunction

    function automatic logic is_valid_interrupt_cause(input logic [31:0] cause);
        case (cause)
            CAUSE_M_SOFTWARE_INTERRUPT,
            CAUSE_M_TIMER_INTERRUPT,
            CAUSE_M_EXTERNAL_INTERRUPT: return 1'b1;
            default: return 1'b0;
        endcase
    endfunction

    //---------------------------------------------------------------------------
    // 8. Exception Priority Functions
    //---------------------------------------------------------------------------
    function automatic exception_priority_e get_exception_priority(input logic [31:0] cause);
        case (cause)
            CAUSE_M_SOFTWARE_INTERRUPT: return PRIORITY_SOFTWARE;
            CAUSE_M_TIMER_INTERRUPT: return PRIORITY_TIMER;
            CAUSE_M_EXTERNAL_INTERRUPT: return PRIORITY_EXTERNAL;
            CAUSE_INSTRUCTION_PAGE_FAULT: return PRIORITY_INSTRUCTION_FAULT;
            CAUSE_LOAD_PAGE_FAULT: return PRIORITY_LOAD_FAULT;
            CAUSE_STORE_PAGE_FAULT: return PRIORITY_STORE_FAULT;
            CAUSE_ECALL_U, CAUSE_ECALL_S, CAUSE_ECALL_M: return PRIORITY_ECALL;
            CAUSE_BREAKPOINT: return PRIORITY_BREAKPOINT;
            default: return PRIORITY_NONE;
        endcase
    endfunction

endpackage : riscv_exception_pkg 