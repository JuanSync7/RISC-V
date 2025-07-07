//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_verif_types_pkg.sv
// Module: riscv_verif_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains all shared parameters, data types, and enumerations related to
//   verification and testing.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_verif_types_pkg;

    import riscv_types_pkg::*;
    import riscv_config_pkg::*;

    //---------------------------------------------------------------------------
    // 1. Test Configuration Parameters
    //---------------------------------------------------------------------------
    parameter integer VERIF_CLK_PERIOD = CONFIG_CLK_PERIOD;
    parameter integer VERIF_TIMEOUT_CYCLES = CONFIG_TIMEOUT_CYCLES;
    parameter integer VERIF_MAX_TEST_ITERATIONS = CONFIG_MAX_TEST_ITERATIONS;

    //---------------------------------------------------------------------------
    // 2. Test Status Enumeration
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        TEST_PASS = 2'b00,
        TEST_FAIL = 2'b01,
        TEST_TIMEOUT = 2'b10,
        TEST_SKIP = 2'b11
    } test_result_e;

    //---------------------------------------------------------------------------
    // 3. Test Statistics Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        integer total_tests;
        integer passed_tests;
        integer failed_tests;
        integer timeout_tests;
        integer skipped_tests;
        real pass_rate;
        integer total_cycles;
        real simulation_time;
    } test_stats_t;

    //---------------------------------------------------------------------------
    // 4. Test Categories
    //---------------------------------------------------------------------------
    typedef enum {
        FUNCTIONAL_TEST,
        PERFORMANCE_TEST,
        STRESS_TEST,
        CORNER_CASE_TEST,
        REGRESSION_TEST,
        INTEGRATION_TEST,
        SYSTEM_TEST
    } test_category_e;

    //---------------------------------------------------------------------------
    // 5. Test Priority Levels
    //---------------------------------------------------------------------------
    typedef enum {
        CRITICAL,
        HIGH,
        MEDIUM,
        LOW
    } test_priority_e;

    //---------------------------------------------------------------------------
    // 6. Transaction Types
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [31:0] operand_a;
        logic [31:0] operand_b;
        logic [3:0] operation;
        logic [31:0] result;
        logic zero_flag;
        logic overflow_flag;
        time timestamp;
    } alu_transaction_t;

    typedef struct packed {
        logic [31:0] address;
        logic [31:0] write_data;
        logic [31:0] read_data;
        logic [2:0] size;
        logic [3:0] strb;
        logic read_write;
        logic valid;
        time timestamp;
    } memory_transaction_t;

    //---------------------------------------------------------------------------
    // 7. Verification Functions
    //---------------------------------------------------------------------------
    function automatic word_t random_word();
        return $random;
    endfunction

    function automatic addr_t random_addr();
        return $random & 32'hFFFF_FFFF;
    endfunction

    function automatic logic [4:0] random_reg_addr();
        return $random & 5'h1F;
    endfunction

endpackage : riscv_verif_types_pkg 