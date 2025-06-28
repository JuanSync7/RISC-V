//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: test_utils.sv
// Module: test_utils
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Common testbench utilities for unit testing. Provides shared functions,
//   tasks, and macros for consistent testbench development across all
//   modules in the RISC-V project.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package test_utils;
    import riscv_core_pkg::*;

    //===========================================================================
    // Test Configuration Parameters
    //===========================================================================
    parameter integer CLK_PERIOD = 10;        // 100MHz clock
    parameter integer TIMEOUT_CYCLES = 1000;  // Timeout for tests
    parameter integer MAX_TEST_ITERATIONS = 100; // Max iterations for random tests

    //===========================================================================
    // Test Status Enumeration
    //===========================================================================
    typedef enum logic [1:0] {
        TEST_PASS = 2'b00,
        TEST_FAIL = 2'b01,
        TEST_TIMEOUT = 2'b10,
        TEST_SKIP = 2'b11
    } test_result_e;

    //===========================================================================
    // Test Statistics Structure
    //===========================================================================
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

    //===========================================================================
    // Clock Generation Task
    //===========================================================================
    task automatic generate_clock(ref logic clk, input integer period);
        clk = 0;
        forever #(period/2) clk = ~clk;
    endtask

    //===========================================================================
    // Reset Generation Task
    //===========================================================================
    task automatic generate_reset(ref logic rst_n, input integer cycles);
        rst_n = 0;
        repeat(cycles) @(posedge clk);
        rst_n = 1;
    endtask

    //===========================================================================
    // Wait for Signal Task
    //===========================================================================
    task automatic wait_for_signal(input logic signal, input integer max_cycles);
        integer cycle_count = 0;
        while (!signal && cycle_count < max_cycles) begin
            @(posedge clk);
            cycle_count++;
        end
        if (cycle_count >= max_cycles) begin
            $error("Timeout waiting for signal after %0d cycles", max_cycles);
        end
    endtask

    //===========================================================================
    // Random Word Generation
    //===========================================================================
    function automatic word_t random_word();
        return $random;
    endfunction

    //===========================================================================
    // Random Address Generation
    //===========================================================================
    function automatic addr_t random_addr();
        return $random & 32'hFFFF_FFFF;
    endfunction

    //===========================================================================
    // Random Register Address Generation
    //===========================================================================
    function automatic reg_addr_t random_reg_addr();
        return $random & 5'h1F;
    endfunction

    //===========================================================================
    // Random Instruction Generation
    //===========================================================================
    function automatic word_t random_instruction();
        return $random;
    endfunction

    //===========================================================================
    // Test Result Recording
    //===========================================================================
    task automatic record_test_result(
        input string test_name,
        input test_result_e result,
        ref test_stats_t stats
    );
        stats.total_tests++;
        case (result)
            TEST_PASS: stats.passed_tests++;
            TEST_FAIL: stats.failed_tests++;
            TEST_TIMEOUT: stats.timeout_tests++;
            TEST_SKIP: stats.skipped_tests++;
        endcase
        
        stats.pass_rate = real'(stats.passed_tests) / real'(stats.total_tests) * 100.0;
        
        case (result)
            TEST_PASS: $display("[PASS] %s", test_name);
            TEST_FAIL: $display("[FAIL] %s", test_name);
            TEST_TIMEOUT: $display("[TIMEOUT] %s", test_name);
            TEST_SKIP: $display("[SKIP] %s", test_name);
        endcase
    endtask

    //===========================================================================
    // Test Statistics Reporting
    //===========================================================================
    task automatic report_test_stats(input test_stats_t stats);
        $display("==========================================");
        $display("TEST SUMMARY");
        $display("==========================================");
        $display("Total Tests:     %0d", stats.total_tests);
        $display("Passed:          %0d", stats.passed_tests);
        $display("Failed:          %0d", stats.failed_tests);
        $display("Timeout:         %0d", stats.timeout_tests);
        $display("Skipped:         %0d", stats.skipped_tests);
        $display("Pass Rate:       %0.1f%%", stats.pass_rate);
        $display("Total Cycles:    %0d", stats.total_cycles);
        $display("Simulation Time: %0.1f ns", stats.simulation_time);
        $display("==========================================");
    endtask

    //===========================================================================
    // Assertion Macros
    //===========================================================================
    `define ASSERT_EQ(actual, expected, message) \
        if (actual !== expected) begin \
            $error("ASSERTION FAILED: %s - Expected: %h, Got: %h", message, expected, actual); \
        end

    `define ASSERT_NEQ(actual, expected, message) \
        if (actual === expected) begin \
            $error("ASSERTION FAILED: %s - Values should not be equal: %h", message, actual); \
        end

    `define ASSERT_TRUE(condition, message) \
        if (!condition) begin \
            $error("ASSERTION FAILED: %s", message); \
        end

    `define ASSERT_FALSE(condition, message) \
        if (condition) begin \
            $error("ASSERTION FAILED: %s", message); \
        end

    //===========================================================================
    // Coverage Macros
    //===========================================================================
    `define COVER_POINT(name, signal) \
        covergroup name @(posedge clk); \
            cp: coverpoint signal; \
        endgroup

    `define COVER_CROSS(name, signal1, signal2) \
        covergroup name @(posedge clk); \
            cp1: coverpoint signal1; \
            cp2: coverpoint signal2; \
            cross cp1, cp2; \
        endgroup

    //===========================================================================
    // Test Vector Generation
    //===========================================================================
    // ALU Test Vectors
    typedef struct packed {
        word_t operand_a;
        word_t operand_b;
        logic [3:0] alu_op;
        word_t expected_result;
        logic expected_zero;
        logic expected_overflow;
    } alu_test_vector_t;

    // Register File Test Vectors
    typedef struct packed {
        reg_addr_t rs1_addr;
        reg_addr_t rs2_addr;
        reg_addr_t rd_addr;
        word_t write_data;
        logic write_enable;
        word_t expected_rs1_data;
        word_t expected_rs2_data;
    } regfile_test_vector_t;

    // Memory Test Vectors
    typedef struct packed {
        addr_t addr;
        word_t write_data;
        logic [2:0] size;
        logic [3:0] strb;
        logic write_enable;
        word_t expected_read_data;
    } memory_test_vector_t;

endpackage : test_utils

//=============================================================================
// Dependencies: riscv_core_pkg.sv
//
// Performance:
//   - Simulation Time: TBD
//   - Test Vectors: TBD
//   - Coverage: TBD
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: N/A (testbench utilities)
//   - Synthesis Tool: N/A
//   - Clock Domains: 1 (clk)
//
// Testing:
//   - Testbench: N/A (utility package)
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//============================================================================= 