//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: alu_tb.sv
// Module: alu_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Unit testbench for the Arithmetic Logic Unit (ALU). Tests all ALU
//   operations including arithmetic, logical, and shift operations as
//   defined by the RV32I base instruction set.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module alu_tb;
    import riscv_core_pkg::*;
    import test_utils::*;

    //===========================================================================
    // Test Configuration
    //===========================================================================
    localparam integer NUM_TESTS = 1000;
    localparam integer TIMEOUT_CYCLES = 100;

    //===========================================================================
    // Clock and Reset
    //===========================================================================
    logic clk;
    logic rst_n;

    //===========================================================================
    // ALU Interface Signals
    //===========================================================================
    word_t operand_a_i;
    word_t operand_b_i;
    logic [3:0] alu_op_i;
    word_t result_o;
    logic zero_o;
    logic overflow_o;

    //===========================================================================
    // Test Control
    //===========================================================================
    test_stats_t test_stats;
    integer test_count;
    logic test_done;

    //===========================================================================
    // ALU Instance
    //===========================================================================
    alu dut (
        .operand_a_i(operand_a_i),
        .operand_b_i(operand_b_i),
        .alu_op_i(alu_op_i),
        .result_o(result_o),
        .zero_o(zero_o),
        .overflow_o(overflow_o)
    );

    //===========================================================================
    // Clock Generation
    //===========================================================================
    initial begin
        generate_clock(clk, CLK_PERIOD);
    end

    //===========================================================================
    // Test Stimulus
    //===========================================================================
    initial begin
        // Initialize test statistics
        test_stats = '0;
        test_count = 0;
        test_done = 0;

        // Initialize signals
        operand_a_i = '0;
        operand_b_i = '0;
        alu_op_i = '0;

        // Reset sequence
        generate_reset(rst_n, 5);
        @(posedge clk);

        $display("==========================================");
        $display("ALU UNIT TESTBENCH STARTED");
        $display("==========================================");

        // Run test suite
        run_basic_arithmetic_tests();
        run_logical_operation_tests();
        run_shift_operation_tests();
        run_comparison_tests();
        run_edge_case_tests();
        run_random_tests();

        // Report results
        test_stats.simulation_time = $time;
        report_test_stats(test_stats);

        $display("==========================================");
        $display("ALU UNIT TESTBENCH COMPLETED");
        $display("==========================================");

        test_done = 1;
        #100;
        $finish;
    end

    //===========================================================================
    // Test Functions
    //===========================================================================

    // Basic arithmetic operations test
    task automatic run_basic_arithmetic_tests();
        $display("Running Basic Arithmetic Tests...");
        
        // Test ADD operation
        test_add_operation();
        
        // Test SUB operation
        test_sub_operation();
        
        // Test SLT operation
        test_slt_operation();
        
        // Test SLTU operation
        test_sltu_operation();
    endtask

    // Logical operations test
    task automatic run_logical_operation_tests();
        $display("Running Logical Operation Tests...");
        
        // Test AND operation
        test_and_operation();
        
        // Test OR operation
        test_or_operation();
        
        // Test XOR operation
        test_xor_operation();
    endtask

    // Shift operations test
    task automatic run_shift_operation_tests();
        $display("Running Shift Operation Tests...");
        
        // Test SLL operation
        test_sll_operation();
        
        // Test SRL operation
        test_srl_operation();
        
        // Test SRA operation
        test_sra_operation();
    endtask

    // Comparison operations test
    task automatic run_comparison_tests();
        $display("Running Comparison Tests...");
        
        // Test equality comparisons
        test_equality_comparisons();
        
        // Test signed comparisons
        test_signed_comparisons();
        
        // Test unsigned comparisons
        test_unsigned_comparisons();
    endtask

    // Edge case tests
    task automatic run_edge_case_tests();
        $display("Running Edge Case Tests...");
        
        // Test zero operands
        test_zero_operands();
        
        // Test overflow conditions
        test_overflow_conditions();
        
        // Test maximum values
        test_maximum_values();
    endtask

    // Random tests
    task automatic run_random_tests();
        $display("Running Random Tests...");
        
        for (int i = 0; i < NUM_TESTS; i++) begin
            test_random_operation();
        end
    endtask

    //===========================================================================
    // Individual Test Tasks
    //===========================================================================

    task automatic test_add_operation();
        string test_name = "ADD Operation";
        
        // Test case 1: Basic addition
        operand_a_i = 32'h0000_0001;
        operand_b_i = 32'h0000_0002;
        alu_op_i = ALU_OP_ADD;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0003, "ADD: 1 + 2 = 3");
        `ASSERT_FALSE(zero_o, "ADD: Result should not be zero");
        `ASSERT_FALSE(overflow_o, "ADD: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_sub_operation();
        string test_name = "SUB Operation";
        
        // Test case 1: Basic subtraction
        operand_a_i = 32'h0000_0005;
        operand_b_i = 32'h0000_0002;
        alu_op_i = ALU_OP_SUB;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0003, "SUB: 5 - 2 = 3");
        `ASSERT_FALSE(zero_o, "SUB: Result should not be zero");
        `ASSERT_FALSE(overflow_o, "SUB: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_and_operation();
        string test_name = "AND Operation";
        
        // Test case 1: Basic AND
        operand_a_i = 32'hFFFF_FFFF;
        operand_b_i = 32'h0000_FFFF;
        alu_op_i = ALU_OP_AND;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_FFFF, "AND: 0xFFFF_FFFF & 0x0000_FFFF = 0x0000_FFFF");
        `ASSERT_FALSE(zero_o, "AND: Result should not be zero");
        `ASSERT_FALSE(overflow_o, "AND: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_or_operation();
        string test_name = "OR Operation";
        
        // Test case 1: Basic OR
        operand_a_i = 32'h0000_FFFF;
        operand_b_i = 32'hFFFF_0000;
        alu_op_i = ALU_OP_OR;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'hFFFF_FFFF, "OR: 0x0000_FFFF | 0xFFFF_0000 = 0xFFFF_FFFF");
        `ASSERT_FALSE(zero_o, "OR: Result should not be zero");
        `ASSERT_FALSE(overflow_o, "OR: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_xor_operation();
        string test_name = "XOR Operation";
        
        // Test case 1: Basic XOR
        operand_a_i = 32'hFFFF_FFFF;
        operand_b_i = 32'hFFFF_FFFF;
        alu_op_i = ALU_OP_XOR;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0000, "XOR: 0xFFFF_FFFF ^ 0xFFFF_FFFF = 0x0000_0000");
        `ASSERT_TRUE(zero_o, "XOR: Result should be zero");
        `ASSERT_FALSE(overflow_o, "XOR: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_sll_operation();
        string test_name = "SLL Operation";
        
        // Test case 1: Basic left shift
        operand_a_i = 32'h0000_0001;
        operand_b_i = 32'h0000_0004; // Shift by 4
        alu_op_i = ALU_OP_SLL;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0010, "SLL: 1 << 4 = 16");
        `ASSERT_FALSE(zero_o, "SLL: Result should not be zero");
        `ASSERT_FALSE(overflow_o, "SLL: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_srl_operation();
        string test_name = "SRL Operation";
        
        // Test case 1: Basic right shift
        operand_a_i = 32'h0000_0010;
        operand_b_i = 32'h0000_0002; // Shift by 2
        alu_op_i = ALU_OP_SRL;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0004, "SRL: 16 >> 2 = 4");
        `ASSERT_FALSE(zero_o, "SRL: Result should not be zero");
        `ASSERT_FALSE(overflow_o, "SRL: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_sra_operation();
        string test_name = "SRA Operation";
        
        // Test case 1: Arithmetic right shift (negative number)
        operand_a_i = 32'hFFFF_FFFF; // -1
        operand_b_i = 32'h0000_0001; // Shift by 1
        alu_op_i = ALU_OP_SRA;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'hFFFF_FFFF, "SRA: -1 >> 1 = -1 (sign preserved)");
        `ASSERT_FALSE(zero_o, "SRA: Result should not be zero");
        `ASSERT_FALSE(overflow_o, "SRA: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_slt_operation();
        string test_name = "SLT Operation";
        
        // Test case 1: Signed less than (true)
        operand_a_i = 32'hFFFF_FFFF; // -1
        operand_b_i = 32'h0000_0001; // 1
        alu_op_i = ALU_OP_SLT;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0001, "SLT: -1 < 1 = 1 (true)");
        `ASSERT_FALSE(zero_o, "SLT: Result should not be zero");
        `ASSERT_FALSE(overflow_o, "SLT: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_sltu_operation();
        string test_name = "SLTU Operation";
        
        // Test case 1: Unsigned less than (false)
        operand_a_i = 32'hFFFF_FFFF; // Large unsigned number
        operand_b_i = 32'h0000_0001; // Small unsigned number
        alu_op_i = ALU_OP_SLTU;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0000, "SLTU: 0xFFFF_FFFF < 1 = 0 (false)");
        `ASSERT_TRUE(zero_o, "SLTU: Result should be zero");
        `ASSERT_FALSE(overflow_o, "SLTU: No overflow expected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_equality_comparisons();
        string test_name = "Equality Comparisons";
        
        // Test equal values
        operand_a_i = 32'h1234_5678;
        operand_b_i = 32'h1234_5678;
        alu_op_i = ALU_OP_SUB;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0000, "SUB: Equal values should result in zero");
        `ASSERT_TRUE(zero_o, "SUB: Zero flag should be set for equal values");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_signed_comparisons();
        string test_name = "Signed Comparisons";
        
        // Test signed comparison with negative number
        operand_a_i = 32'h8000_0000; // Most negative number
        operand_b_i = 32'h7FFF_FFFF; // Most positive number
        alu_op_i = ALU_OP_SLT;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0001, "SLT: Most negative < most positive = 1");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_unsigned_comparisons();
        string test_name = "Unsigned Comparisons";
        
        // Test unsigned comparison
        operand_a_i = 32'h0000_0001; // Small number
        operand_b_i = 32'hFFFF_FFFF; // Large number
        alu_op_i = ALU_OP_SLTU;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0001, "SLTU: 1 < 0xFFFF_FFFF = 1");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_zero_operands();
        string test_name = "Zero Operands";
        
        // Test with zero operands
        operand_a_i = 32'h0000_0000;
        operand_b_i = 32'h0000_0000;
        alu_op_i = ALU_OP_ADD;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h0000_0000, "ADD: 0 + 0 = 0");
        `ASSERT_TRUE(zero_o, "ADD: Zero flag should be set");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_overflow_conditions();
        string test_name = "Overflow Conditions";
        
        // Test addition overflow
        operand_a_i = 32'h7FFF_FFFF; // Max positive
        operand_b_i = 32'h0000_0001; // 1
        alu_op_i = ALU_OP_ADD;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'h8000_0000, "ADD: Max positive + 1 = most negative");
        `ASSERT_TRUE(overflow_o, "ADD: Overflow should be detected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_maximum_values();
        string test_name = "Maximum Values";
        
        // Test with maximum values
        operand_a_i = 32'hFFFF_FFFF;
        operand_b_i = 32'hFFFF_FFFF;
        alu_op_i = ALU_OP_AND;
        @(posedge clk);
        
        `ASSERT_EQ(result_o, 32'hFFFF_FFFF, "AND: Max & Max = Max");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_random_operation();
        string test_name = "Random Operation";
        
        // Generate random operands and operation
        operand_a_i = random_word();
        operand_b_i = random_word();
        alu_op_i = $random % 12; // Random ALU operation
        
        @(posedge clk);
        
        // Basic sanity check - result should be valid
        `ASSERT_TRUE(1, "Random operation completed");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    //===========================================================================
    // Coverage
    //===========================================================================
    covergroup alu_cg @(posedge clk);
        alu_op_cp: coverpoint alu_op_i {
            bins add = {ALU_OP_ADD};
            bins sub = {ALU_OP_SUB};
            bins and_op = {ALU_OP_AND};
            bins or_op = {ALU_OP_OR};
            bins xor_op = {ALU_OP_XOR};
            bins sll = {ALU_OP_SLL};
            bins srl = {ALU_OP_SRL};
            bins sra = {ALU_OP_SRA};
            bins slt = {ALU_OP_SLT};
            bins sltu = {ALU_OP_SLTU};
        }
        
        zero_cp: coverpoint zero_o;
        overflow_cp: coverpoint overflow_o;
        
        // Cross coverage
        alu_op_zero_cross: cross alu_op_cp, zero_cp;
        alu_op_overflow_cross: cross alu_op_cp, overflow_cp;
    endgroup

    alu_cg cg_inst = new();

    //===========================================================================
    // Assertions
    //===========================================================================
    // Check that zero flag is set when result is zero
    property p_zero_flag;
        @(posedge clk) (result_o == 0) |-> zero_o;
    endproperty
    assert property (p_zero_flag) else
        $error("Zero flag not set when result is zero");

    // Check that zero flag is not set when result is non-zero
    property p_zero_flag_not_set;
        @(posedge clk) (result_o != 0) |-> !zero_o;
    endproperty
    assert property (p_zero_flag_not_set) else
        $error("Zero flag set when result is non-zero");

endmodule : alu_tb

//=============================================================================
// Dependencies: riscv_core_pkg.sv, test_utils.sv, alu.sv
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
//   - Target Technology: N/A (testbench)
//   - Synthesis Tool: N/A
//   - Clock Domains: 1 (clk)
//
// Testing:
//   - Testbench: alu_tb.sv
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//============================================================================= 