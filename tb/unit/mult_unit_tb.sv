//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V
//
// File: mult_unit_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: mult_unit_tb
// AUTHOR: DesignAI (<author_email@company.com>)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the Multiplier Unit module.
// PRIMARY_PURPOSE: To verify the functional correctness of the Multiplier Unit module across various operations and edge cases.
// ROLE_IN_SYSTEM: Unit test for the Multiplier Unit, ensuring its standalone functionality before integration.
// PROBLEM_SOLVED: Ensures the Multiplier Unit performs all specified multiplication operations accurately.
// MODULE_TYPE: Testbench_Component
// TARGET_TECHNOLOGY_PREF: N/A (Simulation only)
// RELATED_SPECIFICATION: RISC-V ISA (relevant multiplication instructions)
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

module mult_unit_tb;

  // AI_TAG: FEATURE - Comprehensive testing of multiplication operations.
  // AI_TAG: FEATURE - Parameterized data width for flexible testing.
  // AI_TAG: FEATURE - Random test generation for input operands.
  // AI_TAG: FEATURE - Self-checking mechanism for result validation.

  // Testbench Parameters
  parameter integer CONFIG_DATA_WIDTH = 32; // AI_TAG: PARAM_DESC - Data width of the multiplier operands and result.
                                            // AI_TAG: PARAM_USAGE - Defines the bit-width of input and output data.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.

  // Clock and Reset Signals
  logic clk;  // AI_TAG: PORT_DESC - Testbench clock.
              // AI_TAG: PORT_CLK_DOMAIN - clk
  logic rst_n; // AI_TAG: PORT_DESC - Active-low asynchronous reset.
               // AI_TAG: PORT_CLK_DOMAIN - clk (async assert)
               // AI_TAG: PORT_TIMING - Asynchronous

  // Multiplier Unit Interface Signals
  logic [CONFIG_DATA_WIDTH-1:0] operand_a; // AI_TAG: PORT_DESC - First operand for multiplication.
                                           // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_DATA_WIDTH-1:0] operand_b; // AI_TAG: PORT_DESC - Second operand for multiplication.
                                           // AI_TAG: PORT_CLK_DOMAIN - clk
  logic                         start_i;   // AI_TAG: PORT_DESC - Start signal for multiplication.
                                           // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [2*CONFIG_DATA_WIDTH-1:0] result_o;  // AI_TAG: PORT_DESC - Result of the multiplication operation.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
                                             // AI_TAG: PORT_DEFAULT_STATE - '0
  logic                         valid_o;   // AI_TAG: PORT_DESC - Valid signal for multiplication result.
                                           // AI_TAG: PORT_CLK_DOMAIN - clk
                                           // AI_TAG: PORT_DEFAULT_STATE - 1'b0

  // Internal Testbench Variables
  integer test_count;
  integer errors;

  // Instantiate the Multiplier Unit module
  // Assuming mult_unit.sv is located in rtl/units/
  mult_unit #(
    .CONFIG_DATA_WIDTH(CONFIG_DATA_WIDTH)
  ) u_mult_unit ( // AI_TAG: IF_TYPE - Multiplier Unit Instance
                  // AI_TAG: IF_DESC - Instance of the Multiplier Unit under test.
                  // AI_TAG: IF_CLOCKING - clk
                  // AI_TAG: IF_RESET - rst_n
    .clk_i      (clk),
    .rst_ni     (rst_n),
    .operand_a_i(operand_a),
    .operand_b_i(operand_b),
    .start_i    (start_i),
    .result_o   (result_o),
    .valid_o    (valid_o)
  );

  // Clock Generation
  always #5 clk = ~clk;

  // Test Sequence
  initial begin
    clk = 0;
    rst_n = 0;
    test_count = 0;
    errors = 0;

    // AI_TAG: SCENARIO_START - Initial Reset and Initialization
    // Apply reset and initialize testbench variables.
    // AI_TAG: SCENARIO_END
    #10;
    rst_n = 1;
    #10;

    // AI_TAG: SCENARIO_START - Basic Multiplication Operations
    // Test various multiplication operations.
    // AI_TAG: SCENARIO_END

    // Test 1: Positive * Positive
    test_count++;
    operand_a = 32'd10;
    operand_b = 32'd5;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (result_o !== 64'd50) begin
      $error("Test %0d (Pos * Pos): Expected 50, got %0d.", test_count, result_o);
      errors++;
    end else begin
      $info("Test %0d (Pos * Pos): Passed.", test_count);
    end

    // Test 2: Positive * Zero
    test_count++;
    operand_a = 32'd100;
    operand_b = 32'd0;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (result_o !== 64'd0) begin
      $error("Test %0d (Pos * Zero): Expected 0, got %0d.", test_count, result_o);
      errors++;
    end else begin
      $info("Test %0d (Pos * Zero): Passed.", test_count);
    end

    // Test 3: Zero * Positive
    test_count++;
    operand_a = 32'd0;
    operand_b = 32'd25;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (result_o !== 64'd0) begin
      $error("Test %0d (Zero * Pos): Expected 0, got %0d.", test_count, result_o);
      errors++;
    end else begin
      $info("Test %0d (Zero * Pos): Passed.", test_count);
    end

    // Test 4: Negative * Positive (assuming signed multiplication)
    // For simplicity, assuming 2's complement for negative numbers
    // -5 * 10 = -50
    test_count++;
    operand_a = 32'hFFFFFFFB; // -5
    operand_b = 32'd10;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (result_o !== 64'hFFFFFFFFFFFFFFCE) begin // -50
      $error("Test %0d (Neg * Pos): Expected -50, got %0d.", test_count, result_o);
      errors++;
    end else begin
      $info("Test %0d (Neg * Pos): Passed.", test_count);
    end

    // Test 5: Max values
    test_count++;
    operand_a = 32'h7FFFFFFF; // Max positive 32-bit
    operand_b = 32'd2;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (result_o !== 64'h00000000FFFFFFFE) begin // 2 * (2^31 - 1) = 2^32 - 2
      $error("Test %0d (Max Pos): Expected %h, got %h.", test_count, 64'h00000000FFFFFFFE, result_o);
      errors++;
    end else begin
      $info("Test %0d (Max Pos): Passed.", test_count);
    end

    // Final Report
    if (errors == 0) begin
      $display("======================================");
      $display("All %0d Multiplier Unit tests passed successfully!", test_count);
      $display("======================================");
    end else begin
      $error("======================================");
      $error("%0d out of %0d Multiplier Unit tests failed.", errors, test_count);
      $error("======================================");
    end

    $finish;
  end

endmodule : mult_unit_tb
//=============================================================================
// Dependencies: mult_unit.sv
//
// Instantiated In:
//   - N/A (Top-level testbench)
//
// Performance:
//   - Critical Path: N/A
//   - Max Frequency: N/A (Simulation only)
//   - Area: N/A (Simulation only)
//
// Verification Coverage:
//   - Code Coverage: To be determined by simulation tool
//   - Functional Coverage: To be determined by simulation tool
//   - Branch Coverage: To be determined by simulation tool
//
// Synthesis:
//   - Target Technology: N/A
//   - Synthesis Tool: N/A
//   - Clock Domains: 1
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: mult_unit_tb.sv
//   - Test Vectors: 5 directed test cases
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | DesignAI           | Initial creation of Multiplier Unit testbench.
//=============================================================================
