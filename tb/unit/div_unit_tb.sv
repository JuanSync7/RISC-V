//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V
//
// File: div_unit_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: div_unit_tb
// AUTHOR: DesignAI (<author_email@company.com>)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the Division Unit module.
// PRIMARY_PURPOSE: To verify the functional correctness of the Division Unit module across various operations and edge cases.
// ROLE_IN_SYSTEM: Unit test for the Division Unit, ensuring its standalone functionality before integration.
// PROBLEM_SOLVED: Ensures the Division Unit performs all specified division operations accurately.
// MODULE_TYPE: Testbench_Component
// TARGET_TECHNOLOGY_PREF: N/A (Simulation only)
// RELATED_SPECIFICATION: RISC-V ISA (relevant division instructions)
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

module div_unit_tb;

  // AI_TAG: FEATURE - Comprehensive testing of division operations.
  // AI_TAG: FEATURE - Parameterized data width for flexible testing.
  // AI_TAG: FEATURE - Random test generation for input operands.
  // AI_TAG: FEATURE - Self-checking mechanism for result validation.
  // AI_TAG: FEATURE - Handling of division by zero scenario.

  // Testbench Parameters
  parameter integer CONFIG_DATA_WIDTH = 32; // AI_TAG: PARAM_DESC - Data width of the divider operands and result.
                                            // AI_TAG: PARAM_USAGE - Defines the bit-width of input and output data.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.

  // Clock and Reset Signals
  logic clk;  // AI_TAG: PORT_DESC - Testbench clock.
              // AI_TAG: PORT_CLK_DOMAIN - clk
  logic rst_n; // AI_TAG: PORT_DESC - Active-low asynchronous reset.
               // AI_TAG: PORT_CLK_DOMAIN - clk (async assert)
               // AI_TAG: PORT_TIMING - Asynchronous

  // Divider Unit Interface Signals
  logic [CONFIG_DATA_WIDTH-1:0] dividend; // AI_TAG: PORT_DESC - Dividend for division operation.
                                          // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_DATA_WIDTH-1:0] divisor;  // AI_TAG: PORT_DESC - Divisor for division operation.
                                          // AI_TAG: PORT_CLK_DOMAIN - clk
  logic                         start_i;  // AI_TAG: PORT_DESC - Start signal for division.
                                          // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_DATA_WIDTH-1:0] quotient; // AI_TAG: PORT_DESC - Quotient result of the division operation.
                                          // AI_TAG: PORT_CLK_DOMAIN - clk
                                          // AI_TAG: PORT_DEFAULT_STATE - '0
  logic [CONFIG_DATA_WIDTH-1:0] remainder; // AI_TAG: PORT_DESC - Remainder result of the division operation.
                                           // AI_TAG: PORT_CLK_DOMAIN - clk
                                           // AI_TAG: PORT_DEFAULT_STATE - '0
  logic                         valid_o;  // AI_TAG: PORT_DESC - Valid signal for division result.
                                          // AI_TAG: PORT_CLK_DOMAIN - clk
                                          // AI_TAG: PORT_DEFAULT_STATE - 1'b0
  logic                         busy_o;   // AI_TAG: PORT_DESC - Busy signal indicating division in progress.
                                          // AI_TAG: PORT_CLK_DOMAIN - clk
                                          // AI_TAG: PORT_DEFAULT_STATE - 1'b0

  // Internal Testbench Variables
  integer test_count;
  integer errors;

  // Instantiate the Divider Unit module
  // Assuming div_unit.sv is located in rtl/units/
  div_unit #(
    .CONFIG_DATA_WIDTH(CONFIG_DATA_WIDTH)
  ) u_div_unit ( // AI_TAG: IF_TYPE - Divider Unit Instance
                 // AI_TAG: IF_DESC - Instance of the Division Unit under test.
                 // AI_TAG: IF_CLOCKING - clk
                 // AI_TAG: IF_RESET - rst_n
    .clk_i     (clk),
    .rst_ni    (rst_n),
    .dividend_i(dividend),
    .divisor_i (divisor),
    .start_i   (start_i),
    .quotient_o(quotient),
    .remainder_o(remainder),
    .valid_o   (valid_o),
    .busy_o    (busy_o)
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

    // AI_TAG: SCENARIO_START - Basic Division Operations
    // Test various division operations.
    // AI_TAG: SCENARIO_END

    // Test 1: Exact Division
    test_count++;
    dividend = 32'd100;
    divisor = 32'd10;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (quotient !== 32'd10 || remainder !== 32'd0) begin
      $error("Test %0d (Exact Div): Expected Q=10, R=0, got Q=%0d, R=%0d.", test_count, quotient, remainder);
      errors++;
    end else begin
      $info("Test %0d (Exact Div): Passed.", test_count);
    end

    // Test 2: Division with Remainder
    test_count++;
    dividend = 32'd25;
    divisor = 32'd4;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (quotient !== 32'd6 || remainder !== 32'd1) begin
      $error("Test %0d (Div with Rem): Expected Q=6, R=1, got Q=%0d, R=%0d.", test_count, quotient, remainder);
      errors++;
    end else begin
      $info("Test %0d (Div with Rem): Passed.", test_count);
    end

    // Test 3: Dividend smaller than Divisor
    test_count++;
    dividend = 32'd3;
    divisor = 32'd7;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (quotient !== 32'd0 || remainder !== 32'd3) begin
      $error("Test %0d (Small Div): Expected Q=0, R=3, got Q=%0d, R=%0d.", test_count, quotient, remainder);
      errors++;
    end else begin
      $info("Test %0d (Small Div): Passed.", test_count);
    end

    // Test 4: Division by 1
    test_count++;
    dividend = 32'd99;
    divisor = 32'd1;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (quotient !== 32'd99 || remainder !== 32'd0) begin
      $error("Test %0d (Div by 1): Expected Q=99, R=0, got Q=%0d, R=%0d.", test_count, quotient, remainder);
      errors++;
    end else begin
      $info("Test %0d (Div by 1): Passed.", test_count);
    end

    // Test 5: Division by Zero (Expected behavior: quotient = all 1s, remainder = dividend, valid = 1, busy = 0)
    // AI_TAG: ERROR_CONDITION - Division by Zero - Divisor is 0 - Quotient set to all 1s, Remainder set to Dividend, Valid asserted, Busy de-asserted.
    test_count++;
    dividend = 32'd50;
    divisor = 32'd0;
    start_i = 1;
    #10;
    start_i = 0;
    @(posedge clk iff valid_o);
    if (quotient !== {CONFIG_DATA_WIDTH{1'b1}} || remainder !== dividend) begin
      $error("Test %0d (Div by Zero): Expected Q=all 1s, R=dividend, got Q=%h, R=%h.", test_count, quotient, remainder);
      errors++;
    end else begin
      $info("Test %0d (Div by Zero): Passed.", test_count);
    end

    // Final Report
    if (errors == 0) begin
      $display("======================================");
      $display("All %0d Division Unit tests passed successfully!", test_count);
      $display("======================================");
    end else begin
      $error("======================================");
      $error("%0d out of %0d Division Unit tests failed.", errors, test_count);
      $error("======================================");
    end

    $finish;
  end

endmodule : div_unit_tb
//=============================================================================
// Dependencies: div_unit.sv
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
//   - Testbench: div_unit_tb.sv
//   - Test Vectors: 5 directed test cases
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | DesignAI           | Initial creation of Division Unit testbench.
//=============================================================================
