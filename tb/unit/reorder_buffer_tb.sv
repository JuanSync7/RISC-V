//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V
//
// File: reorder_buffer_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: reorder_buffer_tb
// AUTHOR: DesignAI (<author_email@company.com>)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the Reorder Buffer (ROB) module.
// PRIMARY_PURPOSE: To verify the functional correctness of the ROB, including instruction entry, completion, retirement, and exception handling.
// ROLE_IN_SYSTEM: Unit test for the ROB, ensuring its standalone functionality before integration into an out-of-order core.
// PROBLEM_SOLVED: Ensures the ROB maintains program order for retirement, handles out-of-order completion, and correctly manages exceptions and flushes.
// MODULE_TYPE: Testbench_Component
// TARGET_TECHNOLOGY_PREF: N/A (Simulation only)
// RELATED_SPECIFICATION: Out-of-Order Processor Design Principles
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

module reorder_buffer_tb;

  import riscv_ooo_types_pkg::*;

  // AI_TAG: FEATURE - Verification of instruction entry into ROB.
  // AI_TAG: FEATURE - Verification of out-of-order instruction completion.
  // AI_TAG: FEATURE - Verification of in-order instruction retirement.
  // AI_TAG: FEATURE - Handling of exceptions and ROB flush mechanism.
  // AI_TAG: FEATURE - Parameterized ROB size for flexible testing.

  // Testbench Parameters
  parameter integer CONFIG_ROB_SIZE = 16; // AI_TAG: PARAM_DESC - Number of entries in the Reorder Buffer.
                                          // AI_TAG: PARAM_USAGE - Defines the capacity of the ROB.
                                          // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2.
  parameter integer CONFIG_XLEN     = 32; // AI_TAG: PARAM_DESC - RISC-V XLEN (e.g., 32 or 64).
                                          // AI_TAG: PARAM_USAGE - Defines the width of PC and data in ROB entries.
                                          // AI_TAG: PARAM_CONSTRAINTS - Must be 32 or 64.

  // Clock and Reset Signals
  logic clk;  // AI_TAG: PORT_DESC - Testbench clock.
              // AI_TAG: PORT_CLK_DOMAIN - clk
  logic rst_n; // AI_TAG: PORT_DESC - Active-low asynchronous reset.
               // AI_TAG: PORT_CLK_DOMAIN - clk (async assert)
               // AI_TAG: PORT_TIMING - Asynchronous

  // ROB Interface Signals
  // Issue/Dispatch Interface
  logic                         issue_valid_i;     // AI_TAG: PORT_DESC - Indicates a new instruction is issued to ROB.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk
  rob_entry_t                   issue_entry_i;     // AI_TAG: PORT_DESC - New instruction entry details.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk
  logic                         issue_ready_o;     // AI_TAG: PORT_DESC - Indicates ROB is ready to accept new entry.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk
                                                   // AI_TAG: PORT_DEFAULT_STATE - 1'b1
  rob_idx_t                     issue_rob_idx_o;   // AI_TAG: PORT_DESC - ROB index assigned to the new entry.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk
                                                   // AI_TAG: PORT_DEFAULT_STATE - '0

  // Completion Interface
  logic                         complete_valid_i;  // AI_TAG: PORT_DESC - Indicates an instruction has completed execution.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk
  rob_idx_t                     complete_rob_idx_i; // AI_TAG: PORT_DESC - ROB index of the completed instruction.
                                                    // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_XLEN-1:0]       complete_result_i;  // AI_TAG: PORT_DESC - Result of the completed instruction.
                                                    // AI_TAG: PORT_CLK_DOMAIN - clk
  logic                         complete_exception_i; // AI_TAG: PORT_DESC - Indicates if completed instruction caused an exception.
                                                      // AI_TAG: PORT_CLK_DOMAIN - clk
  exception_code_t              complete_exception_code_i; // AI_TAG: PORT_DESC - Exception code for completed instruction.
                                                           // AI_TAG: PORT_CLK_DOMAIN - clk

  // Retirement Interface
  logic                         retire_valid_o;    // AI_TAG: PORT_DESC - Indicates an instruction is ready for retirement.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk
                                                   // AI_TAG: PORT_DEFAULT_STATE - 1'b0
  rob_entry_t                   retire_entry_o;    // AI_TAG: PORT_DESC - Retired instruction entry details.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk
                                                   // AI_TAG: PORT_DEFAULT_STATE - '0
  logic                         retire_ready_i;    // AI_TAG: PORT_DESC - Indicates external unit is ready to accept retired instruction.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk

  // Flush Interface
  logic                         flush_i;           // AI_TAG: PORT_DESC - Global flush signal (e.g., on branch mispredict or exception).
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk

  // Status Outputs
  logic                         rob_full_o;        // AI_TAG: PORT_DESC - Indicates ROB is full.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk
                                                   // AI_TAG: PORT_DEFAULT_STATE - 1'b0
  logic                         rob_empty_o;       // AI_TAG: PORT_DESC - Indicates ROB is empty.
                                                   // AI_TAG: PORT_CLK_DOMAIN - clk
                                                   // AI_TAG: PORT_DEFAULT_STATE - 1'b1

  // Internal Testbench Variables
  integer test_count;
  integer errors;

  // Instantiate the Reorder Buffer module
  // Assuming reorder_buffer.sv is located in rtl/execution/
  reorder_buffer #(
    .CONFIG_ROB_SIZE(CONFIG_ROB_SIZE),
    .CONFIG_XLEN(CONFIG_XLEN)
  ) u_rob ( // AI_TAG: IF_TYPE - Reorder Buffer Instance
            // AI_TAG: IF_DESC - Instance of the Reorder Buffer under test.
            // AI_TAG: IF_CLOCKING - clk
            // AI_TAG: IF_RESET - rst_n
    .clk_i                   (clk),
    .rst_ni                  (rst_n),
    .issue_valid_i           (issue_valid_i),
    .issue_entry_i           (issue_entry_i),
    .issue_ready_o           (issue_ready_o),
    .issue_rob_idx_o         (issue_rob_idx_o),
    .complete_valid_i        (complete_valid_i),
    .complete_rob_idx_i      (complete_rob_idx_i),
    .complete_result_i       (complete_result_i),
    .complete_exception_i    (complete_exception_i),
    .complete_exception_code_i(complete_exception_code_i),
    .retire_valid_o          (retire_valid_o),
    .retire_entry_o          (retire_entry_o),
    .retire_ready_i          (retire_ready_i),
    .flush_i                 (flush_i),
    .rob_full_o              (rob_full_o),
    .rob_empty_o             (rob_empty_o)
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

    // AI_TAG: SCENARIO_START - Basic Instruction Flow (Issue, Complete, Retire)
    // Issue several instructions, complete them in order, and retire them.
    // AI_TAG: SCENARIO_END

    // Test 1: Issue, Complete, Retire in order
    test_count++;
    retire_ready_i = 1;

    // Issue Inst 0
    issue_valid_i = 1; issue_entry_i.pc = 32'h1000; issue_entry_i.inst = 32'h00000013; issue_entry_i.has_dest = 1; issue_entry_i.dest_reg = 5'd1; issue_entry_i.is_branch = 0; issue_entry_i.is_load = 0; issue_entry_i.is_store = 0;
    #10; // Wait for issue
    issue_valid_i = 0;

    // Issue Inst 1
    issue_valid_i = 1; issue_entry_i.pc = 32'h1004; issue_entry_i.inst = 32'h00000093; issue_entry_i.has_dest = 1; issue_entry_i.dest_reg = 5'd2; issue_entry_i.is_branch = 0; issue_entry_i.is_load = 0; issue_entry_i.is_store = 0;
    #10; // Wait for issue
    issue_valid_i = 0;

    // Complete Inst 0
    complete_valid_i = 1; complete_rob_idx_i = 0; complete_result_i = 32'd10; complete_exception_i = 0;
    #10; // Wait for completion
    complete_valid_i = 0;

    // Retire Inst 0
    #10; // Wait for retirement
    if (!retire_valid_o || retire_entry_o.pc !== 32'h1000) begin
      $error("Test %0d (In-order Retire): Inst 0 failed to retire correctly.", test_count);
      errors++;
    end else begin
      $info("Test %0d (In-order Retire): Inst 0 retired.", test_count);
    end

    // Complete Inst 1
    complete_valid_i = 1; complete_rob_idx_i = 1; complete_result_i = 32'd20; complete_exception_i = 0;
    #10; // Wait for completion
    complete_valid_i = 0;

    // Retire Inst 1
    #10; // Wait for retirement
    if (!retire_valid_o || retire_entry_o.pc !== 32'h1004) begin
      $error("Test %0d (In-order Retire): Inst 1 failed to retire correctly.", test_count);
      errors++;
    end else begin
      $info("Test %0d (In-order Retire): Inst 1 retired.", test_count);
    end

    // AI_TAG: SCENARIO_START - Out-of-Order Completion
    // Issue instructions, complete them out of order, and verify in-order retirement.
    // AI_TAG: SCENARIO_END

    // Test 2: Out-of-order completion, in-order retirement
    test_count++;
    retire_ready_i = 1;

    // Issue Inst 2, 3, 4
    issue_valid_i = 1; issue_entry_i.pc = 32'h2000; issue_entry_i.inst = 32'h00000013; issue_entry_i.has_dest = 1; issue_entry_i.dest_reg = 5'd3; #10; // ROB idx 2
    issue_entry_i.pc = 32'h2004; issue_entry_i.inst = 32'h00000093; issue_entry_i.has_dest = 1; issue_entry_i.dest_reg = 5'd4; #10; // ROB idx 3
    issue_entry_i.pc = 32'h2008; issue_entry_i.inst = 32'h00000113; issue_entry_i.has_dest = 1; issue_entry_i.dest_reg = 5'd5; #10; // ROB idx 4
    issue_valid_i = 0;

    // Complete Inst 4 (out of order)
    complete_valid_i = 1; complete_rob_idx_i = 4; complete_result_i = 32'd40; complete_exception_i = 0;
    #10; complete_valid_i = 0;

    // Complete Inst 2
    complete_valid_i = 1; complete_rob_idx_i = 2; complete_result_i = 32'd20; complete_exception_i = 0;
    #10; complete_valid_i = 0;

    // Inst 2 should retire now
    #10;
    if (!retire_valid_o || retire_entry_o.pc !== 32'h2000) begin
      $error("Test %0d (OOO Complete): Inst 2 failed to retire correctly.", test_count);
      errors++;
    end else begin
      $info("Test %0d (OOO Complete): Inst 2 retired.", test_count);
    end

    // Complete Inst 3
    complete_valid_i = 1; complete_rob_idx_i = 3; complete_result_i = 32'd30; complete_exception_i = 0;
    #10; complete_valid_i = 0;

    // Inst 3 should retire now
    #10;
    if (!retire_valid_o || retire_entry_o.pc !== 32'h2004) begin
      $error("Test %0d (OOO Complete): Inst 3 failed to retire correctly.", test_count);
      errors++;
    end else begin
      $info("Test %0d (OOO Complete): Inst 3 retired.", test_count);
    end

    // Inst 4 should retire now
    #10;
    if (!retire_valid_o || retire_entry_o.pc !== 32'h2008) begin
      $error("Test %0d (OOO Complete): Inst 4 failed to retire correctly.", test_count);
      errors++;
    end else begin
      $info("Test %0d (OOO Complete): Inst 4 retired.", test_count);
    end

    // AI_TAG: SCENARIO_START - Exception Handling and Flush
    // Issue instructions, complete one with an exception, and verify ROB flush.
    // AI_TAG: SCENARIO_END

    // Test 3: Exception and Flush
    test_count++;
    retire_ready_i = 1;

    // Issue Inst 5, 6, 7
    issue_valid_i = 1; issue_entry_i.pc = 32'h3000; issue_entry_i.inst = 32'h00000013; issue_entry_i.has_dest = 1; issue_entry_i.dest_reg = 5'd6; #10; // ROB idx 5
    issue_entry_i.pc = 32'h3004; issue_entry_i.inst = 32'h00000093; issue_entry_i.has_dest = 1; issue_entry_i.dest_reg = 5'd7; #10; // ROB idx 6
    issue_entry_i.pc = 32'h3008; issue_entry_i.inst = 32'h00000113; issue_entry_i.has_dest = 1; issue_entry_i.dest_reg = 5'd8; #10; // ROB idx 7
    issue_valid_i = 0;

    // Complete Inst 6 (out of order) with exception
    complete_valid_i = 1; complete_rob_idx_i = 6; complete_result_i = '0; complete_exception_i = 1; complete_exception_code_i = ILLEGAL_INSTRUCTION;
    #10; complete_valid_i = 0;

    // ROB should flush, no retirement until flush is complete
    #10;
    if (retire_valid_o) begin
      $error("Test %0d (Exception Flush): Unexpected retirement during flush.", test_count);
      errors++;
    end else begin
      $info("Test %0d (Exception Flush): No retirement during flush (expected).", test_count);
    end

    // Verify ROB is empty after flush
    #10;
    if (!rob_empty_o) begin
      $error("Test %0d (Exception Flush): ROB not empty after flush.", test_count);
      errors++;
    end else begin
      $info("Test %0d (Exception Flush): ROB empty after flush (expected).", test_count);
    end

    // Final Report
    if (errors == 0) begin
      $display("======================================");
      $display("All %0d Reorder Buffer tests passed successfully!", test_count);
      $display("======================================");
    end else begin
      $error("======================================");
      $error("%0d out of %0d Reorder Buffer tests failed.", errors, test_count);
      $error("======================================");
    end

    $finish;
  end

endmodule : reorder_buffer_tb
//=============================================================================
// Dependencies: reorder_buffer.sv, riscv_ooo_types_pkg.sv
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
//   - Testbench: reorder_buffer_tb.sv
//   - Test Vectors: 3 directed test cases
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | DesignAI           | Initial creation of Reorder Buffer testbench.
//=============================================================================
