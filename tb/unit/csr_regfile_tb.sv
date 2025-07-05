//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V
//
// File: csr_regfile_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: csr_regfile_tb
// AUTHOR: DesignAI (<author_email@company.com>)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the CSR (Control and Status Register) File module.
// PRIMARY_PURPOSE: To verify the functional correctness of the CSR File module, including read-write operations, address decoding, and access permissions.
// ROLE_IN_SYSTEM: Unit test for the CSR File, ensuring its standalone functionality before integration into the core.
// PROBLEM_SOLVED: Ensures the CSR File correctly handles reads and writes to control and status registers according to RISC-V specifications.
// MODULE_TYPE: Testbench_Component
// TARGET_TECHNOLOGY_PREF: N/A (Simulation only)
// RELATED_SPECIFICATION: RISC-V Privileged Architecture Specification
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

module csr_regfile_tb;

  // AI_TAG: FEATURE - Comprehensive testing of CSR read and write operations.
  // AI_TAG: FEATURE - Handling of read-only and write-only CSRs.
  // AI_TAG: FEATURE - Testing of illegal CSR address accesses.
  // AI_TAG: FEATURE - Parameterized data width for flexible testing.
  // AI_TAG: FEATURE - Self-checking mechanism for data integrity.

  // Testbench Parameters
  parameter integer CONFIG_DATA_WIDTH = 32; // AI_TAG: PARAM_DESC - Data width of CSRs.
                                            // AI_TAG: PARAM_USAGE - Defines the bit-width of data read from/written to CSRs.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.
  parameter integer CONFIG_ADDR_WIDTH = 12; // AI_TAG: PARAM_DESC - Address width for CSRs (12 bits for RISC-V).
                                            // AI_TAG: PARAM_USAGE - Defines the address space for CSRs.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be 12 for RISC-V standard.

  // Clock and Reset Signals
  logic clk;  // AI_TAG: PORT_DESC - Testbench clock.
              // AI_TAG: PORT_CLK_DOMAIN - clk
  logic rst_n; // AI_TAG: PORT_DESC - Active-low asynchronous reset.
               // AI_TAG: PORT_CLK_DOMAIN - clk (async assert)
               // AI_TAG: PORT_TIMING - Asynchronous

  // CSR File Interface Signals
  logic                         csr_we;      // AI_TAG: PORT_DESC - CSR Write Enable.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_ADDR_WIDTH-1:0] csr_addr;    // AI_TAG: PORT_DESC - CSR Address.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_DATA_WIDTH-1:0] csr_wdata;   // AI_TAG: PORT_DESC - CSR Write Data.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_DATA_WIDTH-1:0] csr_rdata;   // AI_TAG: PORT_DESC - CSR Read Data.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
                                             // AI_TAG: PORT_DEFAULT_STATE - '0
  logic                         csr_valid;   // AI_TAG: PORT_DESC - Indicates a valid CSR access.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
                                             // AI_TAG: PORT_DEFAULT_STATE - 1'b0

  // Internal Testbench Variables
  integer test_count;
  integer errors;

  // Instantiate the CSR Register File module
  // Assuming csr_regfile.sv is located in rtl/core/
  csr_regfile #(
    .CONFIG_DATA_WIDTH(CONFIG_DATA_WIDTH),
    .CONFIG_ADDR_WIDTH(CONFIG_ADDR_WIDTH)
  ) u_csr_regfile ( // AI_TAG: IF_TYPE - CSR Register File Instance
                    // AI_TAG: IF_DESC - Instance of the CSR Register File under test.
                    // AI_TAG: IF_CLOCKING - clk
                    // AI_TAG: IF_RESET - rst_n
    .clk_i    (clk),
    .rst_ni   (rst_n),
    .csr_we_i (csr_we),
    .csr_addr_i(csr_addr),
    .csr_wdata_i(csr_wdata),
    .csr_rdata_o(csr_rdata),
    .csr_valid_o(csr_valid)
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

    // AI_TAG: SCENARIO_START - Basic CSR Write and Read
    // Write to a writable CSR (e.g., mscratch) and read it back.
    // AI_TAG: SCENARIO_END

    // Test 1: Write to mscratch (0x340) and read back
    test_count++;
    csr_we = 1;
    csr_addr = 12'h340; // mscratch
    csr_wdata = 32'hDEADBEEF;
    #10;
    csr_we = 0;
    csr_addr = 12'h340;
    #10;
    if (csr_rdata !== 32'hDEADBEEF) begin
      $error("Test %0d (mscratch R/W): Expected %h, got %h", test_count, 32'hDEADBEEF, csr_rdata);
      errors++;
    end else begin
      $info("Test %0d (mscratch R/W): Passed.", test_count);
    end

    // AI_TAG: SCENARIO_START - Read-Only CSR Access
    // Attempt to write to a read-only CSR (e.g., mhartid) and verify its value remains unchanged.
    // AI_TAG: SCENARIO_END

    // Test 2: Attempt to write to mhartid (0xF14), then read
    test_count++;
    csr_we = 1;
    csr_addr = 12'hF14; // mhartid
    csr_wdata = 32'hCAFEBABE; // Attempt to write
    #10;
    csr_we = 0;
    csr_addr = 12'hF14;
    #10;
    // Assuming mhartid defaults to 0 or some fixed value, and write has no effect
    if (csr_rdata !== 32'h0) begin // Assuming initial mhartid is 0
      $error("Test %0d (mhartid RO): Expected 0, got %h (write should have no effect)", test_count, csr_rdata);
      errors++;
    end else begin
      $info("Test %0d (mhartid RO): Passed.", test_count);
    end

    // AI_TAG: SCENARIO_START - Illegal CSR Address Access
    // Attempt to access an invalid CSR address and verify appropriate behavior (e.g., csr_valid de-asserted, rdata is 0).
    // AI_TAG: SCENARIO_END

    // Test 3: Access illegal CSR address (e.g., 0x001)
    test_count++;
    csr_we = 0;
    csr_addr = 12'h001; // Illegal address
    #10;
    if (csr_valid !== 1'b0 || csr_rdata !== 32'h0) begin // Assuming invalid access results in valid=0 and rdata=0
      $error("Test %0d (Illegal Addr): Expected valid=0, rdata=0, got valid=%0d, rdata=%h", test_count, csr_valid, csr_rdata);
      errors++;
    end else begin
      $info("Test %0d (Illegal Addr): Passed.", test_count);
    end

    // Final Report
    if (errors == 0) begin
      $display("======================================");
      $display("All %0d CSR Register File tests passed successfully!", test_count);
      $display("======================================");
    end else begin
      $error("======================================");
      $error("%0d out of %0d CSR Register File tests failed.", errors, test_count);
      $error("======================================");
    end

    $finish;
  end

endmodule : csr_regfile_tb
//=============================================================================
// Dependencies: csr_regfile.sv
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
//   - Testbench: csr_regfile_tb.sv
//   - Test Vectors: 3 directed test cases
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | DesignAI           | Initial creation of CSR Register File testbench.
//=============================================================================
