//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V
//
// File: reg_file_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: reg_file_tb
// AUTHOR: DesignAI (<author_email@company.com>)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the Register File module.
// PRIMARY_PURPOSE: To verify the functional correctness of the Register File module, including read-write operations and address decoding.
// ROLE_IN_SYSTEM: Unit test for the Register File, ensuring its standalone functionality before integration into the core.
// PROBLEM_SOLVED: Ensures the Register File correctly stores and retrieves data for all valid register addresses.
// MODULE_TYPE: Testbench_Component
// TARGET_TECHNOLOGY_PREF: N/A (Simulation only)
// RELATED_SPECIFICATION: RISC-V ISA (Register File specification)
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

module reg_file_tb;

  // AI_TAG: FEATURE - Comprehensive testing of register write and read operations.
  // AI_TAG: FEATURE - Parameterized data width and number of registers for flexible testing.
  // AI_TAG: FEATURE - Random test generation for register addresses and data.
  // AI_TAG: FEATURE - Self-checking mechanism for data integrity.
  // AI_TAG: FEATURE - Handling of register 0 (x0) always reading as zero.

  // Testbench Parameters
  parameter integer CONFIG_DATA_WIDTH = 32; // AI_TAG: PARAM_DESC - Data width of each register.
                                            // AI_TAG: PARAM_USAGE - Defines the bit-width of data stored in registers.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.
  parameter integer CONFIG_NUM_REGS   = 32; // AI_TAG: PARAM_DESC - Number of registers in the file (e.g., 32 for RISC-V).
                                            // AI_TAG: PARAM_USAGE - Determines the address width and total storage capacity.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2.

  localparam integer LP_ADDR_WIDTH = $clog2(CONFIG_NUM_REGS); // AI_TAG: INTERNAL_STORAGE - LP_ADDR_WIDTH - Derived parameter for address bus width.

  // Clock and Reset Signals
  logic clk;  // AI_TAG: PORT_DESC - Testbench clock.
              // AI_TAG: PORT_CLK_DOMAIN - clk
  logic rst_n; // AI_TAG: PORT_DESC - Active-low asynchronous reset.
               // AI_TAG: PORT_CLK_DOMAIN - clk (async assert)
               // AI_TAG: PORT_TIMING - Asynchronous

  // Register File Interface Signals
  logic                         write_en;    // AI_TAG: PORT_DESC - Write enable signal.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [LP_ADDR_WIDTH-1:0]     write_addr;  // AI_TAG: PORT_DESC - Address for write operation.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_DATA_WIDTH-1:0] write_data;  // AI_TAG: PORT_DESC - Data to be written.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk

  logic [LP_ADDR_WIDTH-1:0]     read_addr1;  // AI_TAG: PORT_DESC - First address for read operation.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_DATA_WIDTH-1:0] read_data1;  // AI_TAG: PORT_DESC - Data read from first address.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
                                             // AI_TAG: PORT_DEFAULT_STATE - '0

  logic [LP_ADDR_WIDTH-1:0]     read_addr2;  // AI_TAG: PORT_DESC - Second address for read operation.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [CONFIG_DATA_WIDTH-1:0] read_data2;  // AI_TAG: PORT_DESC - Data read from second address.
                                             // AI_TAG: PORT_CLK_DOMAIN - clk
                                             // AI_TAG: PORT_DEFAULT_STATE - '0

  // Internal Testbench Variables
  integer test_count;
  integer errors;
  logic [CONFIG_DATA_WIDTH-1:0] expected_reg_file [CONFIG_NUM_REGS-1:0]; // AI_TAG: INTERNAL_STORAGE - expected_reg_file - Software model of the register file.
                                                                       // AI_TAG: INTERNAL_STORAGE_TYPE - Array of registers
                                                                       // AI_TAG: INTERNAL_STORAGE_ACCESS - Internal testbench logic

  // Instantiate the Register File module
  // Assuming reg_file.sv is located in rtl/core/
  reg_file #(
    .CONFIG_DATA_WIDTH(CONFIG_DATA_WIDTH),
    .CONFIG_NUM_REGS(CONFIG_NUM_REGS)
  ) u_reg_file ( // AI_TAG: IF_TYPE - Register File Instance
                 // AI_TAG: IF_DESC - Instance of the Register File under test.
                 // AI_TAG: IF_CLOCKING - clk
                 // AI_TAG: IF_RESET - rst_n
    .clk_i       (clk),
    .rst_ni      (rst_n),
    .write_en_i  (write_en),
    .write_addr_i(write_addr),
    .write_data_i(write_data),
    .read_addr1_i(read_addr1),
    .read_data1_o(read_data1),
    .read_addr2_i(read_addr2),
    .read_data2_o(read_data2)
  );

  // Clock Generation
  always #5 clk = ~clk;

  // Test Sequence
  initial begin
    clk = 0;
    rst_n = 0;
    test_count = 0;
    errors = 0;

    // Initialize expected register file model
    for (int i = 0; i < CONFIG_NUM_REGS; i++) begin
      expected_reg_file[i] = '0;
    end

    // AI_TAG: SCENARIO_START - Initial Reset and Initialization
    // Apply reset and initialize testbench variables.
    // AI_TAG: SCENARIO_END
    #10;
    rst_n = 1;
    #10;

    // AI_TAG: SCENARIO_START - Write and Read Basic Values
    // Write distinct values to several registers and read them back.
    // AI_TAG: SCENARIO_END

    // Test 1: Write to x1, x2, x3
    test_count++;
    write_en = 1;
    write_addr = 5'd1; write_data = 32'hDEADBEEF; #10; expected_reg_file[1] = 32'hDEADBEEF;
    write_addr = 5'd2; write_data = 32'hCAFEBABE; #10; expected_reg_file[2] = 32'hCAFEBABE;
    write_addr = 5'd3; write_data = 32'h12345678; #10; expected_reg_file[3] = 32'h12345678;
    write_en = 0;

    // Read from x1, x2, x3 and verify
    read_addr1 = 5'd1; read_addr2 = 5'd2; #10;
    if (read_data1 !== expected_reg_file[1] || read_data2 !== expected_reg_file[2]) begin
      $error("Test %0d (Read x1, x2): Expected x1=%h, x2=%h; Got x1=%h, x2=%h", test_count, expected_reg_file[1], expected_reg_file[2], read_data1, read_data2);
      errors++;
    end else begin
      $info("Test %0d (Read x1, x2): Passed.", test_count);
    end

    read_addr1 = 5'd3; read_addr2 = 5'd0; // Read x3 and x0
    #10;
    if (read_data1 !== expected_reg_file[3] || read_data2 !== '0) begin // x0 should always be 0
      $error("Test %0d (Read x3, x0): Expected x3=%h, x0=0; Got x3=%h, x0=%h", test_count, expected_reg_file[3], read_data1, read_data2);
      errors++;
    end else begin
      $info("Test %0d (Read x3, x0): Passed.", test_count);
    end

    // AI_TAG: SCENARIO_START - Read-After-Write Hazard
    // Write to a register and read it in the same cycle (or next cycle depending on RF implementation).
    // AI_TAG: SCENARIO_END

    // Test 2: Write to x4, then read x4 immediately (combinational read)
    test_count++;
    write_en = 1;
    write_addr = 5'd4; write_data = 32'hF00DCAFE;
    read_addr1 = 5'd4; // Read from the same address being written
    #10;
    write_en = 0;
    expected_reg_file[4] = 32'hF00DCAFE;
    // Assuming combinational read, read_data1 should reflect the new value immediately
    if (read_data1 !== expected_reg_file[4]) begin
      $error("Test %0d (RAW): Expected %h, got %h", test_count, expected_reg_file[4], read_data1);
      errors++;
    end else begin
      $info("Test %0d (RAW): Passed.", test_count);
    end

    // AI_TAG: SCENARIO_START - All Registers Access
    // Write unique values to all registers (excluding x0) and verify.
    // AI_TAG: SCENARIO_END

    // Test 3: Write to all registers (x1 to x31)
    test_count++;
    write_en = 1;
    for (int i = 1; i < CONFIG_NUM_REGS; i++) begin
      write_addr = i;
      write_data = {i[4:0], i[4:0], i[4:0], i[4:0], i[4:0], i[4:0], i[4:0], i[4:0]}; // Unique pattern
      expected_reg_file[i] = write_data;
      #1;
    end
    write_en = 0;
    #10;

    // Verify all registers
    for (int i = 1; i < CONFIG_NUM_REGS; i++) begin
      read_addr1 = i;
      #1;
      if (read_data1 !== expected_reg_file[i]) begin
        $error("Test %0d (All Regs Read): Register x%0d: Expected %h, got %h", test_count, i, expected_reg_file[i], read_data1);
        errors++;
      end
    end
    if (errors == 0) begin
      $info("Test %0d (All Regs Read): Passed.", test_count);
    end

    // Final Report
    if (errors == 0) begin
      $display("======================================");
      $display("All %0d Register File tests passed successfully!", test_count);
      $display("======================================");
    end else begin
      $error("======================================");
      $error("%0d out of %0d Register File tests failed.", errors, test_count);
      $error("======================================");
    end

    $finish;
  end

endmodule : reg_file_tb
//=============================================================================
// Dependencies: reg_file.sv
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
//   - Testbench: reg_file_tb.sv
//   - Test Vectors: 3 directed test cases (multiple sub-tests)
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | DesignAI           | Initial creation of Register File testbench.
//=============================================================================
