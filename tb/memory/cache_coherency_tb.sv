//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V
//
// File: cache_coherency_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: cache_coherency_tb
// AUTHOR: DesignAI (<author_email@company.com>)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for verifying MESI cache coherency protocol compliance.
// PRIMARY_PURPOSE: To simulate multi-core memory accesses and ensure the MESI protocol correctly maintains data consistency across caches.
// ROLE_IN_SYSTEM: Integration test for the cache coherency controller and associated cache units.
// PROBLEM_SOLVED: Validates that shared data is correctly updated and invalidated across multiple caches, preventing stale data issues.
// MODULE_TYPE: Testbench_Component
// TARGET_TECHNOLOGY_PREF: N/A (Simulation only)
// RELATED_SPECIFICATION: MESI Protocol Specification
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

module cache_coherency_tb;

  import riscv_cache_types_pkg::*;
  import riscv_mem_types_pkg::*;
  import riscv_protocol_types_pkg::*;

  // AI_TAG: FEATURE - Verification of MESI states (Modified, Exclusive, Shared, Invalid).
  // AI_TAG: FEATURE - Testing of read/write hits and misses in different cache states.
  // AI_TAG: FEATURE - Simulation of cache-to-cache transfers and invalidation messages.
  // AI_TAG: FEATURE - Multi-core traffic generation for shared memory locations.
  // AI_TAG: FEATURE - Self-checking scoreboard to detect coherency violations.

  // Testbench Parameters
  parameter integer NUM_CORES = 2;    // AI_TAG: PARAM_DESC - Number of simulated cores/caches.
                                      // AI_TAG: PARAM_USAGE - Defines the scale of the coherency test.
                                      // AI_TAG: PARAM_CONSTRAINTS - Must be >= 2.
  parameter integer DATA_WIDTH = 32;  // AI_TAG: PARAM_DESC - Data width of cache lines.
                                      // AI_TAG: PARAM_USAGE - Affects the size of data transferred.
                                      // AI_TAG: PARAM_CONSTRAINTS - Must be a multiple of 8.
  parameter integer ADDR_WIDTH = 32;  // AI_TAG: PARAM_DESC - Address width.
                                      // AI_TAG: PARAM_USAGE - Defines the addressable memory space.
                                      // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.

  // Clock and Reset Signals
  logic clk;  // AI_TAG: PORT_DESC - Testbench clock.
              // AI_TAG: PORT_CLK_DOMAIN - clk
  logic rst_n; // AI_TAG: PORT_DESC - Active-low asynchronous reset.
               // AI_TAG: PORT_CLK_DOMAIN - clk (async assert)
               // AI_TAG: PORT_TIMING - Asynchronous

  // Core Interface Signals (simplified for each core)
  // Each core has its own request/response interface to its L1 cache
  logic [NUM_CORES-1:0] core_req_valid; // AI_TAG: PORT_DESC - Core request valid.
                                        // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [NUM_CORES-1:0][ADDR_WIDTH-1:0] core_req_addr; // AI_TAG: PORT_DESC - Core request address.
                                                     // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [NUM_CORES-1:0] core_req_write; // AI_TAG: PORT_DESC - Core request type (read/write).
                                        // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [NUM_CORES-1:0][DATA_WIDTH-1:0] core_req_wdata; // AI_TAG: PORT_DESC - Core write data.
                                                      // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [NUM_CORES-1:0] core_rsp_valid; // AI_TAG: PORT_DESC - Core response valid.
                                        // AI_TAG: PORT_CLK_DOMAIN - clk
                                        // AI_TAG: PORT_DEFAULT_STATE - 1'b0
  logic [NUM_CORES-1:0][DATA_WIDTH-1:0] core_rsp_rdata; // AI_TAG: PORT_DESC - Core read data.
                                                      // AI_TAG: PORT_CLK_DOMAIN - clk
                                                      // AI_TAG: PORT_DEFAULT_STATE - '0

  // Cache Coherency Controller Interface (to/from caches and main memory)
  // Simplified representation for TB, actual DUT would have complex interfaces
  logic                         cc_req_valid; // AI_TAG: PORT_DESC - Coherency controller request valid.
                                              // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [ADDR_WIDTH-1:0]        cc_req_addr;  // AI_TAG: PORT_DESC - Coherency controller request address.
                                              // AI_TAG: PORT_CLK_DOMAIN - clk
  logic                         cc_rsp_valid; // AI_TAG: PORT_DESC - Coherency controller response valid.
                                              // AI_TAG: PORT_CLK_DOMAIN - clk
  logic [DATA_WIDTH-1:0]        cc_rsp_data;  // AI_TAG: PORT_DESC - Coherency controller response data.
                                              // AI_TAG: PORT_CLK_DOMAIN - clk

  // Internal Testbench Variables
  integer test_count;
  integer errors;
  logic [DATA_WIDTH-1:0] main_memory [ADDR_WIDTH-1:0]; // AI_TAG: INTERNAL_STORAGE - main_memory - Behavioral model of main memory.
                                                      // AI_TAG: INTERNAL_STORAGE_TYPE - Array
                                                      // AI_TAG: INTERNAL_STORAGE_ACCESS - Read/write by testbench and simulated caches.

  // Behavioral Cache Models (simplified for coherency testing)
  // In a real scenario, these would be actual cache DUTs or more complex behavioral models
  logic [NUM_CORES-1:0][ADDR_WIDTH-1:0] cache_tags [1023:0]; // Simplified tags for 1KB direct-mapped cache
  logic [NUM_CORES-1:0][DATA_WIDTH-1:0] cache_data [1023:0]; // Simplified data for 1KB direct-mapped cache
  logic [NUM_CORES-1:0][1:0]            cache_state [1023:0]; // MESI state: 00=Invalid, 01=Shared, 10=Exclusive, 11=Modified

  // Instantiate the Cache Coherency Controller (DUT)
  // Assuming cache_coherency_controller.sv is located in rtl/memory/coherency/
  cache_coherency_controller #(
    .NUM_CORES(NUM_CORES),
    .DATA_WIDTH(DATA_WIDTH),
    .ADDR_WIDTH(ADDR_WIDTH)
  ) u_coherency_ctrl ( // AI_TAG: IF_TYPE - Cache Coherency Controller Instance
                       // AI_TAG: IF_DESC - Instance of the Cache Coherency Controller under test.
                       // AI_TAG: IF_CLOCKING - clk
                       // AI_TAG: IF_RESET - rst_n
    .clk_i          (clk),
    .rst_ni         (rst_n),
    .core_req_valid_i(core_req_valid),
    .core_req_addr_i(core_req_addr),
    .core_req_write_i(core_req_write),
    .core_req_wdata_i(core_req_wdata),
    .core_rsp_valid_o(core_rsp_valid),
    .core_rsp_rdata_o(core_rsp_rdata),
    .cc_req_valid_o (cc_req_valid),
    .cc_req_addr_o  (cc_req_addr),
    .cc_rsp_valid_i (cc_rsp_valid),
    .cc_rsp_data_i  (cc_rsp_data)
  );

  // Clock Generation
  always #5 clk = ~clk;

  // Main Memory Behavioral Model
  initial begin
    for (int i = 0; i < ADDR_WIDTH; i++) begin
      main_memory[i] = i; // Initialize memory with address value
    end
  end

  // Test Sequence
  initial begin
    clk = 0;
    rst_n = 0;
    test_count = 0;
    errors = 0;

    // AI_TAG: SCENARIO_START - Initial Reset and Initialization
    // Apply reset and initialize testbench variables and cache states.
    // AI_TAG: SCENARIO_END
    #10;
    rst_n = 1;
    #10;

    // Initialize behavioral caches to Invalid state
    for (int c = 0; c < NUM_CORES; c++) begin
      for (int i = 0; i < 1024; i++) begin
        cache_state[c][i] = 2'b00; // Invalid
        cache_tags[c][i] = '0;
        cache_data[c][i] = '0;
      end
    end

    // AI_TAG: SCENARIO_START - Single Core Read Miss (Fetch from Memory)
    // Core 0 reads an address, resulting in a miss and line fill from main memory.
    // AI_TAG: SCENARIO_END

    // Test 1: Core 0 Read Miss
    test_count++;
    core_req_valid[0] = 1; core_req_addr[0] = 32'h1000; core_req_write[0] = 0;
    #10;
    core_req_valid[0] = 0;
    // Simulate memory response to coherency controller
    cc_rsp_valid = 1; cc_rsp_data = main_memory[32'h1000];
    #10;
    cc_rsp_valid = 0;
    // Check core 0 response and cache state
    if (core_rsp_rdata[0] !== main_memory[32'h1000] || cache_state[0][(32'h1000 % 1024)] !== 2'b10) begin // Expected Exclusive
      $error("Test %0d (Core 0 Read Miss): Failed. Rdata: %h, State: %b", test_count, core_rsp_rdata[0], cache_state[0][(32'h1000 % 1024)]);
      errors++;
    end else begin
      $info("Test %0d (Core 0 Read Miss): Passed.", test_count);
    end

    // AI_TAG: SCENARIO_START - Multi-Core Shared Read (Shared State)
    // Core 0 has data in Exclusive, Core 1 reads same data, both should end in Shared state.
    // AI_TAG: SCENARIO_END

    // Test 2: Core 1 Read of Shared Data
    test_count++;
    core_req_valid[1] = 1; core_req_addr[1] = 32'h1000; core_req_write[1] = 0;
    #10;
    core_req_valid[1] = 0;
    // No memory response needed, should be cache-to-cache transfer
    #10;
    // Check core 1 response and both cache states
    if (core_rsp_rdata[1] !== main_memory[32'h1000] || cache_state[0][(32'h1000 % 1024)] !== 2'b01 || cache_state[1][(32'h1000 % 1024)] !== 2'b01) begin // Expected Shared
      $error("Test %0d (Shared Read): Failed. Rdata: %h, Core0 State: %b, Core1 State: %b", test_count, core_rsp_rdata[1], cache_state[0][(32'h1000 % 1024)], cache_state[1][(32'h1000 % 1024)]);
      errors++;
    end else begin
      $info("Test %0d (Shared Read): Passed.", test_count);
    end

    // AI_TAG: SCENARIO_START - Write to Shared Data (Invalidation)
    // Core 0 writes to data in Shared state, Core 1's copy should be invalidated.
    // AI_TAG: SCENARIO_END

    // Test 3: Core 0 Write to Shared Data
    test_count++;
    core_req_valid[0] = 1; core_req_addr[0] = 32'h1000; core_req_write[0] = 1; core_req_wdata[0] = 32'hDEADBEEF;
    #10;
    core_req_valid[0] = 0;
    // Simulate memory write completion (if write-through) or just wait for invalidation
    #10;
    // Check core 0 cache state (Modified) and core 1 cache state (Invalid)
    if (cache_state[0][(32'h1000 % 1024)] !== 2'b11 || cache_state[1][(32'h1000 % 1024)] !== 2'b00) begin // Expected Modified and Invalid
      $error("Test %0d (Write Shared): Failed. Core0 State: %b, Core1 State: %b", test_count, cache_state[0][(32'h1000 % 1024)], cache_state[1][(32'h1000 % 1024)]);
      errors++;
    end else begin
      $info("Test %0d (Write Shared): Passed.", test_count);
    end

    // Final Report
    if (errors == 0) begin
      $display("======================================");
      $display("All %0d Cache Coherency tests passed successfully!", test_count);
      $display("======================================");
    end else begin
      $error("======================================");
      $error("%0d out of %0d Cache Coherency tests failed.", errors, test_count);
      $error("======================================");
    end

    $finish;
  end

endmodule : cache_coherency_tb
//=============================================================================
// Dependencies: cache_coherency_controller.sv, riscv_cache_types_pkg.sv, riscv_mem_types_pkg.sv, riscv_protocol_types_pkg.sv
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
//   - Testbench: cache_coherency_tb.sv
//   - Test Vectors: 3 directed test cases
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | DesignAI           | Initial creation of Cache Coherency testbench.
//=============================================================================
