//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V Core
//
// File: mem_stage_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: mem_stage_tb
// AUTHOR: Juan.Kok (juan.kok@company.com)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the mem_stage module.
// PRIMARY_PURPOSE: To verify the functional correctness of the memory stage, including data memory access and exception handling.
// ROLE_IN_SYSTEM: Unit testbench for a critical pipeline stage.
// PROBLEM_SOLVED: Ensures proper memory reads/writes and handling of memory-related exceptions.
// MODULE_TYPE: Testbench
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V Instruction Set Manual
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================
// DOCUMENTATION_PASS_FAIL: PASS
//-----------------------------------------------------------------------------
// REVISION HISTORY:
// - 1.0.0 | 2025-07-05 | Juan.Kok | Initial creation and basic test cases for memory access and exceptions.
//
//=============================================================================
// Toolchain:
//   - QuestaSim 2023.2
//
// Dependencies:
//   - rtl/core/mem_stage.sv
//   - rtl/pkg/riscv_config_pkg.sv
//   - rtl/pkg/riscv_core_pkg.sv
//   - rtl/pkg/riscv_exception_pkg.sv
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

import riscv_config_pkg::*;
import riscv_core_pkg::*;
import riscv_exception_pkg::*;

module mem_stage_tb;

  // Clock and Reset
  logic clk;
  logic rst_ni;

  // Inputs to mem_stage
  ex_mem_reg_t  ex_mem_reg_i;
  logic         flush_i;
  logic         stall_i;
  logic [31:0]  mem_read_data_i; // Data from data memory
  logic         mem_resp_valid_i; // Data memory response valid
  logic         mem_resp_error_i; // Data memory response error

  // Outputs from mem_stage
  mem_wb_reg_t  mem_wb_reg_o;
  logic         mem_wb_valid_o;
  logic         mem_wb_ready_i; // Connected to writeback_stage's ready
  logic         mem_req_valid_o; // Request to data memory
  logic [31:0]  mem_req_addr_o;  // Address to data memory
  logic [31:0]  mem_write_data_o; // Data to write to data memory
  mem_access_t  mem_access_type_o; // Type of memory access
  logic         mem_stall_o;     // Stall signal to previous stage
  logic         mem_flush_o;     // Flush signal to previous stage

  // Internal signals for testbench control
  logic         test_done;

  // Instantiate the mem_stage module
  mem_stage u_mem_stage (
    .clk_i              (clk),
    .rst_ni             (rst_ni),
    .ex_mem_reg_i       (ex_mem_reg_i),
    .flush_i            (flush_i),
    .stall_i            (stall_i),
    .mem_read_data_i    (mem_read_data_i),
    .mem_resp_valid_i   (mem_resp_valid_i),
    .mem_resp_error_i   (mem_resp_error_i),
    .mem_wb_reg_o       (mem_wb_reg_o),
    .mem_wb_valid_o     (mem_wb_valid_o),
    .mem_wb_ready_i     (mem_wb_ready_i),
    .mem_req_valid_o    (mem_req_valid_o),
    .mem_req_addr_o     (mem_req_addr_o),
    .mem_write_data_o   (mem_write_data_o),
    .mem_access_type_o  (mem_access_type_o),
    .mem_stall_o        (mem_stall_o),
    .mem_flush_o        (mem_flush_o)
  );

  // Clock Generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk; // 10ns period, 100MHz
  end

  // Reset Generation
  initial begin
    rst_ni = 0;
    #100;
    rst_ni = 1;
  end

  // Test Scenarios
  initial begin
    test_done = 0;
    mem_wb_ready_i = 1; // Always ready for simplicity in unit test

    // Initialize memory response signals
    mem_read_data_i = 0;
    mem_resp_valid_i = 0;
    mem_resp_error_i = 0;

    // Wait for reset to de-assert
    @(posedge rst_ni);
    #10;

    $display("--------------------------------------------------");
    $display("Starting Memory Stage Testbench");
    $display("--------------------------------------------------");

    // Test Case 1: Load Word (LW) - Successful Read
    // ex_mem_reg_i.alu_result = 0x1000 (address), mem_read_data_i = 0xDEADBEEF
    $display("Test Case 1: Load Word (LW) - Successful Read");
    ex_mem_reg_i.pc = 32'h80000000;
    ex_mem_reg_i.alu_result = 32'h1000; // Memory address
    ex_mem_reg_i.rd = 1;
    ex_mem_reg_i.ctrl_signals.mem_read = MEM_WORD;
    ex_mem_reg_i.ctrl_signals.mem_write = MEM_NONE;
    ex_mem_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    ex_mem_reg_i.ctrl_signals.mem_to_reg = WB_SEL_MEM;
    ex_mem_reg_i.exception_en = 0;
    flush_i = 0;
    stall_i = 0;

    @(posedge clk); #1;
    assert (mem_req_valid_o == 1 && mem_req_addr_o == 32'h1000 && mem_access_type_o == MEM_WORD)
      $info("Test Case 1.1 Passed: Memory read request issued correctly.");
    else
      $error("Test Case 1.1 Failed: Memory read request error.");

    mem_read_data_i = 32'hDEADBEEF;
    mem_resp_valid_i = 1;
    mem_resp_error_i = 0;
    @(posedge clk); #1;
    assert (mem_wb_valid_o == 1 && mem_wb_reg_o.mem_read_data == 32'hDEADBEEF && mem_wb_reg_o.rd == 1 && mem_wb_reg_o.ctrl_signals.mem_to_reg == WB_SEL_MEM)
      $info("Test Case 1.2 Passed: Memory read data propagated correctly.");
    else
      $error("Test Case 1.2 Failed: Memory read data propagation error. Expected 0xDEADBEEF, got %0h", mem_wb_reg_o.mem_read_data);
    mem_resp_valid_i = 0; // De-assert response

    // Test Case 2: Store Word (SW) - Successful Write
    // ex_mem_reg_i.alu_result = 0x2000 (address), ex_mem_reg_i.mem_write_data = 0xCAFEBABE
    $display("Test Case 2: Store Word (SW) - Successful Write");
    ex_mem_reg_i.pc = 32'h80000004;
    ex_mem_reg_i.alu_result = 32'h2000; // Memory address
    ex_mem_reg_i.mem_write_data = 32'hCAFEBABE; // Data to write
    ex_mem_reg_i.rd = 0; // Not writing to register
    ex_mem_reg_i.ctrl_signals.mem_read = MEM_NONE;
    ex_mem_reg_i.ctrl_signals.mem_write = MEM_WORD;
    ex_mem_reg_i.ctrl_signals.reg_write = REG_WRITE_DIS;
    ex_mem_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU; // Not used
    ex_mem_reg_i.exception_en = 0;

    @(posedge clk); #1;
    assert (mem_req_valid_o == 1 && mem_req_addr_o == 32'h2000 && mem_write_data_o == 32'hCAFEBABE && mem_access_type_o == MEM_WORD)
      $info("Test Case 2.1 Passed: Memory write request issued correctly.");
    else
      $error("Test Case 2.1 Failed: Memory write request error.");

    mem_resp_valid_i = 1;
    mem_resp_error_i = 0;
    @(posedge clk); #1;
    assert (mem_wb_valid_o == 1 && mem_wb_reg_o.ctrl_signals.reg_write == REG_WRITE_DIS)
      $info("Test Case 2.2 Passed: Memory write completed and pipeline advanced.");
    else
      $error("Test Case 2.2 Failed: Memory write completion error.");
    mem_resp_valid_i = 0; // De-assert response

    // Test Case 3: Load Byte Unsigned (LBU) - Successful Read
    // ex_mem_reg_i.alu_result = 0x3001 (address), mem_read_data_i = 0x12345678
    $display("Test Case 3: Load Byte Unsigned (LBU) - Successful Read");
    ex_mem_reg_i.pc = 32'h80000008;
    ex_mem_reg_i.alu_result = 32'h3001; // Address
    ex_mem_reg_i.rd = 2;
    ex_mem_reg_i.ctrl_signals.mem_read = MEM_BYTE_U;
    ex_mem_reg_i.ctrl_signals.mem_write = MEM_NONE;
    ex_mem_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    ex_mem_reg_i.ctrl_signals.mem_to_reg = WB_SEL_MEM;
    ex_mem_reg_i.exception_en = 0;

    @(posedge clk); #1;
    assert (mem_req_valid_o == 1 && mem_req_addr_o == 32'h3001 && mem_access_type_o == MEM_BYTE_U)
      $info("Test Case 3.1 Passed: Memory LBU request issued correctly.");
    else
      $error("Test Case 3.1 Failed: Memory LBU request error.");

    mem_read_data_i = 32'h12345678;
    mem_resp_valid_i = 1;
    mem_resp_error_i = 0;
    @(posedge clk); #1;
    assert (mem_wb_valid_o == 1 && mem_wb_reg_o.mem_read_data == 32'h00000056 && mem_wb_reg_o.rd == 2)
      $info("Test Case 3.2 Passed: Memory LBU data propagated correctly (byte 0x56 from 0x12345678).");
    else
      $error("Test Case 3.2 Failed: Memory LBU data propagation error. Expected 0x56, got %0h", mem_wb_reg_o.mem_read_data);
    mem_resp_valid_i = 0; // De-assert response

    // Test Case 4: Memory Read Error (Load Word)
    $display("Test Case 4: Memory Read Error (Load Word)");
    ex_mem_reg_i.pc = 32'h8000000C;
    ex_mem_reg_i.alu_result = 32'h4000; // Address
    ex_mem_reg_i.rd = 3;
    ex_mem_reg_i.ctrl_signals.mem_read = MEM_WORD;
    ex_mem_reg_i.ctrl_signals.mem_write = MEM_NONE;
    ex_mem_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    ex_mem_reg_i.ctrl_signals.mem_to_reg = WB_SEL_MEM;
    ex_mem_reg_i.exception_en = 0;

    @(posedge clk); #1;
    mem_read_data_i = 0;
    mem_resp_valid_i = 1;
    mem_resp_error_i = 1; // Simulate error
    @(posedge clk); #1;
    assert (mem_wb_valid_o == 1 && mem_wb_reg_o.exception_en == 1 && mem_wb_reg_o.exception_code == EXC_LOAD_ACCESS_FAULT)
      $info("Test Case 4 Passed: Load Access Fault exception generated correctly.");
    else
      $error("Test Case 4 Failed: Load Access Fault exception error. Exception_en: %0d, Exception_code: %0d", mem_wb_reg_o.exception_en, mem_wb_reg_o.exception_code);
    mem_resp_valid_i = 0; // De-assert response
    mem_resp_error_i = 0;

    // Test Case 5: Memory Write Error (Store Word)
    $display("Test Case 5: Memory Write Error (Store Word)");
    ex_mem_reg_i.pc = 32'h80000010;
    ex_mem_reg_i.alu_result = 32'h5000; // Address
    ex_mem_reg_i.mem_write_data = 32'h11223344;
    ex_mem_reg_i.rd = 0;
    ex_mem_reg_i.ctrl_signals.mem_read = MEM_NONE;
    ex_mem_reg_i.ctrl_signals.mem_write = MEM_WORD;
    ex_mem_reg_i.ctrl_signals.reg_write = REG_WRITE_DIS;
    ex_mem_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    ex_mem_reg_i.exception_en = 0;

    @(posedge clk); #1;
    mem_resp_valid_i = 1;
    mem_resp_error_i = 1; // Simulate error
    @(posedge clk); #1;
    assert (mem_wb_valid_o == 1 && mem_wb_reg_o.exception_en == 1 && mem_wb_reg_o.exception_code == EXC_STORE_ACCESS_FAULT)
      $info("Test Case 5 Passed: Store Access Fault exception generated correctly.");
    else
      $error("Test Case 5 Failed: Store Access Fault exception error. Exception_en: %0d, Exception_code: %0d", mem_wb_reg_o.exception_en, mem_wb_reg_o.exception_code);
    mem_resp_valid_i = 0; // De-assert response
    mem_resp_error_i = 0;

    // Test Case 6: Flush signal active
    $display("Test Case 6: Flush signal active");
    ex_mem_reg_i.pc = 32'h80000014;
    ex_mem_reg_i.alu_result = 32'h0;
    ex_mem_reg_i.ctrl_signals.mem_read = MEM_NONE;
    ex_mem_reg_i.ctrl_signals.mem_write = MEM_NONE;
    ex_mem_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    flush_i = 1;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (mem_wb_valid_o == 0 && mem_flush_o == 1)
      $info("Test Case 6 Passed: Flush signal correctly invalidates pipeline register and propagates flush.");
    else
      $error("Test Case 6 Failed: Flush signal handling error. mem_wb_valid_o: %0d, mem_flush_o: %0d", mem_wb_valid_o, mem_flush_o);
    flush_i = 0; // De-assert flush

    // Test Case 7: Stall signal active
    $display("Test Case 7: Stall signal active");
    ex_mem_reg_i.pc = 32'h80000018;
    ex_mem_reg_i.alu_result = 32'h0;
    ex_mem_reg_i.ctrl_signals.mem_read = MEM_NONE;
    ex_mem_reg_i.ctrl_signals.mem_write = MEM_NONE;
    ex_mem_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    stall_i = 1;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (mem_wb_valid_o == 0 && mem_stall_o == 1) // Assuming stall prevents new valid output and propagates stall
      $info("Test Case 7 Passed: Stall signal correctly prevents new valid output and propagates stall.");
    else
      $error("Test Case 7 Failed: Stall signal handling error. mem_wb_valid_o: %0d, mem_stall_o: %0d", mem_wb_valid_o, mem_stall_o);
    stall_i = 0; // De-assert stall

    $display("--------------------------------------------------");
    $display("Memory Stage Testbench Finished");
    $display("--------------------------------------------------");
    test_done = 1;
  end

  // Simulation Control
  always @(test_done) begin
    if (test_done) begin
      $finish;
    end
  end

endmodule : mem_stage_tb
//=============================================================================
// Dependencies:
//   - rtl/core/mem_stage.sv
//   - rtl/pkg/riscv_config_pkg.sv
//   - rtl/pkg/riscv_core_pkg.sv
//   - rtl/pkg/riscv_exception_pkg.sv
//
// Instantiated In:
//   - N/A (Unit Testbench)
//
// Performance:
//   - Critical Path: N/A
//   - Max Frequency: N/A
//   - Area: N/A
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
//   - Testbench: mem_stage_tb.sv
//   - Test Vectors: See mem_stage_tb_testcases.md
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | Juan.Kok           | Initial release
//=============================================================================
