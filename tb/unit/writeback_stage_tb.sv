//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V Core
//
// File: writeback_stage_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: writeback_stage_tb
// AUTHOR: Juan.Kok (juan.kok@company.com)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the writeback_stage module.
// PRIMARY_PURPOSE: To verify the functional correctness of the writeback stage, including result selection and register file write.
// ROLE_IN_SYSTEM: Unit testbench for a critical pipeline stage.
// PROBLEM_SOLVED: Ensures correct data is written back to the register file from various sources (ALU, Memory, PC+4, DPU).
// MODULE_TYPE: Testbench
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V Instruction Set Manual
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

import riscv_config_pkg::*;
import riscv_core_pkg::*;

module writeback_stage_tb;

  // Clock and Reset
  logic clk;
  logic rst_ni;

  // Inputs to writeback_stage
  mem_wb_reg_t  mem_wb_reg_i;
  logic         flush_i;
  logic         stall_i;

  // Outputs from writeback_stage
  logic [4:0]   wb_rd_addr_o;
  logic [31:0]  wb_write_data_o;
  logic         wb_reg_write_en_o;

  // Internal signals for testbench control
  logic         test_done;

  // Instantiate the writeback_stage module
  writeback_stage u_writeback_stage (
    .clk_i              (clk),
    .rst_ni             (rst_ni),
    .mem_wb_reg_i       (mem_wb_reg_i),
    .flush_i            (flush_i),
    .stall_i            (stall_i),
    .wb_rd_addr_o       (wb_rd_addr_o),
    .wb_write_data_o    (wb_write_data_o),
    .wb_reg_write_en_o  (wb_reg_write_en_o)
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

    // Wait for reset to de-assert
    @(posedge rst_ni);
    #10;

    $display("--------------------------------------------------");
    $display("Starting Writeback Stage Testbench");
    $display("--------------------------------------------------");

    // Test Case 1: Writeback from ALU (WB_SEL_ALU)
    // ALU result = 100, rd = 5, reg_write_en = 1
    $display("Test Case 1: Writeback from ALU");
    mem_wb_reg_i.alu_result = 100;
    mem_wb_reg_i.mem_read_data = 0; // Not used
    mem_wb_reg_i.dpu_result = 0; // Not used
    mem_wb_reg_i.pc_plus_4 = 0; // Not used
    mem_wb_reg_i.rd = 5;
    mem_wb_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    mem_wb_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    flush_i = 0;
    stall_i = 0;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (wb_rd_addr_o == 5 && wb_write_data_o == 100 && wb_reg_write_en_o == REG_WRITE_EN)
      $info("Test Case 1 Passed: Writeback from ALU successful.");
    else
      $error("Test Case 1 Failed: Writeback from ALU error. Addr: %0d, Data: %0d, En: %0d", wb_rd_addr_o, wb_write_data_o, wb_reg_write_en_o);

    // Test Case 2: Writeback from Memory (WB_SEL_MEM)
    // Memory read data = 0xABCDEF01, rd = 10, reg_write_en = 1
    $display("Test Case 2: Writeback from Memory");
    mem_wb_reg_i.alu_result = 0; // Not used
    mem_wb_reg_i.mem_read_data = 32'hABCDEF01;
    mem_wb_reg_i.dpu_result = 0; // Not used
    mem_wb_reg_i.pc_plus_4 = 0; // Not used
    mem_wb_reg_i.rd = 10;
    mem_wb_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    mem_wb_reg_i.ctrl_signals.mem_to_reg = WB_SEL_MEM;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (wb_rd_addr_o == 10 && wb_write_data_o == 32'hABCDEF01 && wb_reg_write_en_o == REG_WRITE_EN)
      $info("Test Case 2 Passed: Writeback from Memory successful.");
    else
      $error("Test Case 2 Failed: Writeback from Memory error. Addr: %0d, Data: %0h, En: %0d", wb_rd_addr_o, wb_write_data_o, wb_reg_write_en_o);

    // Test Case 3: Writeback PC+4 (WB_SEL_PC_PLUS_4) for JAL
    // PC+4 = 0x80000004, rd = 1, reg_write_en = 1
    $display("Test Case 3: Writeback PC+4 for JAL");
    mem_wb_reg_i.alu_result = 0; // Not used
    mem_wb_reg_i.mem_read_data = 0; // Not used
    mem_wb_reg_i.dpu_result = 0; // Not used
    mem_wb_reg_i.pc_plus_4 = 32'h80000004;
    mem_wb_reg_i.rd = 1;
    mem_wb_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    mem_wb_reg_i.ctrl_signals.mem_to_reg = WB_SEL_PC_PLUS_4;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (wb_rd_addr_o == 1 && wb_write_data_o == 32'h80000004 && wb_reg_write_en_o == REG_WRITE_EN)
      $info("Test Case 3 Passed: Writeback PC+4 successful.");
    else
      $error("Test Case 3 Failed: Writeback PC+4 error. Addr: %0d, Data: %0h, En: %0d", wb_rd_addr_o, wb_write_data_o, wb_reg_write_en_o);

    // Test Case 4: Writeback from DPU (WB_SEL_DPU)
    // DPU result = 0x12345678, rd = 7, reg_write_en = 1
    $display("Test Case 4: Writeback from DPU");
    mem_wb_reg_i.alu_result = 0; // Not used
    mem_wb_reg_i.mem_read_data = 0; // Not used
    mem_wb_reg_i.dpu_result = 32'h12345678;
    mem_wb_reg_i.pc_plus_4 = 0; // Not used
    mem_wb_reg_i.rd = 7;
    mem_wb_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    mem_wb_reg_i.ctrl_signals.mem_to_reg = WB_SEL_DPU;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (wb_rd_addr_o == 7 && wb_write_data_o == 32'h12345678 && wb_reg_write_en_o == REG_WRITE_EN)
      $info("Test Case 4 Passed: Writeback from DPU successful.");
    else
      $error("Test Case 4 Failed: Writeback from DPU error. Addr: %0d, Data: %0h, En: %0d", wb_rd_addr_o, wb_write_data_o, wb_reg_write_en_o);

    // Test Case 5: No Register Write (REG_WRITE_DIS)
    // Should not write to register file
    $display("Test Case 5: No Register Write");
    mem_wb_reg_i.alu_result = 200;
    mem_wb_reg_i.rd = 6;
    mem_wb_reg_i.ctrl_signals.reg_write = REG_WRITE_DIS;
    mem_wb_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (wb_reg_write_en_o == REG_WRITE_DIS)
      $info("Test Case 5 Passed: No register write when REG_WRITE_DIS.");
    else
      $error("Test Case 5 Failed: Register write enabled when it should be disabled. En: %0d", wb_reg_write_en_o);

    // Test Case 6: Flush signal active
    $display("Test Case 6: Flush signal active");
    mem_wb_reg_i.alu_result = 300;
    mem_wb_reg_i.rd = 8;
    mem_wb_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    mem_wb_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    flush_i = 1;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (wb_reg_write_en_o == REG_WRITE_DIS) // Flush should disable write
      $info("Test Case 6 Passed: Flush signal correctly disables register write.");
    else
      $error("Test Case 6 Failed: Flush signal did not disable register write. En: %0d", wb_reg_write_en_o);
    flush_i = 0; // De-assert flush

    // Test Case 7: Stall signal active
    $display("Test Case 7: Stall signal active");
    mem_wb_reg_i.alu_result = 400;
    mem_wb_reg_i.rd = 9;
    mem_wb_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    mem_wb_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    stall_i = 1;
    @(posedge cllk); #1;
    @(posedge clk); #1;
    assert (wb_reg_write_en_o == REG_WRITE_DIS) // Stall should disable write
      $info("Test Case 7 Passed: Stall signal correctly disables register write.");
    else
      $error("Test Case 7 Failed: Stall signal did not disable register write. En: %0d", wb_reg_write_en_o);
    stall_i = 0; // De-assert stall

    $display("--------------------------------------------------");
    $display("Writeback Stage Testbench Finished");
    $display("--------------------------------------------------");
    test_done = 1;
  end

  // Simulation Control
  always @(test_done) begin
    if (test_done) begin
      $finish;
    end
  end

endmodule : writeback_stage_tb
//=============================================================================
// Dependencies:
//   - rtl/core/writeback_stage.sv
//   - rtl/pkg/riscv_config_pkg.sv
//   - rtl/pkg/riscv_core_pkg.sv
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
//   - Testbench: writeback_stage_tb.sv
//   - Test Vectors: See writeback_stage_tb_testcases.md
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | Juan.Kok           | Initial release
//=============================================================================
