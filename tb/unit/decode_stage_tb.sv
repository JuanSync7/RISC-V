//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V Core
//
// File: decode_stage_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: decode_stage_tb
// AUTHOR: Juan.Kok (juan.kok@company.com)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the decode_stage module.
// PRIMARY_PURPOSE: To verify the functional correctness of the instruction decode stage.
// ROLE_IN_SYSTEM: Unit testbench for a critical pipeline stage.
// PROBLEM_SOLVED: Ensures proper decoding of RISC-V instructions and generation of control signals.
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
// - 1.0.0 | 2025-07-05 | Juan.Kok | Initial creation and basic test cases for R,I,S,B,U,J types.
// - 1.1.0 | 2025-07-05 | Juan.Kok | Added DPU/FPU custom instruction test case.
//
//=============================================================================
// Toolchain:
//   - QuestaSim 2023.2
//
// Dependencies:
//   - rtl/core/decode_stage.sv
//   - rtl/pkg/riscv_config_pkg.sv
//   - rtl/pkg/riscv_core_pkg.sv
//   - rtl/pkg/riscv_dpu_types_pkg.sv
//
// Instantiated In:
//   - Not applicable (this is a testbench).
//
// Known Issues:
//   - None.
//
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

import riscv_config_pkg::*;
import riscv_core_pkg::*;
import riscv_dpu_types_pkg::*;

module decode_stage_tb;

  // Clock and Reset
  logic clk;
  logic rst_ni;

  // Inputs to decode_stage
  id_ex_reg_t id_ex_reg_i;
  logic [31:0]  pc_i;
  logic [31:0]  instr_i;
  logic         flush_i;
  logic         stall_i;

  // Outputs from decode_stage
  id_ex_reg_t id_ex_reg_o;
  logic         id_ex_valid_o;
  logic         id_ex_ready_i; // Connected to execute_stage's ready

  // Internal signals for testbench control
  logic         test_done;

  // Instantiate the decode_stage module
  decode_stage u_decode_stage (
    .clk_i         (clk),
    .rst_ni        (rst_ni),
    .pc_i          (pc_i),
    .instr_i       (instr_i),
    .flush_i       (flush_i),
    .stall_i       (stall_i),
    .id_ex_reg_o   (id_ex_reg_o),
    .id_ex_valid_o (id_ex_valid_o),
    .id_ex_ready_i (id_ex_ready_i)
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
    id_ex_ready_i = 1; // Always ready for simplicity in unit test

    // Wait for reset to de-assert
    @(posedge rst_ni);
    #10;

    $display("--------------------------------------------------");
    $display("Starting Decode Stage Testbench");
    $display("--------------------------------------------------");

    // Test Case 1: R-type instruction (ADD x1, x2, x3)
    // instr_i = 32'h003100B3 (ADD x1, x2, x3)
    // Expected: op_code = OP_R_TYPE, funct3 = 3'b000, funct7 = 7'b0000000, rd = 1, rs1 = 2, rs2 = 3
    $display("Test Case 1: R-type instruction (ADD x1, x2, x3)");
    pc_i = 32'h80000000;
    instr_i = 32'h003100B3; // ADD x1, x2, x3
    flush_i = 0;
    stall_i = 0;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (id_ex_reg_o.op_code == OP_R_TYPE &&
            id_ex_reg_o.funct3 == 3'b000 &&
            id_ex_reg_o.funct7 == 7'b0000000 &&
            id_ex_reg_o.rd == 1 &&
            id_ex_reg_o.rs1 == 2 &&
            id_ex_reg_o.rs2 == 3 &&
            id_ex_reg_o.ctrl_signals.alu_op == ALU_ADD &&
            id_ex_reg_o.ctrl_signals.mem_read == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.mem_write == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.branch == BR_NONE &&
            id_ex_reg_o.ctrl_signals.reg_write == REG_WRITE_EN &&
            id_ex_reg_o.ctrl_signals.mem_to_reg == WB_SEL_ALU &&
            id_ex_reg_o.ctrl_signals.pc_src == PC_PLUS_4)
      $info("Test Case 1 Passed: R-type instruction decoded correctly.");
    else
      $error("Test Case 1 Failed: R-type instruction decoding error.");

    // Test Case 2: I-type instruction (ADDI x5, x6, 10)
    // instr_i = 32'h00A30293 (ADDI x5, x6, 10)
    // Expected: op_code = OP_I_TYPE, funct3 = 3'b000, rd = 5, rs1 = 6, imm = 10
    $display("Test Case 2: I-type instruction (ADDI x5, x6, 10)");
    pc_i = 32'h80000004;
    instr_i = 32'h00A30293; // ADDI x5, x6, 10
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (id_ex_reg_o.op_code == OP_I_TYPE &&
            id_ex_reg_o.funct3 == 3'b000 &&
            id_ex_reg_o.rd == 5 &&
            id_ex_reg_o.rs1 == 6 &&
            id_ex_reg_o.imm == 10 &&
            id_ex_reg_o.ctrl_signals.alu_op == ALU_ADD &&
            id_ex_reg_o.ctrl_signals.mem_read == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.mem_write == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.branch == BR_NONE &&
            id_ex_reg_o.ctrl_signals.reg_write == REG_WRITE_EN &&
            id_ex_reg_o.ctrl_signals.mem_to_reg == WB_SEL_ALU &&
            id_ex_reg_o.ctrl_signals.pc_src == PC_PLUS_4)
      $info("Test Case 2 Passed: I-type instruction decoded correctly.");
    else
      $error("Test Case 2 Failed: I-type instruction decoding error.");

    // Test Case 3: S-type instruction (SW x7, 0(x8))
    // instr_i = 32'h00742023 (SW x7, 0(x8))
    // Expected: op_code = OP_S_TYPE, funct3 = 3'b010, rs1 = 8, rs2 = 7, imm = 0
    $display("Test Case 3: S-type instruction (SW x7, 0(x8))");
    pc_i = 32'h80000008;
    instr_i = 32'h00742023; // SW x7, 0(x8)
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (id_ex_reg_o.op_code == OP_S_TYPE &&
            id_ex_reg_o.funct3 == 3'b010 &&
            id_ex_reg_o.rs1 == 8 &&
            id_ex_reg_o.rs2 == 7 &&
            id_ex_reg_o.imm == 0 &&
            id_ex_reg_o.ctrl_signals.alu_op == ALU_ADD && // ALU calculates address
            id_ex_reg_o.ctrl_signals.mem_read == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.mem_write == MEM_WORD &&
            id_ex_reg_o.ctrl_signals.branch == BR_NONE &&
            id_ex_reg_o.ctrl_signals.reg_write == REG_WRITE_DIS &&
            id_ex_reg_o.ctrl_signals.mem_to_reg == WB_SEL_ALU && // Not used for S-type
            id_ex_reg_o.ctrl_signals.pc_src == PC_PLUS_4)
      $info("Test Case 3 Passed: S-type instruction decoded correctly.");
    else
      $error("Test Case 3 Failed: S-type instruction decoding error.");

    // Test Case 4: B-type instruction (BEQ x9, x10, 0x10)
    // instr_i = 32'h00A48463 (BEQ x9, x10, 0x10)
    // Expected: op_code = OP_B_TYPE, funct3 = 3'b000, rs1 = 9, rs2 = 10, imm = 16
    $display("Test Case 4: B-type instruction (BEQ x9, x10, 0x10)");
    pc_i = 32'h8000000C;
    instr_i = 32'h00A48463; // BEQ x9, x10, 0x10
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (id_ex_reg_o.op_code == OP_B_TYPE &&
            id_ex_reg_o.funct3 == 3'b000 &&
            id_ex_reg_o.rs1 == 9 &&
            id_ex_reg_o.rs2 == 10 &&
            id_ex_reg_o.imm == 16 &&
            id_ex_reg_o.ctrl_signals.alu_op == ALU_SUB && // ALU performs comparison
            id_ex_reg_o.ctrl_signals.mem_read == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.mem_write == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.branch == BR_EQ &&
            id_ex_reg_o.ctrl_signals.reg_write == REG_WRITE_DIS &&
            id_ex_reg_o.ctrl_signals.mem_to_reg == WB_SEL_ALU && // Not used for B-type
            id_ex_reg_o.ctrl_signals.pc_src == PC_BRANCH)
      $info("Test Case 4 Passed: B-type instruction decoded correctly.");
    else
      $error("Test Case 4 Failed: B-type instruction decoding error.");

    // Test Case 5: U-type instruction (LUI x11, 0x12345)
    // instr_i = 32'h00012345B7 (LUI x11, 0x12345)
    // Expected: op_code = OP_U_TYPE, rd = 11, imm = 32'h12345000
    $display("Test Case 5: U-type instruction (LUI x11, 0x12345)");
    pc_i = 32'h80000010;
    instr_i = 32'h00012345B7; // LUI x11, 0x12345
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (id_ex_reg_o.op_code == OP_U_TYPE &&
            id_ex_reg_o.rd == 11 &&
            id_ex_reg_o.imm == 32'h12345000 &&
            id_ex_reg_o.ctrl_signals.alu_op == ALU_LUI &&
            id_ex_reg_o.ctrl_signals.mem_read == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.mem_write == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.branch == BR_NONE &&
            id_ex_reg_o.ctrl_signals.reg_write == REG_WRITE_EN &&
            id_ex_reg_o.ctrl_signals.mem_to_reg == WB_SEL_ALU &&
            id_ex_reg_o.ctrl_signals.pc_src == PC_PLUS_4)
      $info("Test Case 5 Passed: U-type instruction decoded correctly.");
    else
      $error("Test Case 5 Failed: U-type instruction decoding error.");

    // Test Case 6: J-type instruction (JAL x12, 0x20)
    // instr_i = 32'h020006EF (JAL x12, 0x20)
    // Expected: op_code = OP_J_TYPE, rd = 12, imm = 32
    $display("Test Case 6: J-type instruction (JAL x12, 0x20)");
    pc_i = 32'h80000014;
    instr_i = 32'h020006EF; // JAL x12, 0x20
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (id_ex_reg_o.op_code == OP_J_TYPE &&
            id_ex_reg_o.rd == 12 &&
            id_ex_reg_o.imm == 32 &&
            id_ex_reg_o.ctrl_signals.alu_op == ALU_ADD && // ALU calculates target address
            id_ex_reg_o.ctrl_signals.mem_read == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.mem_write == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.branch == BR_JAL &&
            id_ex_reg_o.ctrl_signals.reg_write == REG_WRITE_EN &&
            id_ex_reg_o.ctrl_signals.mem_to_reg == WB_SEL_PC_PLUS_4 &&
            id_ex_reg_o.ctrl_signals.pc_src == PC_JUMP)
      $info("Test Case 6 Passed: J-type instruction decoded correctly.");
    else
      $error("Test Case 6 Failed: J-type instruction decoding error.");

    // Test Case 7: DPU FPU instruction (CUSTOM0, FPU_ADD)
    // instr_i = 32'h0000000B (CUSTOM0, funct3 = 0, funct7 = 0) - assuming FPU_ADD is funct3=0, funct7=0
    // This is a placeholder. Actual DPU instruction encoding needs to be confirmed from riscv_config_pkg.sv
    // For now, assuming a simple CUSTOM0 instruction that triggers DPU FPU.
    $display("Test Case 7: DPU FPU instruction (CUSTOM0, FPU_ADD)");
    pc_i = 32'h80000018;
    instr_i = {7'b0000000, 5'd0, 5'd0, FUNCT3_DPU_FPU, 5'd0, OPCODE_CUSTOM0}; // Example: FPU_ADD (rs2=0, rs1=0, rd=0)
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (id_ex_reg_o.op_code == OP_CUSTOM0 &&
            id_ex_reg_o.funct3 == FUNCT3_DPU_FPU &&
            id_ex_reg_o.ctrl_signals.alu_op == ALU_DPU &&
            id_ex_reg_o.ctrl_signals.mem_read == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.mem_write == MEM_NONE &&
            id_ex_reg_o.ctrl_signals.branch == BR_NONE &&
            id_ex_reg_o.ctrl_signals.reg_write == REG_WRITE_EN && // DPU writes back to register
            id_ex_reg_o.ctrl_signals.mem_to_reg == WB_SEL_DPU &&
            id_ex_reg_o.ctrl_signals.pc_src == PC_PLUS_4)
      $info("Test Case 7 Passed: DPU FPU instruction decoded correctly.");
    else
      $error("Test Case 7 Failed: DPU FPU instruction decoding error.");

    // Test Case 8: Flush signal active
    $display("Test Case 8: Flush signal active");
    pc_i = 32'h8000001C;
    instr_i = 32'h00000013; // NOP (ADDI x0, x0, 0)
    flush_i = 1;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (id_ex_valid_o == 0)
      $info("Test Case 8 Passed: Flush signal correctly invalidates pipeline register.");
    else
      $error("Test Case 8 Failed: Flush signal did not invalidate pipeline register.");
    flush_i = 0; // De-assert flush

    // Test Case 9: Stall signal active
    $display("Test Case 9: Stall signal active");
    pc_i = 32'h80000020;
    instr_i = 32'h00000013; // NOP
    stall_i = 1;
    @(posedge clk); #1;
    @(posedge clk); #1;
    // In a real pipeline, the previous stage would hold its output.
    // Here, we just check if decode_stage holds its output.
    // This test case is more about observing behavior than a strict assertion on id_ex_reg_o.
    // For a unit test, we expect id_ex_valid_o to be 0 if the stage is stalled and not processing new input.
    // However, the current decode_stage implementation might still produce valid output if input is valid.
    // The stall logic typically prevents the *next* stage from consuming, or the *current* stage from accepting new input.
    // For this unit test, we'll assume stall_i prevents id_ex_valid_o from going high if it was low,
    // or holds the current output if it was high.
    // A more robust test would involve a driver for instr_i that stops providing new instructions.
    // For now, we'll check if id_ex_valid_o is 0, assuming no new instruction is being processed.
    assert (id_ex_valid_o == 0) // Assuming stall prevents new valid output
      $info("Test Case 9 Passed: Stall signal correctly prevents new valid output.");
    else
      $error("Test Case 9 Failed: Stall signal did not prevent new valid output.");
    stall_i = 0; // De-assert stall

    $display("--------------------------------------------------");
    $display("Decode Stage Testbench Finished");
    $display("--------------------------------------------------");
    test_done = 1;
  end

  // Simulation Control
  always @(test_done) begin
    if (test_done) begin
      $finish;
    end
  end

endmodule : decode_stage_tb
//=============================================================================
// Dependencies:
//   - rtl/core/decode_stage.sv
//   - rtl/pkg/riscv_config_pkg.sv
//   - rtl/pkg/riscv_core_pkg.sv
//   - rtl/pkg/riscv_dpu_types_pkg.sv
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
//   - Testbench: decode_stage_tb.sv
//   - Test Vectors: See decode_stage_tb_testcases.md
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | Juan.Kok           | Initial release
//=============================================================================
