//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V Core
//
// File: execute_stage_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: execute_stage_tb
// AUTHOR: Juan.Kok (juan.kok@company.com)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the execute_stage module.
// PRIMARY_PURPOSE: To verify the functional correctness of the execute stage, including ALU, DPU, and exception handling.
// ROLE_IN_SYSTEM: Unit testbench for a critical pipeline stage.
// PROBLEM_SOLVED: Ensures proper execution of instructions, DPU operations, and exception generation.
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
// - 1.0.0 | 2025-07-05 | Juan.Kok | Initial creation and basic test cases for ALU and branch operations.
// - 1.1.0 | 2025-07-05 | Juan.Kok | Added DPU/FPU custom instruction test case and bypass logic placeholders.
//
//=============================================================================
// Toolchain:
//   - QuestaSim 2023.2
//
// Dependencies:
//   - rtl/core/execute_stage.sv
//   - rtl/pkg/riscv_config_pkg.sv
//   - rtl/pkg/riscv_core_pkg.sv
//   - rtl/pkg/riscv_dpu_types_pkg.sv
//   - rtl/pkg/riscv_exception_pkg.sv
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

import riscv_config_pkg::*;
import riscv_core_pkg::*;
import riscv_dpu_types_pkg::*;
import riscv_exception_pkg::*;

module execute_stage_tb;

  // Clock and Reset
  logic clk;
  logic rst_ni;

  // Inputs to execute_stage
  id_ex_reg_t id_ex_reg_i;
  logic         flush_i;
  logic         stall_i;
  logic [31:0]  mem_result_i; // From memory stage for bypass
  logic [31:0]  wb_result_i;  // From writeback stage for bypass
  logic [4:0]   mem_rd_addr_i;
  logic [4:0]   wb_rd_addr_i;
  logic         mem_reg_write_en_i;
  logic         wb_reg_write_en_i;

  // Outputs from execute_stage
  ex_mem_reg_t  ex_mem_reg_o;
  logic         ex_mem_valid_o;
  logic         ex_mem_ready_i; // Connected to memory_stage's ready
  logic         ex_stall_o;     // Stall signal to previous stage
  logic         ex_flush_o;     // Flush signal to previous stage

  // Internal signals for testbench control
  logic         test_done;

  // Instantiate the execute_stage module
  execute_stage u_execute_stage (
    .clk_i              (clk),
    .rst_ni             (rst_ni),
    .id_ex_reg_i        (id_ex_reg_i),
    .flush_i            (flush_i),
    .stall_i            (stall_i),
    .mem_result_i       (mem_result_i),
    .wb_result_i        (wb_result_i),
    .mem_rd_addr_i      (mem_rd_addr_i),
    .wb_rd_addr_i       (wb_rd_addr_i),
    .mem_reg_write_en_i (mem_reg_write_en_i),
    .wb_reg_write_en_i  (wb_reg_write_en_i),
    .ex_mem_reg_o       (ex_mem_reg_o),
    .ex_mem_valid_o     (ex_mem_valid_o),
    .ex_mem_ready_i     (ex_mem_ready_i),
    .ex_stall_o         (ex_stall_o),
    .ex_flush_o         (ex_flush_o)
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
    ex_mem_ready_i = 1; // Always ready for simplicity in unit test

    // Initialize bypass signals
    mem_result_i = 0;
    wb_result_i = 0;
    mem_rd_addr_i = 0;
    wb_rd_addr_i = 0;
    mem_reg_write_en_i = 0;
    wb_reg_write_en_i = 0;

    // Wait for reset to de-assert
    @(posedge rst_ni);
    #10;

    $display("--------------------------------------------------");
    $display("Starting Execute Stage Testbench");
    $display("--------------------------------------------------");

    // Test Case 1: R-type instruction (ADD x1, x2, x3) - No bypass
    // x2 = 10, x3 = 20. Expected result: x1 = 30
    $display("Test Case 1: R-type instruction (ADD x1, x2, x3) - No bypass");
    id_ex_reg_i.pc = 32'h80000000;
    id_ex_reg_i.instr = 32'h003100B3; // ADD x1, x2, x3
    id_ex_reg_i.op_code = OP_R_TYPE;
    id_ex_reg_i.funct3 = 3'b000;
    id_ex_reg_i.funct7 = 7'b0000000;
    id_ex_reg_i.rd = 1;
    id_ex_reg_i.rs1 = 2;
    id_ex_reg_i.rs2 = 3;
    id_ex_reg_i.op1 = 10; // Value of x2
    id_ex_reg_i.op2 = 20; // Value of x3
    id_ex_reg_i.ctrl_signals.alu_op = ALU_ADD;
    id_ex_reg_i.ctrl_signals.mem_read = MEM_NONE;
    id_ex_reg_i.ctrl_signals.mem_write = MEM_NONE;
    id_ex_reg_i.ctrl_signals.branch = BR_NONE;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    id_ex_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    id_ex_reg_i.ctrl_signals.pc_src = PC_PLUS_4;
    flush_i = 0;
    stall_i = 0;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (ex_mem_reg_o.alu_result == 30 &&
            ex_mem_reg_o.rd == 1 &&
            ex_mem_reg_o.ctrl_signals.reg_write == REG_WRITE_EN)
      $info("Test Case 1 Passed: R-type ADD instruction executed correctly.");
    else
      $error("Test Case 1 Failed: R-type ADD instruction execution error. Expected 30, got %0d", ex_mem_reg_o.alu_result);

    // Test Case 2: I-type instruction (ADDI x5, x6, 10) - No bypass
    // x6 = 50. Expected result: x5 = 60
    $display("Test Case 2: I-type instruction (ADDI x5, x6, 10) - No bypass");
    id_ex_reg_i.pc = 32'h80000004;
    id_ex_reg_i.instr = 32'h00A30293; // ADDI x5, x6, 10
    id_ex_reg_i.op_code = OP_I_TYPE;
    id_ex_reg_i.funct3 = 3'b000;
    id_ex_reg_i.rd = 5;
    id_ex_reg_i.rs1 = 6;
    id_ex_reg_i.op1 = 50; // Value of x6
    id_ex_reg_i.imm = 10;
    id_ex_reg_i.ctrl_signals.alu_op = ALU_ADD;
    id_ex_reg_i.ctrl_signals.mem_read = MEM_NONE;
    id_ex_reg_i.ctrl_signals.mem_write = MEM_NONE;
    id_ex_reg_i.ctrl_signals.branch = BR_NONE;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    id_ex_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    id_ex_reg_i.ctrl_signals.pc_src = PC_PLUS_4;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (ex_mem_reg_o.alu_result == 60 &&
            ex_mem_reg_o.rd == 5 &&
            ex_mem_reg_o.ctrl_signals.reg_write == REG_WRITE_EN)
      $info("Test Case 2 Passed: I-type ADDI instruction executed correctly.");
    else
      $error("Test Case 2 Failed: I-type ADDI instruction execution error. Expected 60, got %0d", ex_mem_reg_o.alu_result);

    // Test Case 3: S-type instruction (SW x7, 0(x8)) - No bypass
    // x7 = 100, x8 = 0x1000. Expected: mem_addr = 0x1000, mem_write_data = 100
    $display("Test Case 3: S-type instruction (SW x7, 0(x8)) - No bypass");
    id_ex_reg_i.pc = 32'h80000008;
    id_ex_reg_i.instr = 32'h00742023; // SW x7, 0(x8)
    id_ex_reg_i.op_code = OP_S_TYPE;
    id_ex_reg_i.funct3 = 3'b010;
    id_ex_reg_i.rs1 = 8;
    id_ex_reg_i.rs2 = 7;
    id_ex_reg_i.op1 = 32'h1000; // Value of x8 (base address)
    id_ex_reg_i.op2 = 100;      // Value of x7 (data to write)
    id_ex_reg_i.imm = 0;
    id_ex_reg_i.ctrl_signals.alu_op = ALU_ADD; // ALU calculates address
    id_ex_reg_i.ctrl_signals.mem_read = MEM_NONE;
    id_ex_reg_i.ctrl_signals.mem_write = MEM_WORD;
    id_ex_reg_i.ctrl_signals.branch = BR_NONE;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_DIS;
    id_ex_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    id_ex_reg_i.ctrl_signals.pc_src = PC_PLUS_4;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (ex_mem_reg_o.alu_result == 32'h1000 && // Address
            ex_mem_reg_o.mem_write_data == 100 &&
            ex_mem_reg_o.ctrl_signals.mem_write == MEM_WORD)
      $info("Test Case 3 Passed: S-type SW instruction executed correctly.");
    else
      $error("Test Case 3 Failed: S-type SW instruction execution error. Addr: %0h, Data: %0d", ex_mem_reg_o.alu_result, ex_mem_reg_o.mem_write_data);

    // Test Case 4: B-type instruction (BEQ x9, x10, 0x10) - Branch Taken
    // x9 = 5, x10 = 5. Expected: branch_taken = 1, branch_target = pc + 16
    $display("Test Case 4: B-type instruction (BEQ x9, x10, 0x10) - Branch Taken");
    id_ex_reg_i.pc = 32'h8000000C;
    id_ex_reg_i.instr = 32'h00A48463; // BEQ x9, x10, 0x10
    id_ex_reg_i.op_code = OP_B_TYPE;
    id_ex_reg_i.funct3 = 3'b000;
    id_ex_reg_i.rs1 = 9;
    id_ex_reg_i.rs2 = 10;
    id_ex_reg_i.op1 = 5; // Value of x9
    id_ex_reg_i.op2 = 5; // Value of x10
    id_ex_reg_i.imm = 16;
    id_ex_reg_i.ctrl_signals.alu_op = ALU_SUB; // ALU performs comparison
    id_ex_reg_i.ctrl_signals.mem_read = MEM_NONE;
    id_ex_reg_i.ctrl_signals.mem_write = MEM_NONE;
    id_ex_reg_i.ctrl_signals.branch = BR_EQ;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_DIS;
    id_ex_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    id_ex_reg_i.ctrl_signals.pc_src = PC_BRANCH;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (ex_mem_reg_o.branch_taken == 1 &&
            ex_mem_reg_o.branch_target == (32'h8000000C + 16))
      $info("Test Case 4 Passed: B-type BEQ instruction (branch taken) executed correctly.");
    else
      $error("Test Case 4 Failed: B-type BEQ instruction (branch taken) execution error. Branch Taken: %0d, Target: %0h", ex_mem_reg_o.branch_taken, ex_mem_reg_o.branch_target);

    // Test Case 5: DPU FPU instruction (FPU_ADD) - ENABLE_FPU = 1
    // Assuming FPU_ADD adds op1 and op2. op1 = 1.5, op2 = 2.5. Expected: 4.0
    // Note: For floating point, actual values will be bit patterns.
    // This test assumes a simple pass-through for DPU for now, as FPU unit is separate.
    // The execute stage should correctly route to DPU and handle stall/flush from DPU.
    $display("Test Case 5: DPU FPU instruction (FPU_ADD)");
    id_ex_reg_i.pc = 32'h80000010;
    id_ex_reg_i.instr = {7'b0000000, 5'd0, 5'd0, FUNCT3_DPU_FPU, 5'd0, OPCODE_CUSTOM0}; // Example FPU_ADD
    id_ex_reg_i.op_code = OP_CUSTOM0;
    id_ex_reg_i.funct3 = FUNCT3_DPU_FPU;
    id_ex_reg_i.rd = 1;
    id_ex_reg_i.op1 = 32'h3fc00000; // 1.5 (IEEE 754 single precision)
    id_ex_reg_i.op2 = 32'h40200000; // 2.5 (IEEE 754 single precision)
    id_ex_reg_i.ctrl_signals.alu_op = ALU_DPU;
    id_ex_reg_i.ctrl_signals.mem_read = MEM_NONE;
    id_ex_reg_i.ctrl_signals.mem_write = MEM_NONE;
    id_ex_reg_i.ctrl_signals.branch = BR_NONE;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    id_ex_reg_i.ctrl_signals.mem_to_reg = WB_SEL_DPU;
    id_ex_reg_i.ctrl_signals.pc_src = PC_PLUS_4;
    @(posedge clk); #1;
    @(posedge clk); #1;
    // Assuming DPU result is passed through alu_result for simplicity in this testbench
    // In a real scenario, the DPU unit would produce the result.
    // For this test, we'll check if the DPU path is correctly activated.
    // The actual FPU calculation is done in fpu_unit.sv, this stage just routes.
    // We can't assert the exact floating point result here without a reference model.
    // Instead, we'll check if the DPU related control signals are propagated.
    assert (ex_mem_reg_o.ctrl_signals.mem_to_reg == WB_SEL_DPU &&
            ex_mem_reg_o.ctrl_signals.reg_write == REG_WRITE_EN)
      $info("Test Case 5 Passed: DPU FPU instruction correctly handled by execute stage.");
    else
      $error("Test Case 5 Failed: DPU FPU instruction handling error.");

    // Test Case 6: Flush signal active
    $display("Test Case 6: Flush signal active");
    id_ex_reg_i.pc = 32'h80000014;
    id_ex_reg_i.instr = 32'h00000013; // NOP
    id_ex_reg_i.op_code = OP_R_TYPE;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    flush_i = 1;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (ex_mem_valid_o == 0 && ex_flush_o == 1)
      $info("Test Case 6 Passed: Flush signal correctly invalidates pipeline register and propagates flush.");
    else
      $error("Test Case 6 Failed: Flush signal handling error. ex_mem_valid_o: %0d, ex_flush_o: %0d", ex_mem_valid_o, ex_flush_o);
    flush_i = 0; // De-assert flush

    // Test Case 7: Stall signal active
    $display("Test Case 7: Stall signal active");
    id_ex_reg_i.pc = 32'h80000018;
    id_ex_reg_i.instr = 32'h00000013; // NOP
    id_ex_reg_i.op_code = OP_R_TYPE;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    stall_i = 1;
    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (ex_mem_valid_o == 0 && ex_stall_o == 1) // Assuming stall prevents new valid output and propagates stall
      $info("Test Case 7 Passed: Stall signal correctly prevents new valid output and propagates stall.");
    else
      $error("Test Case 7 Failed: Stall signal handling error. ex_mem_valid_o: %0d, ex_stall_o: %0d", ex_mem_valid_o, ex_stall_o);
    stall_i = 0; // De-assert stall

    // Test Case 8: Data Bypass from Memory Stage
    // ADD x1, x2, x3. x2 = 10. x3 is result from MEM stage (30). Expected: x1 = 40
    $display("Test Case 8: Data Bypass from Memory Stage");
    id_ex_reg_i.pc = 32'h80000020;
    id_ex_reg_i.instr = 32'h003100B3; // ADD x1, x2, x3
    id_ex_reg_i.op_code = OP_R_TYPE;
    id_ex_reg_i.funct3 = 3'b000;
    id_ex_reg_i.funct7 = 7'b0000000;
    id_ex_reg_i.rd = 1;
    id_ex_reg_i.rs1 = 2;
    id_ex_reg_i.rs2 = 3;
    id_ex_reg_i.op1 = 10; // Value of x2
    id_ex_reg_i.op2 = 0;  // Will be bypassed
    id_ex_reg_i.ctrl_signals.alu_op = ALU_ADD;
    id_ex_reg_i.ctrl_signals.mem_read = MEM_NONE;
    id_ex_reg_i.ctrl_signals.mem_write = MEM_NONE;
    id_ex_reg_i.ctrl_signals.branch = BR_NONE;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    id_ex_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    id_ex_reg_i.ctrl_signals.pc_src = PC_PLUS_4;

    mem_rd_addr_i = 3; // x3 is being written by MEM stage
    mem_reg_write_en_i = 1;
    mem_result_i = 30; // Value of x3 from MEM stage

    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (ex_mem_reg_o.alu_result == 40 &&
            ex_mem_reg_o.rd == 1 &&
            ex_mem_reg_o.ctrl_signals.reg_write == REG_WRITE_EN)
      $info("Test Case 8 Passed: Data bypass from Memory stage successful. Expected 40, got %0d", ex_mem_reg_o.alu_result);
    else
      $error("Test Case 8 Failed: Data bypass from Memory stage error. Expected 40, got %0d", ex_mem_reg_o.alu_result);

    // Test Case 9: Data Bypass from Writeback Stage
    // ADD x1, x2, x3. x2 = 10. x3 is result from WB stage (30). Expected: x1 = 40
    $display("Test Case 9: Data Bypass from Writeback Stage");
    id_ex_reg_i.pc = 32'h80000024;
    id_ex_reg_i.instr = 32'h003100B3; // ADD x1, x2, x3
    id_ex_reg_i.op_code = OP_R_TYPE;
    id_ex_reg_i.funct3 = 3'b000;
    id_ex_reg_i.funct7 = 7'b0000000;
    id_ex_reg_i.rd = 1;
    id_ex_reg_i.rs1 = 2;
    id_ex_reg_i.rs2 = 3;
    id_ex_reg_i.op1 = 10; // Value of x2
    id_ex_reg_i.op2 = 0;  // Will be bypassed
    id_ex_reg_i.ctrl_signals.alu_op = ALU_ADD;
    id_ex_reg_i.ctrl_signals.mem_read = MEM_NONE;
    id_ex_reg_i.ctrl_signals.mem_write = MEM_NONE;
    id_ex_reg_i.ctrl_signals.branch = BR_NONE;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_EN;
    id_ex_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    id_ex_reg_i.ctrl_signals.pc_src = PC_PLUS_4;

    mem_reg_write_en_i = 0; // No bypass from MEM
    wb_rd_addr_i = 3; // x3 is being written by WB stage
    wb_reg_write_en_i = 1;
    wb_result_i = 30; // Value of x3 from WB stage

    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (ex_mem_reg_o.alu_result == 40 &&
            ex_mem_reg_o.rd == 1 &&
            ex_mem_reg_o.ctrl_signals.reg_write == REG_WRITE_EN)
      $info("Test Case 9 Passed: Data bypass from Writeback stage successful. Expected 40, got %0d", ex_mem_reg_o.alu_result);
    else
      $error("Test Case 9 Failed: Data bypass from Writeback stage error. Expected 40, got %0d", ex_mem_reg_o.alu_result);

    // Test Case 10: Illegal Instruction Exception
    $display("Test Case 10: Illegal Instruction Exception");
    id_ex_reg_i.pc = 32'h80000028;
    id_ex_reg_i.instr = 32'hFFFFFFFF; // Illegal instruction
    id_ex_reg_i.op_code = OP_ILLEGAL;
    id_ex_reg_i.ctrl_signals.alu_op = ALU_ADD; // Doesn't matter for illegal
    id_ex_reg_i.ctrl_signals.mem_read = MEM_NONE;
    id_ex_reg_i.ctrl_signals.mem_write = MEM_NONE;
    id_ex_reg_i.ctrl_signals.branch = BR_NONE;
    id_ex_reg_i.ctrl_signals.reg_write = REG_WRITE_DIS;
    id_ex_reg_i.ctrl_signals.mem_to_reg = WB_SEL_ALU;
    id_ex_reg_i.ctrl_signals.pc_src = PC_PLUS_4;

    mem_reg_write_en_i = 0;
    wb_reg_write_en_i = 0;

    @(posedge clk); #1;
    @(posedge clk); #1;
    assert (ex_mem_reg_o.exception_en == 1 &&
            ex_mem_reg_o.exception_code == EXC_ILLEGAL_INSTR)
      $info("Test Case 10 Passed: Illegal Instruction Exception generated correctly.");
    else
      $error("Test Case 10 Failed: Illegal Instruction Exception error. Exception_en: %0d, Exception_code: %0d", ex_mem_reg_o.exception_en, ex_mem_reg_o.exception_code);

    $display("--------------------------------------------------");
    $display("Execute Stage Testbench Finished");
    $display("--------------------------------------------------");
    test_done = 1;
  end

  // Simulation Control
  always @(test_done) begin
    if (test_done) begin
      $finish;
    end
  end

endmodule : execute_stage_tb
//=============================================================================
// Dependencies:
//   - rtl/core/execute_stage.sv
//   - rtl/pkg/riscv_config_pkg.sv
//   - rtl/pkg/riscv_core_pkg.sv
//   - rtl/pkg/riscv_dpu_types_pkg.sv
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
//   - Testbench: execute_stage_tb.sv
//   - Test Vectors: See execute_stage_tb_testcases.md
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | Juan.Kok           | Initial release
//=============================================================================
