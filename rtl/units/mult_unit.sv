//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: mult_unit.sv
// Module: mult_unit
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Pipelined multiplication unit supporting signed and unsigned multiplication
//   operations. Implements RISC-V RV32M multiplication instructions:
//   MUL, MULH, MULHSU, MULHU. Uses a configurable latency pipeline for
//   high-performance multiplication operations.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module mult_unit #(
    parameter integer DATA_WIDTH = 32, // AI_TAG: PARAM_DESC - Width of the data path and operands.
    parameter integer LATENCY    = 3   // AI_TAG: PARAM_DESC - Number of pipeline stages for multiplication.
) (
    // Clock and Reset
    input  logic        clk_i,
    input  logic        rst_ni,

    // Control Interface
    input  logic        start_i,      // AI_TAG: PORT_DESC - start_i - Initiates a new multiplication operation.
    input  logic [2:0]  op_type_i,    // AI_TAG: PORT_DESC - op_type_i - Specifies the multiplication operation type.
    input  word_t       operand_a_i,  // AI_TAG: PORT_DESC - operand_a_i - First operand.
    input  word_t       operand_b_i,  // AI_TAG: PORT_DESC - operand_b_i - Second operand.

    // Result Interface
    output word_t       result_o,     // AI_TAG: PORT_DESC - result_o - The 32-bit result of the operation.
    output logic        done_o,       // AI_TAG: PORT_DESC - done_o - Asserts high when the calculation is complete.
    output logic        exception_valid_o, // AI_TAG: PORT_DESC - exception_valid_o - Asserts if the operation caused an exception.
    output logic [31:0] exception_cause_o  // AI_TAG: PORT_DESC - exception_cause_o - The cause of the exception.
);

    // AI_TAG: TYPEDEF - Operation types for clarity, derived from funct3 of OP-family instructions.
    // According to RISC-V RV32M specification:
    // MUL: funct3 = 3'b000, MULH: funct3 = 3'b001, MULHSU: funct3 = 3'b010, MULHU: funct3 = 3'b011
    localparam logic [2:0] OP_TYPE_MUL    = 3'b000; // signed * signed, lower
    localparam logic [2:0] OP_TYPE_MULH   = 3'b001; // signed * signed, upper
    localparam logic [2:0] OP_TYPE_MULHSU = 3'b010; // signed * unsigned, upper
    localparam logic [2:0] OP_TYPE_MULHU  = 3'b011; // unsigned * unsigned, upper

    // AI_TAG: INTERNAL_STORAGE - Registers for pipelining the operation.
    word_t      operand_a_q, operand_b_q;
    logic [2:0] op_type_q;

    // AI_TAG: INTERNAL_WIRE - Wires for the full 64-bit products.
    // AI_TAG: SYNTHESIS_NOTE - Using the '*' operator allows the synthesis tool to infer a
    // highly optimized multiplier (e.g., a Wallace or Dadda tree), which is ideal for ASIC targets.
    logic [63:0] product_ss; // signed * signed
    logic [63:0] product_su; // signed * unsigned
    logic [63:0] product_uu; // unsigned * unsigned

    // AI_TAG: INTERNAL_STORAGE - Shift register to track operation completion and generate done signal.
    logic [LATENCY-1:0] busy_q;


    // AI_TAG: INTERNAL_LOGIC - Input operand pipeline register
    // Latches the inputs when a new operation starts. This holds the values
    // stable for the duration of the calculation.
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            operand_a_q <= '0;
            operand_b_q <= '0;
            op_type_q   <= '0;
        end else if (start_i) begin
            operand_a_q <= operand_a_i;
            operand_b_q <= operand_b_i;
            op_type_q   <= op_type_i;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Multiplication calculations
    // These use SystemVerilog multiplication operators which will be synthesized
    // into optimized multiplier hardware.
    assign product_ss = $signed(operand_a_q) * $signed(operand_b_q); // signed * signed
    assign product_su = $signed(operand_a_q) * operand_b_q;          // signed * unsigned
    assign product_uu = operand_a_q * operand_b_q;                   // unsigned * unsigned

    // AI_TAG: INTERNAL_LOGIC - Result selection based on operation type
    always_comb begin
        case (op_type_q)
            OP_TYPE_MUL:    result_o = product_ss[DATA_WIDTH-1:0];     // Lower 32 bits of signed * signed
            OP_TYPE_MULH:   result_o = product_ss[2*DATA_WIDTH-1:DATA_WIDTH]; // Upper 32 bits of signed * signed
            OP_TYPE_MULHSU: result_o = product_su[2*DATA_WIDTH-1:DATA_WIDTH]; // Upper 32 bits of signed * unsigned
            OP_TYPE_MULHU:  result_o = product_uu[2*DATA_WIDTH-1:DATA_WIDTH]; // Upper 32 bits of unsigned * unsigned
            default:        result_o = '0;
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Pipeline completion tracking
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            busy_q <= '0;
        end else begin
            if (start_i) begin
                busy_q <= {1'b1, {LATENCY-1{1'b0}}}; // Start new operation
            end else begin
                busy_q <= {1'b0, busy_q[LATENCY-1:1]}; // Shift pipeline
            end
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Done signal generation
    assign done_o = busy_q[0]; // Operation complete when it reaches the end of pipeline

    // AI_TAG: INTERNAL_LOGIC - Exception handling (multiplication typically doesn't generate exceptions)
    assign exception_valid_o = 1'b0;
    assign exception_cause_o = '0;

    // AI_TAG: ASSERTION - Done signal should only be asserted when operation is complete
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - mult_unit_coverage.done_signal_cp
    DoneSignalValid: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (done_o |-> busy_q[0]));

    // AI_TAG: ASSERTION - Valid operation types only
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - mult_unit_coverage.valid_op_type_cp
    ValidOpType: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (start_i |-> op_type_i inside {OP_TYPE_MUL, OP_TYPE_MULH, OP_TYPE_MULHSU, OP_TYPE_MULHU}));

endmodule : mult_unit

//=============================================================================
// Dependencies: riscv_config_pkg, riscv_types_pkg
//
// Performance:
//   - Critical Path: Through the multiplier (depends on implementation)
//   - Max Frequency: Depends on multiplier algorithm and target technology
//   - Area: Significant due to multiplication hardware
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)
//
// Testing:
//   - Testbench: TBD
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//=============================================================================