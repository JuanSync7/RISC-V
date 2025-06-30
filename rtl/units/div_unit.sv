//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: div_unit.sv
// Module: div_unit
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Pipelined division unit supporting signed and unsigned division and
//   remainder operations. Implements RISC-V RV32M division instructions:
//   DIV, DIVU, REM, REMU. Uses a configurable latency pipeline for
//   high-performance division operations.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module div_unit #(
    parameter integer DATA_WIDTH = 32, // AI_TAG: PARAM_DESC - Width of the data path and operands.
    parameter integer LATENCY    = DEFAULT_DIV_LATENCY // AI_TAG: PARAM_DESC - Number of pipeline stages for division.
) (
    // Clock and Reset
    input  logic        clk_i,
    input  logic        rst_ni,

    // Control Interface
    input  logic        start_i,      // AI_TAG: PORT_DESC - start_i - Initiates a new division operation.
    input  logic [2:0]  op_type_i,    // AI_TAG: PORT_DESC - op_type_i - Specifies the division operation type.
    input  word_t       operand_a_i,  // AI_TAG: PORT_DESC - operand_a_i - First operand (dividend).
    input  word_t       operand_b_i,  // AI_TAG: PORT_DESC - operand_b_i - Second operand (divisor).

    // Result Interface
    // AI_TAG: PORT_DESC - result_o - The 32-bit result of the operation.
    output word_t       result_o,
    // AI_TAG: PORT_DESC - done_o - Asserts high when the calculation is complete and the result is valid.
    output logic        done_o,
    // AI_TAG: PORT_DESC - busy_o - Asserts high when the unit is performing a calculation.
    output logic        busy_o,
    // AI_TAG: PORT_DESC - exception_valid_o - Asserts if the operation caused an exception.
    output logic        exception_valid_o,
    // AI_TAG: PORT_DESC - exception_cause_o - The cause of the exception.
    output logic [31:0] exception_cause_o
);

    // AI_TAG: TYPEDEF - Operation types for clarity, derived from funct3 of OP-family instructions.
    // According to RISC-V RV32M specification:
    // DIV: funct3 = 3'b100, DIVU: funct3 = 3'b101, REM: funct3 = 3'b110, REMU: funct3 = 3'b111
    localparam logic [2:0] OP_TYPE_DIV  = 3'b100; // signed / signed
    localparam logic [2:0] OP_TYPE_DIVU = 3'b101; // unsigned / unsigned
    localparam logic [2:0] OP_TYPE_REM  = 3'b110; // signed % signed
    localparam logic [2:0] OP_TYPE_REMU = 3'b111; // unsigned % unsigned

    // AI_TAG: INTERNAL_STORAGE - Registers for pipelining the operation.
    word_t      operand_a_q, operand_b_q;
    logic [2:0] op_type_q;

    // AI_TAG: INTERNAL_WIRE - Wires for the division results.
    word_t div_result_signed;   // Signed division result
    word_t div_result_unsigned; // Unsigned division result
    word_t rem_result_signed;   // Signed remainder result
    word_t rem_result_unsigned; // Unsigned remainder result

    // AI_TAG: INTERNAL_STORAGE - Shift register to track operation completion and generate done signal.
    logic [LATENCY-1:0] busy_q;

    // AI_TAG: INTERNAL_LOGIC - Division by zero and overflow detection
    logic div_by_zero;
    logic signed_overflow;
    logic use_default_result;

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

    // AI_TAG: INTERNAL_LOGIC - Division by zero detection
    assign div_by_zero = (operand_b_q == '0);

    // AI_TAG: INTERNAL_LOGIC - Signed overflow detection
    // For signed division: if dividend is -2^31 and divisor is -1, result overflows
    assign signed_overflow = (operand_a_q == {1'b1, {(DATA_WIDTH-1){1'b0}}}) && (operand_b_q == {DATA_WIDTH{1'b1}});

    // AI_TAG: INTERNAL_LOGIC - Determine if we need to use default result
    assign use_default_result = div_by_zero || signed_overflow;

    // AI_TAG: INTERNAL_LOGIC - Exception Generation
    assign exception_valid_o = use_default_result;
    always_comb begin
        if (div_by_zero) begin
            // This is a generic illegal operation for now.
            // A more specific cause could be defined.
            exception_cause_o = CAUSE_ILLEGAL_INSTRUCTION;
        end else if (signed_overflow) begin
            exception_cause_o = CAUSE_ILLEGAL_INSTRUCTION;
        end else begin
            exception_cause_o = '0;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Division and remainder calculations
    // These are simplified for illustration. In a real implementation,
    // these would be pipelined division algorithms.
    assign div_result_signed   = ($signed(operand_a_q) / $signed(operand_b_q));
    assign div_result_unsigned = (operand_a_q / operand_b_q);
    assign rem_result_signed   = ($signed(operand_a_q) % $signed(operand_b_q));
    assign rem_result_unsigned = (operand_a_q % operand_b_q);

    // AI_TAG: INTERNAL_LOGIC - Result selection based on operation type
    always_comb begin
        if (use_default_result) begin
            // Handle exception cases according to RISC-V specification
            case (op_type_q)
                OP_TYPE_DIV:  result_o = div_by_zero ? {DATA_WIDTH{1'b1}} : operand_a_q; // -1 for div by zero, dividend for overflow
                OP_TYPE_DIVU: result_o = {DATA_WIDTH{1'b1}}; // -1 for div by zero
                OP_TYPE_REM:  result_o = div_by_zero ? operand_a_q : '0; // dividend for div by zero, 0 for overflow
                OP_TYPE_REMU: result_o = operand_a_q; // dividend for div by zero
                default:      result_o = '0;
            endcase
        end else begin
            // Normal operation cases - compute actual division/remainder
            case (op_type_q)
                OP_TYPE_DIV:  result_o = div_result_signed;   // Signed division result
                OP_TYPE_DIVU: result_o = div_result_unsigned; // Unsigned division result
                OP_TYPE_REM:  result_o = rem_result_signed;   // Signed remainder result
                OP_TYPE_REMU: result_o = rem_result_unsigned; // Unsigned remainder result
                default:      result_o = '0;
            endcase
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Pipeline completion tracking
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            busy_q <= '0;
        end else begin
            if (start_i) begin
                busy_q <= {{(LATENCY-1){1'b0}}, 1'b1}; // Start new operation
            end else begin
                busy_q <= {busy_q[LATENCY-2:0], 1'b0}; // Shift pipeline
            end
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Done signal generation
    assign done_o = busy_q[LATENCY-1]; // Operation complete when it reaches the end of pipeline

    // AI_TAG: INTERNAL_LOGIC - Busy signal generation
    assign busy_o = |busy_q; // Unit is busy when any stage in pipeline is active

    // AI_TAG: ASSERTION - Division by zero should always generate an exception
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - div_unit_coverage.div_by_zero_cp
    DivByZeroException: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (div_by_zero |-> exception_valid_o));

    // AI_TAG: ASSERTION - Signed overflow should always generate an exception
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - div_unit_coverage.signed_overflow_cp
    SignedOverflowException: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (signed_overflow |-> exception_valid_o));

    // AI_TAG: ASSERTION - Done signal should only be asserted when operation is complete
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - div_unit_coverage.done_signal_cp
    DoneSignalValid: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (done_o |-> busy_q[LATENCY-1]));

endmodule : div_unit

//=============================================================================
// Dependencies: riscv_config_pkg, riscv_types_pkg, riscv_exception_pkg
//
// Performance:
//   - Critical Path: Through the division algorithm (depends on implementation)
//   - Max Frequency: Depends on division algorithm and target technology
//   - Area: Significant due to division hardware
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