//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
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
//   A dedicated multi-cycle division unit for the RISC-V core. It implements
//   the RV32M standard extension instructions (DIV, DIVU, REM, REMU). It uses
//   a registered, pipelined approach for high performance and handles division
//   by zero and overflow conditions according to the RISC-V specification.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module div_unit
    import riscv_core_pkg::*;
#(
    // AI_TAG: PARAMETER - LATENCY - Defines the number of cycles to compute the result.
    // Division typically takes more cycles than multiplication. A latency of 32
    // is common for a simple restoring division algorithm.
    parameter integer LATENCY = 32
)
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // AI_TAG: PORT_DESC - start_i - A single-cycle pulse from Execute to begin a division.
    input  logic        start_i,
    // AI_TAG: PORT_DESC - operand_a_i, operand_b_i - The 32-bit input operands (dividend, divisor).
    input  word_t       operand_a_i,
    input  word_t       operand_b_i,
    // AI_TAG: PORT_DESC - op_type_i - Selects the division type (funct3-derived).
    input  logic [2:0]  op_type_i,

    // AI_TAG: PORT_DESC - result_o - The 32-bit result of the operation.
    output word_t       result_o,
    // AI_TAG: PORT_DESC - done_o - Asserts high when the calculation is complete and the result is valid.
    output logic        done_o
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
    assign signed_overflow = (operand_a_q == 32'h80000000) && (operand_b_q == 32'hFFFFFFFF);

    // AI_TAG: INTERNAL_LOGIC - Determine if we need to use default result
    assign use_default_result = div_by_zero || signed_overflow;

    // AI_TAG: INTERNAL_LOGIC - Core Division Operations
    // Using SystemVerilog division operators. Synthesis tools will infer
    // appropriate division hardware (e.g., restoring division, SRT division).
    assign div_result_signed   = $signed(operand_a_q) / $signed(operand_b_q);
    assign div_result_unsigned = operand_a_q / operand_b_q;
    assign rem_result_signed   = $signed(operand_a_q) % $signed(operand_b_q);
    assign rem_result_unsigned = operand_a_q % operand_b_q;

    // AI_TAG: INTERNAL_LOGIC - Result Selection Mux with Exception Handling
    // This combinational logic selects the correct result based on the operation type
    // and handles division by zero and overflow conditions according to RISC-V spec.
    always_comb begin
        // Default assignment helps prevent latches in case of invalid op_type.
        result_o = div_result_signed; // Default to signed division result

        if (use_default_result) begin
            // AI_TAG: RISC-V_SPEC - Division by zero and overflow handling
            // According to RISC-V spec:
            // - DIV/REM with divisor=0: result = -1 (DIV) or dividend (REM)
            // - DIV with overflow: result = dividend
            // - REM with overflow: result = 0
            case (op_type_q)
                OP_TYPE_DIV:  result_o = signed_overflow ? operand_a_q : 32'hFFFFFFFF; // -1 for div by zero, dividend for overflow
                OP_TYPE_DIVU: result_o = 32'hFFFFFFFF; // -1 for div by zero
                OP_TYPE_REM:  result_o = signed_overflow ? 32'h0 : operand_a_q; // 0 for overflow, dividend for div by zero
                OP_TYPE_REMU: result_o = operand_a_q; // dividend for div by zero
                default:      result_o = div_result_signed;
            endcase
        end else begin
            // Normal division operations
            case (op_type_q)
                OP_TYPE_DIV:  result_o = div_result_signed;
                OP_TYPE_DIVU: result_o = div_result_unsigned;
                OP_TYPE_REM:  result_o = rem_result_signed;
                OP_TYPE_REMU: result_o = rem_result_unsigned;
                default:      result_o = div_result_signed;
            endcase
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Done Signal Generation
    // This shift register pipeline creates a delayed 'done' signal. When start_i
    // is asserted, a '1' enters the pipeline. When it emerges after LATENCY cycles,
    // the 'done_o' signal is asserted.
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            busy_q <= '0;
        end else begin
            busy_q <= {busy_q[LATENCY-2:0], start_i};
        end
    end

    // The result is 'done' when the start signal has reached the end of the latency pipeline.
    assign done_o = busy_q[LATENCY-1];

    // AI_TAG: SVA - Check for valid operation types
    // Description: Ensures that only valid RV32M division operation types are used.
`ifndef SYNTHESIS
    property p_valid_div_op_type;
        @(posedge clk_i)
        disable iff(!rst_ni)
        (start_i) |-> (op_type_i inside {OP_TYPE_DIV, OP_TYPE_DIVU, OP_TYPE_REM, OP_TYPE_REMU});
    endproperty

    a_valid_div_op_type: assert property (p_valid_div_op_type) else
        $error("Assertion failed: Invalid division operation type detected.");
`endif

endmodule : div_unit

//=============================================================================
// Dependencies: riscv_core_pkg.sv
//
// Performance:
//   - Critical Path: Division operation to result output
//   - Max Frequency: TBD
//   - Area: TBD
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
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//============================================================================= 