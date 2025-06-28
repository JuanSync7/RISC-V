//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
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
//   A dedicated multi-cycle multiplication unit for the RISC-V core. It
//   implements the RV32M standard extension instructions (MUL, MULH, MULHSU,
//   MULHU). It uses a registered, pipelined approach for high performance.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module mult_unit
    import riscv_core_pkg::*;
#(
    // AI_TAG: PARAMETER - LATENCY - Defines the number of cycles to compute the result.
    // A latency of 2 means the result is available 2 cycles after start is asserted.
    parameter integer LATENCY = 2
)
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // AI_TAG: PORT_DESC - start_i - A single-cycle pulse from Execute to begin a multiplication.
    input  logic        start_i,
    // AI_TAG: PORT_DESC - operand_a_i, operand_b_i - The 32-bit input operands.
    input  word_t       operand_a_i,
    input  word_t       operand_b_i,
    // AI_TAG: PORT_DESC - op_type_i - Selects the multiplication type (funct3-derived).
    input  logic [2:0]  op_type_i,

    // AI_TAG: PORT_DESC - result_o - The 32-bit result of the operation.
    output word_t       result_o,
    // AI_TAG: PORT_DESC - done_o - Asserts high when the calculation is complete and the result is valid.
    output logic        done_o
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

    // AI_TAG: INTERNAL_LOGIC - Core Multiplication Operations
    // Three parallel multiplications are described. A smart synthesis tool may be able
    // to share resources between them. This explicit style is clear and verifiable.
    assign product_ss = $signed(operand_a_q) * $signed(operand_b_q);
    assign product_su = $signed(operand_a_q) * operand_b_q;
    assign product_uu = operand_a_q * operand_b_q;

    // AI_TAG: INTERNAL_LOGIC - Result Selection Mux
    // This combinational logic selects the correct 32-bit portion of the correct
    // 64-bit product based on the latched operation type.
    always_comb begin
        // Default assignment helps prevent latches in case of invalid op_type.
        result_o = product_ss[31:0]; // Default to MUL result

        case (op_type_q)
            OP_TYPE_MUL:    result_o = product_ss[31:0];  // MUL result (lower 32 bits of signed*signed)
            OP_TYPE_MULH:   result_o = product_ss[63:32]; // MULH result (upper 32 bits of signed*signed)
            OP_TYPE_MULHSU: result_o = product_su[63:32]; // MULHSU result (upper 32 bits of signed*unsigned)
            OP_TYPE_MULHU:  result_o = product_uu[63:32]; // MULHU result (upper 32 bits of unsigned*unsigned)
            default:        result_o = product_ss[31:0];  // MUL result (default case)
        endcase
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


endmodule : mult_unit

//=============================================================================
// Dependencies: riscv_core_pkg.sv
//
// Performance:
//   - Critical Path: Multiplier to result output
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
// 1.1.0   | 2025-06-28 | DesignAI           | Fixed operation type mapping to correctly match RISC-V RV32M specification
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//=============================================================================