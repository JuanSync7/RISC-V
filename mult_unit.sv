////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-28
// Design Name:   RV32IM Core
// Module Name:   mult_unit
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   A dedicated multi-cycle multiplication unit for the RISC-V
//                core. It implements the RV32M standard extension instructions
//                (MUL, MULH, MULHSU, MULHU). It uses a registered, pipelined
//                approach for high performance.
//
// Dependencies:  riscv_core_pkg.sv
//
// Revision:
// Revision 1.0.0 - File Created
//
////////////////////////////////////////////////////////////////////////////////

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
    input  logic [1:0]  op_type_i,

    // AI_TAG: PORT_DESC - result_o - The 32-bit result of the operation.
    output word_t       result_o,
    // AI_TAG: PORT_DESC - done_o - Asserts high when the calculation is complete and the result is valid.
    output logic        done_o
);

    // AI_TAG: TYPEDEF - Operation types for clarity, derived from funct3[1:0] of OP-family instructions.
    localparam logic [1:0] OP_TYPE_MULH   = 2'b00; // signed * signed, upper
    localparam logic [1:0] OP_TYPE_MULHSU = 2'b01; // signed * unsigned, upper
    localparam logic [1:0] OP_TYPE_MULHU  = 2'b10; // unsigned * unsigned, upper
    // Note: MUL uses the same calculation as MULH but takes the lower 32 bits.

    // AI_TAG: INTERNAL_STORAGE - Registers for pipelining the operation.
    word_t      operand_a_q, operand_b_q;
    logic [1:0] op_type_q;

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
            OP_TYPE_MULH:   result_o = product_ss[63:32]; // MULH result
            OP_TYPE_MULHSU: result_o = product_su[63:32]; // MULHSU result
            OP_TYPE_MULHU:  result_o = product_uu[63:32]; // MULHU result
            default:        result_o = product_ss[31:0];  // MUL result
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