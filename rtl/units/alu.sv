//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: alu.sv
// Module: alu
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Arithmetic Logic Unit (ALU) for the RISC-V core. This is a purely
//   combinational module that performs all integer arithmetic, logical,
//   and shift operations as defined by the RV32I base instruction set.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module alu #(
) (
    // AI_TAG: PORT_DESC - alu_op_i - Control signal selecting the ALU operation to perform.
    input  alu_op_e alu_op_i,
    // AI_TAG: PORT_DESC - operand_a_i - First 32-bit data operand (e.g., from rs1 or PC).
    input  word_t   operand_a_i,
    // AI_TAG: PORT_DESC - operand_b_i - Second 32-bit data operand (e.g., from rs2 or immediate).
    input  word_t   operand_b_i,

    // AI_TAG: PORT_DESC - alu_result_o - 32-bit result of the ALU operation.
    output word_t   alu_result_o,
    // AI_TAG: PORT_DESC - zero_o - Flag that is asserted if the ALU result is zero. Used for branch evaluation.
    output logic    zero_o,
    // AI_TAG: PORT_DESC - overflow_o - Flag that is asserted when arithmetic operations overflow. Used for exception handling.
    output logic    overflow_o
);

    logic [XLEN-1:0] alu_result;
    logic add_overflow, sub_overflow;

    // AI_TAG: INTERNAL_LOGIC - Main ALU combinational logic.
    // Description: A case statement selects the operation based on alu_op_i.
    // This block calculates the result of the operation.
    always_comb begin
        // Default assignment to prevent latches and propagate unknowns.
        alu_result = 'x;

        case (alu_op_i)
            ALU_OP_ADD:  alu_result = operand_a_i + operand_b_i;
            ALU_OP_SUB:  alu_result = operand_a_i - operand_b_i;
            ALU_OP_XOR:  alu_result = operand_a_i ^ operand_b_i;
            ALU_OP_OR:   alu_result = operand_a_i | operand_b_i;
            ALU_OP_AND:  alu_result = operand_a_i & operand_b_i;
            // AI_TAG: SYNTHESIS_NOTE - The RISC-V ISA specifies that for XLEN=32, only the
            // lower 5 bits of the shift amount operand are used.
            ALU_OP_SLL:  alu_result = operand_a_i << operand_b_i[4:0];
            ALU_OP_SRL:  alu_result = operand_a_i >> operand_b_i[4:0];
            // AI_TAG: SYNTHESIS_NOTE - The `>>>` operator performs a signed arithmetic right shift.
            ALU_OP_SRA:  alu_result = $signed(operand_a_i) >>> operand_b_i[4:0];
            ALU_OP_SLT:  alu_result = ($signed(operand_a_i) < $signed(operand_b_i)) ? 32'd1 : 32'd0;
            ALU_OP_SLTU: alu_result = (operand_a_i < operand_b_i) ? 32'd1 : 32'd0;
            ALU_OP_LUI:  alu_result = operand_b_i; // For LUI, the immediate is passed through operand_b
            ALU_OP_COPY_A: alu_result = operand_a_i; // For JALR address calculation
            ALU_OP_COPY_B: alu_result = operand_b_i; // For Load/Store address calculation
            default:     alu_result = 'x;
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Overflow Detection Logic.
    // Description: Detects arithmetic overflow for ADD and SUB operations.
    // Overflow occurs when:
    // - ADD: Adding two positive numbers produces a negative result, or
    //        adding two negative numbers produces a positive result
    // - SUB: Subtracting a negative number from a positive number produces a negative result, or
    //        subtracting a positive number from a negative number produces a positive result
    always_comb begin
        add_overflow = 1'b0;
        sub_overflow = 1'b0;
        
        if (alu_op_i == ALU_OP_ADD) begin
            // Overflow occurs when adding two numbers of the same sign produces a result of opposite sign
            add_overflow = (operand_a_i[XLEN-1] == operand_b_i[XLEN-1]) && 
                          (alu_result[XLEN-1] != operand_a_i[XLEN-1]);
        end else if (alu_op_i == ALU_OP_SUB) begin
            // Overflow occurs when subtracting numbers of opposite signs produces a result of the same sign as the subtrahend
            sub_overflow = (operand_a_i[XLEN-1] != operand_b_i[XLEN-1]) && 
                          (alu_result[XLEN-1] == operand_b_i[XLEN-1]);
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Zero Flag Generation.
    // Description: Combinatorially asserts 'zero_o' if the ALU result is zero.
    // The result of a SUB operation is used to evaluate branch conditions (e.g., BEQ).
    assign alu_result_o = alu_result;
    assign zero_o       = (alu_result == '0);
    assign overflow_o   = add_overflow || sub_overflow;

endmodule : alu

//=============================================================================
// Dependencies: riscv_core_pkg.sv
// Instantiated In:
//   - rtl/core/pipeline/execute_stage.sv
//
// Performance:
//   - Critical Path: ALU operation to result output
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
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//=============================================================================

`default_nettype wire