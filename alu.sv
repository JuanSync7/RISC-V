////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-27
// Design Name:   RV32IM Core
// Module Name:   alu
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   Arithmetic Logic Unit (ALU) for the RISC-V core.
//                This is a purely combinational module that performs all
//                integer arithmetic, logical, and shift operations as
//                defined by the RV32I base instruction set.
//
// Dependencies:  riscv_core_pkg.sv
//
// Revision:
// Revision 1.0.0 - File Created
// Additional Comments:
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps
`default_nettype none

module alu
    import riscv_core_pkg::*;
(
    // AI_TAG: PORT_DESC - alu_op_i - Control signal selecting the ALU operation to perform.
    input  alu_op_e alu_op_i,
    // AI_TAG: PORT_DESC - operand_a_i - First 32-bit data operand (e.g., from rs1 or PC).
    input  word_t   operand_a_i,
    // AI_TAG: PORT_DESC - operand_b_i - Second 32-bit data operand (e.g., from rs2 or immediate).
    input  word_t   operand_b_i,

    // AI_TAG: PORT_DESC - alu_result_o - 32-bit result of the ALU operation.
    output word_t   alu_result_o,
    // AI_TAG: PORT_DESC - zero_o - Flag that is asserted if the ALU result is zero. Used for branch evaluation.
    output logic    zero_o
);

    // AI_TAG: FEATURE - Implements RV32I arithmetic operations: ADD, SUB.
    // AI_TAG: FEATURE - Implements RV32I logical operations: XOR, OR, AND.
    // AI_TAG: FEATURE - Implements RV32I shift operations: SLL, SRL, SRA.
    // AI_TAG: FEATURE - Implements RV32I comparison operations: SLT, SLTU.
    // AI_TAG: FEATURE - Implements pass-through capabilities for LUI and address calculations.

    logic [XLEN-1:0] alu_result;

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

    // AI_TAG: INTERNAL_LOGIC - Zero Flag Generation.
    // Description: Combinatorially asserts 'zero_o' if the ALU result is zero.
    // The result of a SUB operation is used to evaluate branch conditions (e.g., BEQ).
    assign alu_result_o = alu_result;
    assign zero_o       = (alu_result == '0);

endmodule : alu

`default_nettype wire