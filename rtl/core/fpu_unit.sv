//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: fpu_unit.sv
// Module: fpu_unit
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Placeholder module for a Floating Point Unit (FPU).
//   This unit will handle floating-point arithmetic operations.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_fpu_types_pkg::*;

module fpu_unit
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // FPU Request Interface
    input  fpu_req_t    fpu_req_i,
    output logic        fpu_req_ready_o,

    // FPU Response Interface
    output fpu_rsp_t    fpu_rsp_o,
    input  logic        fpu_rsp_ready_i
);

    // Internal signals and registers for a 3-stage pipeline
    // Stage 1: Decode/Issue
    fpu_req_t  s1_req_r;
    logic      s1_valid_r;

    // Stage 2: Execute
    fpu_req_t  s2_req_r;
    logic      s2_valid_r;
    word_t     s2_operand1_real;
    word_t     s2_operand2_real;
    logic      s2_error_r;

    // Stage 3: Writeback
    fpu_rsp_t  s3_rsp_r;
    logic      s3_valid_r;

    // Output assignments
    assign fpu_req_ready_o = !s1_valid_r; // Ready if Stage 1 is not busy
    assign fpu_rsp_o = s3_rsp_r;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            s1_req_r <= '0;
            s1_valid_r <= 1'b0;
            s2_req_r <= '0;
            s2_valid_r <= 1'b0;
            s2_operand1_real <= '0;
            s2_operand2_real <= '0;
            s2_error_r <= 1'b0;
            s3_rsp_r <= '0;
            s3_valid_r <= 1'b0;
        end else begin
            // Stage 3: Writeback
            s3_valid_r <= s2_valid_r;
            s3_rsp_r.valid <= s2_valid_r;
            s3_rsp_r.rd_addr <= s2_req_r.rd_addr;
            s3_rsp_r.error <= s2_error_r;
            s3_rsp_r.data <= s2_operand1_real; // s2_operand1_real now holds the result

            // Stage 2: Execute
            s2_valid_r <= s1_valid_r;
            s2_req_r <= s1_req_r;
            s2_error_r <= 1'b0; // Reset error for this stage

            if (s1_valid_r) begin
                shortreal op1_real, op2_real, result_real;
                int op_int;

                op1_real = $bitstoshortreal(s1_req_r.operand1);
                op2_real = $bitstoshortreal(s1_req_r.operand2);

                case (s1_req_r.opcode)
                    FPU_ADD: begin
                        result_real = op1_real + op2_real;
                        s2_operand1_real <= $shortrealtobits(result_real);
                    end
                    FPU_SUB: begin
                        result_real = op1_real - op2_real;
                        s2_operand1_real <= $shortrealtobits(result_real);
                    end
                    FPU_MUL: begin
                        result_real = op1_real * op2_real;
                        s2_operand1_real <= $shortrealtobits(result_real);
                    end
                    FPU_DIV: begin
                        if (op2_real == 0.0) begin
                            s2_operand1_real <= '0; // Indicate error or specific NaN/Inf
                            s2_error_r <= 1'b1; // Division by zero error
                        end else begin
                            result_real = op1_real / op2_real;
                            s2_operand1_real <= $shortrealtobits(result_real);
                        end
                    end
                    FPU_SQRT: begin
                        if (op1_real < 0.0) begin
                            s2_operand1_real <= '0; // Indicate error for sqrt of negative number
                            s2_error_r <= 1'b1;
                        end else begin
                            result_real = $sqrt(op1_real);
                            s2_operand1_real <= $shortrealtobits(result_real);
                        end
                    end
                    FPU_F2I: begin
                        op_int = int'(op1_real); // Convert float to integer
                        s2_operand1_real <= op_int;
                    end
                    FPU_I2F: begin
                        op_int = int'(s1_req_r.operand1); // Convert word_t to integer
                        result_real = shortreal'(op_int); // Convert integer to float
                        s2_operand1_real <= $shortrealtobits(result_real);
                    end
                    FPU_FMA: begin
                        shortreal op1_real_fma, op2_real_fma, op3_real_fma, result_real_fma;
                        op1_real_fma = $bitstoshortreal(s1_req_r.operand1);
                        op2_real_fma = $bitstoshortreal(s1_req_r.operand2);
                        op3_real_fma = $bitstoshortreal(s1_req_r.operand3); // Assuming operand3 is available for FMA
                        result_real_fma = (op1_real_fma * op2_real_fma) + op3_real_fma;
                        s2_operand1_real <= $shortrealtobits(result_real_fma);
                    end
                    default: begin
                        s2_operand1_real <= '0;
                        s2_error_r <= 1'b1; // Unsupported opcode
                    end
                endcase
            end else begin
                s2_operand1_real <= '0;
            end

            // Stage 1: Decode/Issue
            s1_valid_r <= fpu_req_i.valid && fpu_req_ready_o;
            if (fpu_req_i.valid && fpu_req_ready_o) begin
                s1_req_r <= fpu_req_i;
            end else begin
                s1_req_r <= '0;
            end
        end
    end

endmodule : fpu_unit
