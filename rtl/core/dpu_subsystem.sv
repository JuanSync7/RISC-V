//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: dpu_subsystem.sv
// Module: dpu_subsystem
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Data Processing Unit (DPU) subsystem. This module acts as a wrapper
//   for various specialized data processing accelerators like FPU, VPU,
//   and ML Inference units, allowing for flexible configuration.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_dpu_types_pkg::*;
import riscv_fpu_types_pkg::*;
import riscv_vpu_types_pkg::*;

module dpu_subsystem #(
    // AI_TAG: PARAM_DESC - DPU_ID - Unique identifier for this DPU instance.
    parameter integer DPU_ID = 0,
    // AI_TAG: PARAM_DESC - ENABLE_FPU - Enable/Disable Floating Point Unit instantiation.
    parameter logic ENABLE_FPU = 1'b0,
    // AI_TAG: PARAM_DESC - ENABLE_VPU - Enable/Disable Vector Processing Unit instantiation.
    parameter logic ENABLE_VPU = 1'b0,
    // AI_TAG: PARAM_DESC - ENABLE_ML_INFERENCE - Enable/Disable Machine Learning Inference Unit instantiation.
    parameter logic ENABLE_ML_INFERENCE = 1'b0
)
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Control Interface from CPU (Generic DPU Request) ---
    // This interface is used by the CPU to send generic requests to the DPU subsystem.
    // The DPU subsystem will then route these requests to the appropriate internal unit.
    input  dpu_req_t    dpu_req_i,
    output logic        dpu_req_ready_o,

    // --- Status/Response Interface to CPU (Generic DPU Response) ---
    output dpu_rsp_t    dpu_rsp_o,
    output logic        dpu_busy_o,
    output logic        dpu_error_o
);

    // Internal signals for routing requests/responses
    // FPU signals
    fpu_req_t  fpu_req_s;
    logic      fpu_req_ready_s;
    fpu_rsp_t  fpu_rsp_s;
    logic      fpu_rsp_ready_s;

    // VPU signals
    vpu_req_t  vpu_req_s;
    logic      vpu_req_ready_s;
    vpu_rsp_t  vpu_rsp_s;
    logic      vpu_rsp_ready_s;

    // ML Inference signals (placeholder for now)
    logic [31:0] ml_input_s;
    logic [31:0] ml_output_s;
    logic        ml_busy_s;

    // Overall DPU busy and error status
    logic overall_busy;
    logic overall_error;

    // Default assignments for unused interfaces
    assign fpu_req_s = '0;
    assign fpu_rsp_ready_s = 1'b0;
    assign vpu_req_s = '0;
    assign vpu_rsp_ready_s = 1'b0;
    assign ml_input_s = '0;

    // Route incoming DPU request to appropriate unit based on opcode or other criteria
    // This is a simplified example; a real implementation would have more sophisticated decoding.
    always_comb begin
        dpu_req_ready_o = 1'b0; // Default to not ready
        dpu_rsp_o = '0; // Default response
        overall_busy = 1'b0;
        overall_error = 1'b0;

        // Placeholder for routing logic
        // In a real design, you'd decode dpu_req_i.opcode to determine which unit to activate.
        // For now, we'll just pass through to the first enabled unit.

        if (ENABLE_FPU && dpu_req_i.valid) begin
            // Example: Route to FPU if opcode matches FPU operation
            fpu_req_s.valid = dpu_req_i.valid;
            fpu_req_s.opcode = fpu_op_e'(dpu_req_i.opcode); // Cast generic opcode to FPU opcode
            fpu_req_s.operand1 = dpu_req_i.data; // Example: use dpu_req_i.data as operand1
            fpu_req_s.operand2 = dpu_req_i.addr; // Example: use dpu_req_i.addr as operand2
            fpu_req_s.rd_addr = dpu_req_i.rd_addr; // Assuming rd_addr is part of dpu_req_t
            fpu_req_s.rs1_addr = dpu_req_i.rs1_addr; // Assuming rs1_addr is part of dpu_req_t
            fpu_req_s.rs2_addr = dpu_req_i.rs2_addr; // Assuming rs2_addr is part of dpu_req_t

            dpu_req_ready_o = fpu_req_ready_s;
            dpu_rsp_o = dpu_rsp_t'{valid: fpu_rsp_s.valid, data: fpu_rsp_s.data, error: fpu_rsp_s.error};
            overall_busy = fpu_rsp_s.valid ? 1'b0 : 1'b1; // If FPU has valid response, it's not busy anymore
            overall_error = fpu_rsp_s.error;
            fpu_rsp_ready_s = dpu_rsp_o.valid; // Acknowledge FPU response
        end else if (ENABLE_VPU && dpu_req_i.valid) begin
            // Example: Route to VPU
            vpu_req_s.valid = dpu_req_i.valid;
            vpu_req_s.opcode = vpu_op_e'(dpu_req_i.opcode); // Cast generic opcode to VPU opcode
            vpu_req_s.operand1_vector[0] = dpu_req_i.data; // Example: use dpu_req_i.data as first element
            vpu_req_s.addr = dpu_req_i.addr;
            vpu_req_s.vector_length = dpu_req_i.vector_length; // Assuming vector_length is part of dpu_req_t
            vpu_req_s.rd_addr = dpu_req_i.rd_addr;
            vpu_req_s.rs1_addr = dpu_req_i.rs1_addr;
            vpu_req_s.rs2_addr = dpu_req_i.rs2_addr;

            dpu_req_ready_o = vpu_req_ready_s;
            dpu_rsp_o = dpu_rsp_t'{valid: vpu_rsp_s.valid, data: vpu_rsp_s.result_vector[0], error: vpu_rsp_s.error}; // Example: return first element
            overall_busy = vpu_rsp_s.valid ? 1'b0 : 1'b1;
            overall_error = vpu_rsp_s.error;
            vpu_rsp_ready_s = dpu_rsp_o.valid;
        end else if (ENABLE_ML_INFERENCE && dpu_req_i.valid) begin
            // Example: Route to ML Inference Unit
            ml_input_s = dpu_req_i.data;
            dpu_req_ready_o = !ml_busy_s;
            dpu_rsp_o = dpu_rsp_t'{valid: ml_busy_s, data: ml_output_s, error: 1'b0}; // Placeholder
            overall_busy = ml_busy_s;
            overall_error = 1'b0;
        end else begin
            dpu_req_ready_o = 1'b1; // Always ready if no DPU is enabled or request is invalid
            dpu_rsp_o = '0;
            overall_busy = 1'b0;
            overall_error = 1'b0;
        end
    end

    assign dpu_busy_o = overall_busy;
    assign dpu_error_o = overall_error;

    // Conditional FPU Instantiation
    generate
        if (ENABLE_FPU) begin : gen_fpu_unit
            fpu_unit u_fpu_unit (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .fpu_req_i(fpu_req_s),
                .fpu_req_ready_o(fpu_req_ready_s),
                .fpu_rsp_o(fpu_rsp_s),
                .fpu_rsp_ready_i(fpu_rsp_ready_s)
            );
        end
    endgenerate

    // Conditional VPU Instantiation
    generate
        if (ENABLE_VPU) begin : gen_vpu_unit
            vpu_unit u_vpu_unit (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .vpu_req_i(vpu_req_s),
                .vpu_req_ready_o(vpu_req_ready_s),
                .vpu_rsp_o(vpu_rsp_s),
                .vpu_rsp_ready_i(vpu_rsp_ready_s)
            );
        end
    endgenerate

    // Conditional ML Inference Unit Instantiation
    generate
        if (ENABLE_ML_INFERENCE) begin : gen_ml_inference_unit
            ml_inference_unit u_ml_inference_unit (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .ml_input_i(ml_input_s),
                .ml_output_o(ml_output_s),
                .ml_busy_o(ml_busy_s)
            );
        end
    endgenerate

endmodule : dpu_subsystem