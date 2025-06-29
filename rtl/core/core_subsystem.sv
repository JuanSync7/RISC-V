//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: core_subsystem.sv
// Module: core_subsystem
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Core subsystem that integrates the fetch, decode, execute, memory, and
//   writeback stages of the RISC-V pipeline. Manages pipeline control,
//   hazard detection, and exception handling with configurable reset vector.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_config_pkg::*;
import riscv_types_pkg::*;
import riscv_core_pkg::*;

module core_subsystem #(
    parameter addr_t RESET_VECTOR = DEFAULT_RESET_VECTOR,
    parameter integer NUM_CORES = DEFAULT_NUM_CORES,
    parameter integer CORE_ID = 0
) (
    // Clock and Reset
    input  logic        clk_i,
    input  logic        rst_ni,

    // Memory Interface
    output logic        mem_req_valid_o,
    output addr_t       mem_req_addr_o,
    output logic        mem_req_write_o,
    output logic [3:0]  mem_req_strb_o,
    output word_t       mem_req_data_o,
    input  logic        mem_req_ready_i,
    input  logic        mem_rsp_valid_i,
    input  word_t       mem_rsp_data_i,

    // Interrupt Interface
    input  logic        interrupt_i,
    input  logic [31:0] interrupt_cause_i,

    // Debug Interface
    input  logic        debug_req_i,
    output logic        debug_ack_o,

    // Performance Counters
    output logic [31:0] cycle_count_o,
    output logic [31:0] instruction_count_o
);

    // AI_TAG: INTERNAL_LOGIC - Pipeline stage interfaces
    // IF/ID pipeline register
    logic        if_id_valid;
    word_t       if_id_instr;
    addr_t       if_id_pc;
    logic        if_id_branch_predicted;
    addr_t       if_id_branch_target;

    // ID/EX pipeline register
    logic        id_ex_valid;
    word_t       id_ex_instr;
    addr_t       id_ex_pc;
    word_t       id_ex_rs1_data;
    word_t       id_ex_rs2_data;
    word_t       id_ex_immediate;
    logic [4:0]  id_ex_alu_op;
    logic        id_ex_mem_read;
    logic        id_ex_mem_write;
    logic        id_ex_reg_write;
    logic [4:0]  id_ex_rd_addr;

    // EX/MEM pipeline register
    logic        ex_mem_valid;
    word_t       ex_mem_instr;
    addr_t       ex_mem_pc;
    word_t       ex_mem_alu_result;
    word_t       ex_mem_rs2_data;
    logic        ex_mem_mem_read;
    logic        ex_mem_mem_write;
    logic        ex_mem_reg_write;
    logic [4:0]  ex_mem_rd_addr;

    // MEM/WB pipeline register
    logic        mem_wb_valid;
    word_t       mem_wb_instr;
    addr_t       mem_wb_pc;
    word_t       mem_wb_result;
    logic        mem_wb_reg_write;
    logic [4:0]  mem_wb_rd_addr;

    // AI_TAG: INTERNAL_LOGIC - Hazard detection signals
    logic        data_hazard_detected;
    logic        control_hazard_detected;
    logic        pipeline_stall;
    logic        pipeline_flush;

    // AI_TAG: INTERNAL_LOGIC - Exception signals
    logic        exception_valid;
    logic [31:0] exception_cause;
    addr_t       exception_pc;

    // AI_TAG: INTERNAL_LOGIC - Performance counters
    logic [31:0] cycle_count_r;
    logic [31:0] instruction_count_r;

    // AI_TAG: INTERNAL_LOGIC - Fetch stage instantiation
    fetch_stage #(
        .RESET_VECTOR(RESET_VECTOR),
        .BTB_ENTRIES(DEFAULT_BTB_ENTRIES),
        .BHT_ENTRIES(DEFAULT_BHT_ENTRIES)
    ) u_fetch_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .stall_i(pipeline_stall),
        .flush_i(pipeline_flush),
        .branch_taken_i(control_hazard_detected),
        .branch_target_i(exception_pc),
        .mem_req_valid_o(mem_req_valid_o),
        .mem_req_addr_o(mem_req_addr_o),
        .mem_req_ready_i(mem_req_ready_i),
        .mem_rsp_valid_i(mem_rsp_valid_i),
        .mem_rsp_data_i(mem_rsp_data_i),
        .bp_req_valid_o(),
        .bp_req_pc_o(),
        .bp_rsp_valid_i(1'b0),
        .bp_rsp_data_i('0),
        .if_valid_o(if_id_valid),
        .if_instr_o(if_id_instr),
        .if_pc_o(if_id_pc),
        .if_branch_predicted_o(if_id_branch_predicted),
        .if_branch_target_o(if_id_branch_target)
    );

    // AI_TAG: INTERNAL_LOGIC - Decode stage instantiation
    decode_stage u_decode_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .stall_i(pipeline_stall),
        .flush_i(pipeline_flush),
        .if_id_reg_i({if_id_valid, if_id_instr, if_id_pc}),
        .id_ex_reg_o({id_ex_valid, id_ex_instr, id_ex_pc, id_ex_rs1_data, id_ex_rs2_data, id_ex_immediate, id_ex_alu_op, id_ex_mem_read, id_ex_mem_write, id_ex_reg_write, id_ex_rd_addr}),
        .reg_file_rs1_addr_o(),
        .reg_file_rs2_addr_o(),
        .reg_file_rs1_data_i('0),
        .reg_file_rs2_data_i('0),
        .hazard_detected_o(data_hazard_detected)
    );

    // AI_TAG: INTERNAL_LOGIC - Execute stage instantiation
    execute_stage u_execute_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .stall_i(pipeline_stall),
        .flush_i(pipeline_flush),
        .id_ex_reg_i({id_ex_valid, id_ex_instr, id_ex_pc, id_ex_rs1_data, id_ex_rs2_data, id_ex_immediate, id_ex_alu_op, id_ex_mem_read, id_ex_mem_write, id_ex_reg_write, id_ex_rd_addr}),
        .ex_mem_reg_o({ex_mem_valid, ex_mem_instr, ex_mem_pc, ex_mem_alu_result, ex_mem_rs2_data, ex_mem_mem_read, ex_mem_mem_write, ex_mem_reg_write, ex_mem_rd_addr}),
        .mem_req_write_o(mem_req_write_o),
        .mem_req_strb_o(mem_req_strb_o),
        .mem_req_data_o(mem_req_data_o),
        .exception_valid_o(exception_valid),
        .exception_cause_o(exception_cause),
        .exception_pc_o(exception_pc)
    );

    // AI_TAG: INTERNAL_LOGIC - Memory stage instantiation
    mem_stage u_mem_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .stall_i(pipeline_stall),
        .flush_i(pipeline_flush),
        .ex_mem_reg_i({ex_mem_valid, ex_mem_instr, ex_mem_pc, ex_mem_alu_result, ex_mem_rs2_data, ex_mem_mem_read, ex_mem_mem_write, ex_mem_reg_write, ex_mem_rd_addr}),
        .mem_wb_reg_o({mem_wb_valid, mem_wb_instr, mem_wb_pc, mem_wb_result, mem_wb_reg_write, mem_wb_rd_addr}),
        .mem_rsp_valid_i(mem_rsp_valid_i),
        .mem_rsp_data_i(mem_rsp_data_i)
    );

    // AI_TAG: INTERNAL_LOGIC - Writeback stage instantiation
    writeback_stage u_writeback_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .mem_wb_reg_i({mem_wb_valid, mem_wb_instr, mem_wb_pc, mem_wb_result, mem_wb_reg_write, mem_wb_rd_addr}),
        .reg_file_write_en_o(),
        .reg_file_rd_addr_o(),
        .reg_file_rd_data_o(),
        .instruction_retired_o()
    );

    // AI_TAG: INTERNAL_LOGIC - Pipeline control
    assign pipeline_stall = data_hazard_detected;
    assign pipeline_flush = control_hazard_detected || exception_valid;

    // AI_TAG: INTERNAL_LOGIC - Control hazard detection
    assign control_hazard_detected = exception_valid || interrupt_i;

    // AI_TAG: INTERNAL_LOGIC - Performance counter update
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            cycle_count_r <= '0;
            instruction_count_r <= '0;
        end else begin
            cycle_count_r <= cycle_count_r + 1;
            if (mem_wb_valid) begin
                instruction_count_r <= instruction_count_r + 1;
            end
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Output assignments
    assign cycle_count_o = cycle_count_r;
    assign instruction_count_o = instruction_count_r;
    assign debug_ack_o = debug_req_i;

    // AI_TAG: ASSERTION - Reset vector should be aligned
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - core_subsystem_coverage.reset_vector_alignment_cp
    ResetVectorAlignment: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (RESET_VECTOR[1:0] == 2'b00));

    // AI_TAG: ASSERTION - Pipeline should not be stalled and flushed simultaneously
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - core_subsystem_coverage.pipeline_control_cp
    PipelineControl: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (!(pipeline_stall && pipeline_flush)));

endmodule : core_subsystem

//=============================================================================
// Dependencies: riscv_config_pkg, riscv_types_pkg, riscv_core_pkg
//
// Performance:
//   - Critical Path: Through the entire pipeline
//   - Max Frequency: Limited by the slowest pipeline stage
//   - Area: Significant - includes all pipeline stages and control logic
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