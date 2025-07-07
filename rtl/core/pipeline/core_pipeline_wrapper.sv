//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: core_pipeline_wrapper.sv
// Module: core_pipeline_wrapper
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   This module acts as a wrapper for either the in-order or out-of-order
//   RISC-V pipeline, instantiating the appropriate pipeline based on the
//   EXECUTION_MODE parameter.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_ooo_types_pkg::*;
import ooo_pkg::*;

module core_pipeline_wrapper #(
    parameter addr_t RESET_VECTOR = DEFAULT_RESET_VECTOR,
    parameter integer CORE_ID = 0,
    parameter string EXECUTION_MODE = DEFAULT_EXECUTION_MODE,
    parameter string BRANCH_PREDICTOR_TYPE = DEFAULT_BRANCH_PREDICTOR_TYPE,
    parameter int unsigned L1_CACHE_SIZE = DEFAULT_L1_CACHE_SIZE,
    parameter logic ENABLE_FPU = ENABLE_FPU,
    parameter logic ENABLE_VPU = ENABLE_VPU,
    parameter logic ENABLE_ML_INFERENCE = ENABLE_ML_INFERENCE,
    parameter logic ENABLE_MMU = 1,
    parameter logic ENABLE_QOS = 1,
    parameter logic ENABLE_OOO = 0 // New: Enable Out-of-Order Execution
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    // Memory Interfaces
    memory_req_rsp_if.master icache_if,
    memory_req_rsp_if.master dcache_if,

    // Inter-Core Communication Interfaces (for multi-core)
    inter_core_comm_if.core comm_if,
    sync_primitives_if.core sync_if,

    // Interrupt Interface
    input  logic        m_software_interrupt_i,
    input  logic        m_timer_interrupt_i,
    input  logic        m_external_interrupt_i,

    // Pipeline Control Signals
    output logic        pipeline_stall_o,
    output logic        branch_mispredicted_o,
    output logic        instruction_retired_o,
    output logic        core_active_o,

    // Exception Output
    output exception_info_t exception_o,

    // OOO-specific inputs (if OOO is enabled)
    input  ooo_dispatch_t ooo_dispatch_o, // From core_subsystem
    input  ooo_commit_t   ooo_commit_i,   // From core_subsystem
    input  logic          ooo_decode_ready_i, // From core_subsystem
    input  logic          ooo_flush_i,     // From core_subsystem

    // CSR-related outputs for core_subsystem
    output logic [2:0]  csr_op_o,
    output logic        trap_en_o,
    output addr_t       mepc_o,
    output word_t       mcause_o,
    output word_t       mtval_o,
    output logic        pipeline_stall_o_csr, // Output for CSR regfile
    output logic        instruction_retired_o_csr // Output for CSR regfile
);

    // Internal signals
    if_id_reg_t         if_id_reg;
    id_ex_reg_t         id_ex_reg;
    ex_mem_reg_t        ex_mem_reg;
    mem_wb_reg_t        mem_wb_reg;
    
    addr_t              pc_f;
    branch_prediction_t bp_prediction;
    branch_update_t     bp_update;

    exception_info_t    fetch_exception;
    exception_info_t    execute_exception;
    exception_info_t    memory_exception;

    logic        data_hazard_detected;
    logic        control_hazard_detected;
    logic        structural_hazard_detected;
    logic        pipeline_stall_internal;
    logic        pipeline_flush_internal;

    logic [4:0]  reg_file_rs1_addr;
    logic [4:0]  reg_file_rs2_addr;
    logic [4:0]  reg_file_rd_addr;
    word_t       reg_file_rs1_data;
    word_t       reg_file_rs2_data;
    word_t       reg_file_rd_data;
    logic        reg_file_write_en;

    logic        ex_mem_branch_taken;
    addr_t       ex_mem_branch_target;

    logic        interrupt_pending;
    logic [31:0] exception_cause_internal;
    addr_t       exception_pc_internal;

    logic        instruction_retired_internal;

    logic exception_pending_internal;

    assign exception_pending_internal = fetch_exception.valid || execute_exception.valid || memory_exception.valid || (ENABLE_OOO ? ooo_commit_s.exception.valid : 1'b0);

    // Branch Prediction Unit Instantiation
    branch_prediction_unit #(
        .BRANCH_PREDICTOR_TYPE(BRANCH_PREDICTOR_TYPE)
    ) u_branch_prediction_unit (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .pc_i(pc_f),
        .bp_prediction_o(bp_prediction),
        .bp_update_i(bp_update),
        .ex_mem_reg_valid_i(ex_mem_reg.valid),
        .ex_mem_reg_ctrl_is_branch_i(ex_mem_reg.ctrl.is_branch),
        .ex_mem_reg_pc_i(ex_mem_reg.pc),
        .ex_mem_branch_taken_i(ex_mem_branch_taken),
        .ex_mem_branch_target_i(ex_mem_branch_target),
        .id_ex_reg_ctrl_is_jal_i(id_ex_reg.ctrl.is_jal),
        .id_ex_reg_jal_target_i(id_ex_reg.jal_target),
        .id_ex_reg_ctrl_is_jalr_i(id_ex_reg.ctrl.is_jalr)
    );

    generate
        if (ENABLE_OOO) begin : gen_ooo_pipeline
            // AI_TAG: INTERNAL_BLOCK - Out-of-Order Execution Engine
            ooo_engine #(
                .DATA_WIDTH(DATA_WIDTH),
                .PC_WIDTH(PC_WIDTH),
                .REG_ADDR_WIDTH(REG_ADDR_WIDTH),
                .RS_SIZE(RS_SIZE),
                .ROB_SIZE(ROB_SIZE)
            ) u_ooo_engine (
                .clk_i             (clk_i),
                .rst_ni            (rst_ni),
                .flush_i           (ooo_flush_i),
                .decode_dispatch_i (ooo_dispatch_o),
                .decode_ready_o    (ooo_decode_ready_i),
                .commit_o          (ooo_commit_s),
                .commit_ready_i    (1'b1) // Always ready to commit from ROB to architectural state
            );

            // Connect fetch stage to OOO engine's decode interface
            fetch_stage #(
                .RESET_VECTOR(RESET_VECTOR),
                .BTB_ENTRIES(DEFAULT_BTB_ENTRIES),
                .BHT_ENTRIES(DEFAULT_BHT_ENTRIES)
            ) u_fetch_stage (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .stall_f_i(pipeline_stall),
                .stall_d_i(pipeline_stall),
                .flush_f_i(pipeline_flush),
                .pc_redirect_en_i(ooo_commit_s.exception.valid || (bp_prediction.taken && !ooo_decode_ready_i)),
                .pc_redirect_target_i(ooo_commit_s.exception.valid ? ooo_commit_s.pc : bp_prediction.target),
                .bp_update_i(bp_update),
                .instr_req_valid_o(icache_if.req_valid),
                .instr_req_ready_i(icache_if.req_ready),
                .instr_req_addr_o(icache_if.req.addr),
                .instr_rsp_valid_i(icache_if.rsp.valid),
                .instr_rsp_ready_o(icache_if.rsp.ready),
                .instr_rsp_data_i(icache_if.rsp.data),
                .instr_rsp_error_i(icache_if.rsp.error),
                .if_id_reg_o(if_id_reg),
                .pc_f_o(pc_f),
                .bp_prediction_o(bp_prediction),
                .exception_o(fetch_exception),
                .perf_hit_count_o(),
                .perf_miss_count_o(),
                .perf_flush_count_o(),
                .perf_total_requests_o(),
                .perf_hit_rate_o(),
                .perf_counter_reset_i(1'b0)
            );

            // Connect fetch stage output to decode stage input
            decode_stage #(
                .ENABLE_OOO(ENABLE_OOO) // Pass ENABLE_OOO to decode_stage
            ) u_decode_stage (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .stall_e_i(pipeline_stall),
                .flush_d_i(pipeline_flush),
                .if_id_reg_i(if_id_reg),
                .rs1_addr_o(reg_file_rs1_addr),
                .rs2_addr_o(reg_file_rs2_addr),
                .rs1_data_i(reg_file_rs1_data),
                .rs2_data_i(reg_file_rs2_data),
                .dispatch_o(ooo_dispatch_s) // Connect to OOO engine dispatch
            );

            // Connect OOO commit to writeback logic
            assign reg_file_write_en = ooo_commit_s.valid && (ooo_commit_s.rd_addr != 0);
            assign reg_file_rd_addr  = ooo_commit_s.rd_addr;
            assign reg_file_rd_data  = ooo_commit_s.result;
            assign instruction_retired = ooo_commit_s.valid;

            // Tie off unused in-order pipeline signals
            assign id_ex_reg = '0;
            assign ex_mem_reg = '0;
            assign mem_wb_reg = '0;
            assign data_hazard_detected = 1'b0;
            assign control_hazard_detected = 1'b0;
            assign structural_hazard_detected = 1'b0;
            assign ex_mem_branch_taken = 1'b0;
            assign ex_mem_branch_target = '0;

            // Connect outputs
            assign pipeline_stall_o = pipeline_stall_internal;
            assign branch_mispredicted_o = control_hazard_detected;
            assign instruction_retired_o = instruction_retired_internal;
            assign core_active_o = instruction_retired_internal; // Core is active if instructions are retiring
            assign exception_o = ooo_commit_s.exception; // Exception from OOO engine

        end else begin : gen_in_order_pipeline
            // AI_TAG: INTERNAL_BLOCK - Fetch stage with branch prediction
            fetch_stage #(.RESET_VECTOR(RESET_VECTOR), .BTB_ENTRIES(DEFAULT_BTB_ENTRIES), .BHT_ENTRIES(DEFAULT_BHT_ENTRIES)) u_fetch_stage (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .stall_f_i(pipeline_stall),
                .stall_d_i(pipeline_stall),
                .flush_f_i(pipeline_flush),
                .pc_redirect_en_i(ex_mem_branch_taken),
                .pc_redirect_target_i(ex_mem_branch_target),
                .bp_update_i(bp_update),
                .instr_req_valid_o(icache_if.req_valid),
                .instr_req_ready_i(icache_if.req_ready),
                .instr_req_addr_o(icache_if.req.addr),
                .instr_rsp_valid_i(icache_if.rsp.valid),
                .instr_rsp_ready_o(icache_if.rsp.ready),
                .instr_rsp_data_i(icache_if.rsp.data),
                .instr_rsp_error_i(icache_if.rsp.error),
                .if_id_reg_o(if_id_reg),
                .pc_f_o(pc_f),
                .bp_prediction_o(bp_prediction),
                .exception_o(fetch_exception),
                .perf_hit_count_o(),
                .perf_miss_count_o(),
                .perf_flush_count_o(),
                .perf_total_requests_o(),
                .perf_hit_rate_o(),
                .perf_counter_reset_i(1'b0)
            );

            // AI_TAG: INTERNAL_BLOCK - Decode stage with register file interface
            decode_stage u_decode_stage (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .stall_e_i(pipeline_stall),
                .flush_d_i(pipeline_flush),
                .if_id_reg_i(if_id_reg),
                .rs1_addr_o(reg_file_rs1_addr),
                .rs2_addr_o(reg_file_rs2_addr),
                .rs1_data_i(reg_file_rs1_data),
                .rs2_data_i(reg_file_rs2_data),
                .id_ex_reg_o(id_ex_reg),
                .is_jal_o(bp_update.is_jal),
                .jal_target_o(bp_update.jal_target),
                .is_jalr_o(bp_update.is_jalr)
            );

            // AI_TAG: INTERNAL_BLOCK - Execute stage with ALU and branch resolution
            execute_stage u_execute_stage (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .stall_m_i(pipeline_stall),
                .flush_e_i(pipeline_flush),
                .id_ex_reg_i(id_ex_reg),
                .ex_mem_reg_o(ex_mem_reg),
                .branch_taken_o(ex_mem_branch_taken),
                .branch_target_o(ex_mem_branch_target),
                .exception_o(execute_exception)
            );

            // AI_TAG: INTERNAL_BLOCK - Memory stage with data cache interface
            mem_stage u_mem_stage (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .stall_w_i(pipeline_stall),
                .flush_m_i(pipeline_flush),
                .ex_mem_reg_i(ex_mem_reg),
                .dcache_if(dcache_if),
                .mem_wb_reg_o(mem_wb_reg),
                .exception_o(memory_exception)
            );

            // AI_TAG: INTERNAL_BLOCK - Writeback stage with register file interface
            writeback_stage u_writeback_stage (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mem_wb_reg_i(mem_wb_reg),
                .reg_file_write_en_o(reg_file_write_en),
                .reg_file_rd_addr_o(reg_file_rd_addr),
                .reg_file_rd_data_o(reg_file_rd_data),
                .instruction_retired_o(instruction_retired)
            );

            //------------------------------------------------------------------------- 
            // Register File Instance
            //------------------------------------------------------------------------- 
            
            // AI_TAG: INTERNAL_BLOCK - Register file with dual read ports
            reg_file u_reg_file (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .rs1_addr_i(reg_file_rs1_addr),
                .rs2_addr_i(reg_file_rs2_addr),
                .rs1_data_o(reg_file_rs1_data),
                .rs2_data_o(reg_file_rs2_data),
                .rd_addr_i(reg_file_rd_addr),
                .rd_data_i(reg_file_rd_data),
                .rd_write_en_i(reg_file_write_en)
            );

            //------------------------------------------------------------------------- 
            // Hazard Detection Unit
            //------------------------------------------------------------------------- 
            
            // AI_TAG: INTERNAL_BLOCK - Hazard detection for pipeline control
            hazard_unit u_hazard_unit (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .if_id_reg_i(if_id_reg),
                .id_ex_reg_i(id_ex_reg),
                .ex_mem_reg_i(ex_mem_reg),
                .mem_wb_reg_i(mem_wb_reg),
                .data_hazard_o(data_hazard_detected),
                .control_hazard_o(control_hazard_detected),
                .structural_hazard_o(structural_hazard_detected)
            );

            //------------------------------------------------------------------------- 
            // Exception Handler
            //------------------------------------------------------------------------- 
            
            // AI_TAG: INTERNAL_BLOCK - Exception and interrupt handling
            exception_handler u_exception_handler (
                .clk_i(clk_i),
                .rst_ni(rst_ni_sync2),
                .fetch_exception_i(fetch_exception),
                .execute_exception_i(execute_exception),
                .memory_exception_i(memory_exception),
                .m_software_interrupt_i(m_software_interrupt_i),
                .m_timer_interrupt_i(m_timer_interrupt_i),
                .m_external_interrupt_i(m_external_interrupt_i),
                .interrupt_pending_o(interrupt_pending),
                .exception_pc_o(exception_pc),
                .exception_cause_o(exception_cause),
                .exception_o(exception_o)
            );

            //------------------------------------------------------------------------- 
            // Pipeline Control Logic
            //------------------------------------------------------------------------- 
            
            // AI_TAG: INTERNAL_LOGIC - Pipeline control and hazard handling
            assign pipeline_stall_internal = data_hazard_detected || structural_hazard_detected;
    assign pipeline_flush_internal = control_hazard_detected || exception_pending_internal || interrupt_pending;

            // Connect to performance monitoring outputs
            assign pipeline_stall_o = pipeline_stall;
            assign branch_mispredicted_o = control_hazard_detected;
            assign instruction_retired_o = instruction_retired;
            assign core_active_o = |if_id_reg.valid; // Core is active if there is a valid instruction in pipeline
        end
    endgenerate

endmodule : core_pipeline_wrapper

`default_nettype wire