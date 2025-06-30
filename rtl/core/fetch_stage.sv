//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: fetch_stage.sv
// Module: fetch_stage
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   The Fetch Stage (F) of the 5-stage RISC-V pipeline. Manages the Program
//   Counter (PC), handles PC redirection for branches, jumps, and exceptions,
//   drives the AXI4 instruction memory interface to fetch instructions, and
//   passes the fetched instruction and its PC to the Decode stage via the
//   IF/ID pipeline register.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module fetch_stage
#(
    // AI_TAG: PARAMETER - RESET_VECTOR - The address where the core begins execution after reset.
    parameter addr_t RESET_VECTOR = DEFAULT_RESET_VECTOR,
    // AI_TAG: PARAMETER - BTB_ENTRIES - Number of entries in the Branch Target Buffer.
    parameter integer BTB_ENTRIES = DEFAULT_BTB_ENTRIES,
    // AI_TAG: PARAMETER - BHT_ENTRIES - Number of entries in the Branch History Table.
    parameter integer BHT_ENTRIES = DEFAULT_BHT_ENTRIES
)
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Control Signals from Hazard Unit ---
    // AI_TAG: PORT_DESC - stall_f_i - Freezes the PC and stops new fetch requests. Asserted for memory waits or downstream hazards.
    input  logic        stall_f_i,
    // AI_TAG: PORT_DESC - stall_d_i - Stalls the IF/ID pipeline register, preventing new data from entering Decode.
    input  logic        stall_d_i,
    // AI_TAG: PORT_DESC - flush_f_i - Injects a bubble (NOP) into the IF/ID register, nullifying the currently fetched instruction.
    input  logic        flush_f_i,

    // --- PC Redirect Interface (from Execute/Memory stages) ---
    // AI_TAG: PORT_DESC - pc_redirect_en_i - Indicates a control flow change (branch, jump, exception).
    input  logic        pc_redirect_en_i,
    // AI_TAG: PORT_DESC - pc_redirect_target_i - The new target address for the PC.
    input  addr_t       pc_redirect_target_i,

    // --- Branch Predictor Update Interface ---
    // AI_TAG: PORT_DESC - bp_update_i - Branch prediction update information from execute stage.
    input  branch_update_t bp_update_i,

    // --- Memory Wrapper Instruction Interface ---
    // AI_TAG: PORT_DESC - instr_req_valid_o - Instruction request valid.
    output logic        instr_req_valid_o,
    // AI_TAG: PORT_DESC - instr_req_ready_i - Instruction request ready.
    input  logic        instr_req_ready_i,
    // AI_TAG: PORT_DESC - instr_req_addr_o - Instruction request address.
    output addr_t       instr_req_addr_o,
    // AI_TAG: PORT_DESC - instr_rsp_valid_i - Instruction response valid.
    input  logic        instr_rsp_valid_i,
    // AI_TAG: PORT_DESC - instr_rsp_ready_o - Instruction response ready.
    output logic        instr_rsp_ready_o,
    // AI_TAG: PORT_DESC - instr_rsp_data_i - Instruction response data.
    input  word_t       instr_rsp_data_i,
    // AI_TAG: PORT_DESC - instr_rsp_error_i - Instruction response error.
    input  logic        instr_rsp_error_i,

    // --- Output to Decode Stage ---
    // AI_TAG: PORT_DESC - if_id_reg_o - The IF/ID pipeline register data passed to the Decode stage.
    output if_id_reg_t  if_id_reg_o,
    // AI_TAG: PORT_DESC - pc_f_o - The current value of the PC for use in control/hazard logic.
    output addr_t       pc_f_o,
    // AI_TAG: PORT_DESC - bp_prediction_o - Branch prediction result for the current instruction.
    output branch_prediction_t bp_prediction_o,

    // AI_TAG: NEW_PORT - Exception detection output
    // AI_TAG: PORT_DESC - exception_o - Exception information from fetch stage
    output exception_info_t exception_o,

    // --- Performance Counters Interface ---
    // AI_TAG: PORT_DESC - perf_hit_count_o - Total number of cache hits.
    output logic [31:0] perf_hit_count_o,
    // AI_TAG: PORT_DESC - perf_miss_count_o - Total number of cache misses.
    output logic [31:0] perf_miss_count_o,
    // AI_TAG: PORT_DESC - perf_flush_count_o - Total number of cache flushes.
    output logic [31:0] perf_flush_count_o,
    // AI_TAG: PORT_DESC - perf_total_requests_o - Total number of cache requests.
    output logic [31:0] perf_total_requests_o,
    // AI_TAG: PORT_DESC - perf_hit_rate_o - Cache hit rate (0-100, scaled by 100).
    output logic [31:0] perf_hit_rate_o,
    // AI_TAG: PORT_DESC - perf_counter_reset_i - Reset all performance counters.
    input  logic        perf_counter_reset_i
);

    // AI_TAG: INTERNAL_STORAGE - Program Counter register.
    addr_t pc_q, pc_d;

    // AI_TAG: INTERNAL_STORAGE - IF/ID pipeline register.
    if_id_reg_t if_id_reg_q;

    // AI_TAG: INTERNAL_LOGIC - Branch prediction signals
    logic        bp_predict_taken;
    addr_t       bp_predict_target;
    logic        bp_btb_hit;

    // AI_TAG: INTERNAL_WIRE - Exception detection signals
    logic instr_addr_misaligned;
    logic instr_access_fault;
    exception_info_t exception_detected;

    // AI_TAG: INTERNAL_LOGIC - Branch Predictor instance
    branch_predictor #(
        .BTB_ENTRIES(BTB_ENTRIES),
        .BHT_ENTRIES(BHT_ENTRIES)
    ) branch_predictor_inst (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .pc_i(pc_q),
        .predict_taken_o(bp_predict_taken),
        .predict_target_o(bp_predict_target),
        .btb_hit_o(bp_btb_hit),
        .update_i(bp_update_i.update_valid),
        .update_pc_i(bp_update_i.update_pc),
        .actual_taken_i(bp_update_i.actual_taken),
        .actual_target_i(bp_update_i.actual_target),
        .is_branch_i(bp_update_i.is_branch)
    );

    // AI_TAG: INTERNAL_LOGIC - Next PC Selection Logic
    // Description: This logic determines the address of the next instruction.
    // Priority 1: A redirect from a branch, jump, or exception has highest priority.
    // Priority 2: Branch prediction (if no redirect and BPU predicts taken).
    // Priority 3: Default sequential execution (PC + 4).
    always_comb begin
        if (pc_redirect_en_i) begin
            pc_d = pc_redirect_target_i;
        end else if (bp_predict_taken && bp_btb_hit) begin
            pc_d = bp_predict_target;
        end else begin
            pc_d = pc_q + 4;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Program Counter Register
    // Description: The PC is updated when the pipeline is not stalled.
    // A stall in the fetch stage (stall_f_i) freezes the PC.
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            pc_q <= RESET_VECTOR;
        end else if (!stall_f_i) begin
            pc_q <= pc_d;
        end
    end

    // --- ICache Interface ---
    // Add signals for ICache
    logic        icache_ready;
    word_t       icache_instruction;
    logic        icache_hit;
    logic        icache_valid;
    logic        icache_flush;
    logic        icache_flush_done;

    // Instantiate ICache with memory wrapper interface
    icache u_icache (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .pc_i(pc_q),
        .valid_i(!stall_f_i && !pc_redirect_en_i),
        .ready_o(icache_ready),
        .instruction_o(icache_instruction),
        .hit_o(icache_hit),
        .valid_o(icache_valid),
        .mem_req_valid_o(instr_req_valid_o),
        .mem_req_ready_i(instr_req_ready_i),
        .mem_req_addr_o(instr_req_addr_o),
        .mem_rsp_valid_i(instr_rsp_valid_i),
        .mem_rsp_data_i(instr_rsp_data_i),
        .mem_rsp_ready_o(instr_rsp_ready_o),
        .flush_i(icache_flush),
        .flush_done_o(icache_flush_done),
        .perf_hit_count_o(perf_hit_count_o),
        .perf_miss_count_o(perf_miss_count_o),
        .perf_flush_count_o(perf_flush_count_o),
        .perf_total_requests_o(perf_total_requests_o),
        .perf_hit_rate_o(perf_hit_rate_o),
        .perf_counter_reset_i(perf_counter_reset_i)
    );

    // ICache flush logic (can be tied to reset or exception flush)
    assign icache_flush = flush_f_i;

    // AI_TAG: INTERNAL_LOGIC - Instruction Exception Detection
    // Instruction address misalignment detection (RISC-V requires 2-byte alignment)
    always_comb begin
        instr_addr_misaligned = 1'b0;
        if (pc_q[0]) begin // Check if PC is not 2-byte aligned
            instr_addr_misaligned = 1'b1;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Instruction Access Fault Detection
    always_comb begin
        instr_access_fault = 1'b0;
        // Check for instruction memory response errors
        if (instr_rsp_valid_i && instr_rsp_error_i) begin
            instr_access_fault = 1'b1;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Fetch Exception Information Generation
    always_comb begin
        exception_detected = '0; // Default to no exception
        
        // Check for fetch exceptions in priority order
        if (instr_addr_misaligned) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_INSTR_ADDR_MISALIGNED;
            exception_detected.pc = pc_q; // The misaligned PC
            exception_detected.tval = pc_q; // The misaligned address
            exception_detected.priority = PRIO_MISALIGNED;
        end
        else if (instr_access_fault) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_INSTR_ACCESS_FAULT;
            exception_detected.pc = pc_q; // The faulting PC
            exception_detected.tval = pc_q; // The faulting address
            exception_detected.priority = PRIO_INSTR_FAULT;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Exception Output Assignment
    assign exception_o = exception_detected;

    // IF/ID pipeline register now uses ICache output
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            if_id_reg_q.instr <= NOP_INSTRUCTION;
            if_id_reg_q.pc    <= '0;
            if_id_reg_q.valid <= 1'b0;
        end else if (!stall_d_i) begin
            if (flush_f_i) begin
                if_id_reg_q.instr <= NOP_INSTRUCTION;
                if_id_reg_q.pc    <= '0;
                if_id_reg_q.valid <= 1'b0;
            end else begin
                if_id_reg_q.instr <= icache_instruction;
                if_id_reg_q.pc    <= pc_q;
                if_id_reg_q.valid <= icache_valid;
            end
        end
    end

    // --- Module Outputs ---
    assign if_id_reg_o = if_id_reg_q;
    assign pc_f_o      = pc_q;
    assign bp_prediction_o = {bp_predict_taken, bp_predict_target, bp_btb_hit};

endmodule : fetch_stage

//=============================================================================
// Dependencies: riscv_config_pkg, riscv_types_pkg, riscv_bp_types_pkg
//
// Performance:
//   - Critical Path: PC update to instruction fetch
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
// NOTE: `default_nettype wire is set below for legacy compatibility. Prefer keeping `none` throughout the project and explicitly typing all signals. Remove if not required.
`default_nettype wire