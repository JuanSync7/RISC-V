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

import mmu_pkg::*;

module fetch_stage
#(
    // AI_TAG: PARAMETER - RESET_VECTOR - The address where the core begins execution after reset.
    parameter addr_t RESET_VECTOR = DEFAULT_RESET_VECTOR,
    // AI_TAG: PARAMETER - BRANCH_PREDICTOR_TYPE - Type of branch predictor to use.
    parameter string BRANCH_PREDICTOR_TYPE = DEFAULT_BRANCH_PREDICTOR_TYPE,
    // AI_TAG: PARAMETER - BTB_ENTRIES - Number of entries in the Branch Target Buffer.
    parameter integer BTB_ENTRIES = DEFAULT_BTB_ENTRIES,
    // AI_TAG: PARAMETER - BHT_ENTRIES - Number of entries in the Branch History Table.
    parameter integer BHT_ENTRIES = DEFAULT_BHT_ENTRIES,
    // AI_TAG: PARAMETER - PHT_ENTRIES - Number of entries in the Pattern History Table.
    parameter integer PHT_ENTRIES = DEFAULT_PHT_ENTRIES,
    // AI_TAG: PARAMETER - SELECTOR_ENTRIES - Number of entries in the Selector Table.
    parameter integer SELECTOR_ENTRIES = DEFAULT_SELECTOR_ENTRIES,
    // AI_TAG: PARAMETER - GLOBAL_HISTORY_WIDTH - Width of the Global History Register.
    parameter integer GLOBAL_HISTORY_WIDTH = DEFAULT_GLOBAL_HISTORY_WIDTH,
    // AI_TAG: PARAMETER - RAS_ENTRIES - Number of entries in the Return Address Stack.
    parameter integer RAS_ENTRIES = DEFAULT_RAS_ENTRIES,
    // AI_TAG: PARAMETER - ENABLE_MMU - Enable Memory Management Unit
    parameter bit ENABLE_MMU = 1
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

    // --- MMU Interface (from core_subsystem) ---
    input  mmu_request_t           mmu_req_i,
    input  logic                   mmu_req_valid_i,
    output logic                   mmu_req_ready_o,
    output mmu_response_t          mmu_resp_o,
    output logic                   mmu_resp_valid_o,
    input  logic                   mmu_resp_ready_i,

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

    

    // AI_TAG: INTERNAL_WIRE - Exception detection signals
    logic instr_addr_misaligned;
    logic instr_access_fault;
    exception_info_t exception_detected;

    // AI_TAG: INTERNAL_LOGIC - Branch Predictor instance
    generate
        if (BRANCH_PREDICTOR_TYPE == "TOURNAMENT") begin : gen_tournament_bp
            tournament_predictor #(
                .ADDR_WIDTH(ADDR_WIDTH),
                .GLOBAL_HISTORY_WIDTH(GLOBAL_HISTORY_WIDTH),
                .BTB_ENTRIES(BTB_ENTRIES),
                .BHT_ENTRIES(BHT_ENTRIES),
                .PHT_ENTRIES(PHT_ENTRIES),
                .SELECTOR_ENTRIES(SELECTOR_ENTRIES)
            ) i_tournament_predictor (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .pc_i(pc_q),
                .prediction_o(bp_prediction_o),
                .update_i(bp_update_i)
            );
        end else if (BRANCH_PREDICTOR_TYPE == "STATIC") begin : gen_static_bp
            // Static predictor: always predict not taken
            assign bp_prediction_o.predict_taken = 1'b0;
            assign bp_prediction_o.predict_target = pc_q + 4;
            assign bp_prediction_o.btb_hit = 1'b0;
        end else begin : gen_default_bp
            // Default to static predictor if type is unknown or not specified
            assign bp_prediction_o.predict_taken = 1'b0;
            assign bp_prediction_o.predict_target = pc_q + 4;
            assign bp_prediction_o.btb_hit = 1'b0;
        end
    endgenerate

    // AI_TAG: INTERNAL_LOGIC - Return Address Stack instance
    return_stack_buffer #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .STACK_DEPTH(RAS_ENTRIES)
    ) i_ras (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .push_en_i(bp_update_i.update_valid && bp_update_i.is_jal),
        .push_addr_i(bp_update_i.jal_target),
        .pop_en_i(bp_update_i.update_valid && bp_update_i.is_jalr),
        .pop_addr_o(ras_pop_addr_c),
        .pop_valid_o(ras_pop_valid_c)
    );

    // AI_TAG: INTERNAL_LOGIC - RAS output signals
    logic ras_pop_valid_c;
    addr_t ras_pop_addr_c;

    // AI_TAG: INTERNAL_LOGIC - Next PC Selection Logic
    // Description: This logic determines the address of the next instruction.
    // Priority 1: A redirect from a branch, jump, or exception has highest priority.
    // Priority 2: Branch prediction (if no redirect and BPU predicts taken).
    // Priority 3: Return Address Stack (for JALR instructions).
    // Priority 4: Default sequential execution (PC + 4).
    always_comb begin
        if (pc_redirect_en_i) begin
            pc_d = pc_redirect_target_i;
        end else if (bp_prediction_o.predict_taken && bp_prediction_o.btb_hit) begin
            pc_d = bp_prediction_o.predict_target;
        end else if (ras_pop_valid_c && bp_update_i.is_jalr) begin // Use RAS for JALR prediction
            pc_d = ras_pop_addr_c;
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

    // Internal signals for MMU interaction
    mmu_request_t  mmu_instr_req;
    mmu_response_t mmu_instr_resp;
    logic          mmu_instr_req_valid;
    logic          mmu_instr_req_ready;
    logic          mmu_instr_resp_valid;
    logic          mmu_instr_resp_ready;

    // MMU request for instruction fetch
    assign mmu_instr_req.vaddr = pc_q;
    assign mmu_instr_req.is_write = 1'b0;
    assign mmu_instr_req.is_fetch = 1'b1;
    assign mmu_instr_req_valid = !stall_f_i && !pc_redirect_en_i;

    // Connect to MMU interface
    assign mmu_req_o = mmu_instr_req;
    assign mmu_req_valid_o = mmu_instr_req_valid;
    assign mmu_instr_req_ready = mmu_req_ready_i;
    assign mmu_instr_resp = mmu_resp_i;
    assign mmu_instr_resp_valid = mmu_resp_valid_i;
    assign mmu_resp_ready_o = mmu_instr_resp_ready;

    // Instantiate ICache with memory wrapper interface
    icache u_icache (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .pc_i(ENABLE_MMU ? mmu_instr_resp.paddr : pc_q), // Use physical address from MMU if enabled
        .valid_i(ENABLE_MMU ? (mmu_instr_resp_valid && !mmu_instr_resp.fault) : (!stall_f_i && !pc_redirect_en_i)),
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
        if (ENABLE_MMU && mmu_instr_resp_valid && mmu_instr_resp.fault) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = mmu_instr_resp.fault_type; // Use fault type from MMU
            exception_detected.pc = pc_q; // The virtual PC
            exception_detected.tval = pc_q; // The virtual address
            exception_detected.priority = PRIO_INSTR_FAULT; // Assuming highest priority for now
        end else if (instr_addr_misaligned) begin
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