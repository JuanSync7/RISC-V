////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-27
// Design Name:   RV32IM Core
// Module Name:   fetch_stage
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   The Fetch Stage (F) of the 5-stage RISC-V pipeline.
//                - Manages the Program Counter (PC).
//                - Handles PC redirection for branches, jumps, and exceptions.
//                - Drives the AXI4 instruction memory interface to fetch instructions.
//                - Passes the fetched instruction and its PC to the Decode stage
//                  via the IF/ID pipeline register.
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

module fetch_stage
    import riscv_core_pkg::*;
#(
    // AI_TAG: PARAMETER - RESET_VECTOR - The address where the core begins execution after reset.
    parameter addr_t RESET_VECTOR = 32'h0000_0000,
    // AI_TAG: PARAMETER - BTB_ENTRIES - Number of entries in the Branch Target Buffer.
    parameter integer BTB_ENTRIES = BPU_DEFAULT_BTB_ENTRIES,
    // AI_TAG: PARAMETER - BHT_ENTRIES - Number of entries in the Branch History Table.
    parameter integer BHT_ENTRIES = BPU_DEFAULT_BHT_ENTRIES
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

    // --- AXI4 Instruction Read Interface (Master) ---
    output logic        i_arvalid_o,
    input  logic        i_arready_i,
    output addr_t       i_araddr_o,
    output logic [2:0]  i_arprot_o,  // Privileged, secure, data access
    output logic [3:0]  i_arcache_o, // Bufferable, modifiable, etc.
    output logic [1:0]  i_arsize_o,  // 4-byte transfer
    input  word_t       i_rdata_i,
    input  logic        i_rvalid_i,
    output logic        i_rready_o,

    // --- Output to Decode Stage ---
    // AI_TAG: PORT_DESC - if_id_reg_o - The IF/ID pipeline register data passed to the Decode stage.
    output if_id_reg_t  if_id_reg_o,
    // AI_TAG: PORT_DESC - pc_f_o - The current value of the PC for use in control/hazard logic.
    output addr_t       pc_f_o,
    // AI_TAG: PORT_DESC - bp_prediction_o - Branch prediction result for the current instruction.
    output branch_prediction_t bp_prediction_o
);

    // AI_TAG: RISC-V_SPEC - A NOP is encoded as `addi x0, x0, 0`.
    localparam word_t NOP_INSTRUCTION = 32'h00000013;

    // AI_TAG: INTERNAL_STORAGE - Program Counter register.
    addr_t pc_q, pc_d;

    // AI_TAG: INTERNAL_STORAGE - IF/ID pipeline register.
    if_id_reg_t if_id_reg_q;

    // AI_TAG: INTERNAL_LOGIC - Branch prediction signals
    logic        bp_predict_taken;
    addr_t       bp_predict_target;
    logic        bp_btb_hit;

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

    // AI_TAG: INTERNAL_LOGIC - IF/ID Pipeline Register
    // Description: This register decouples the Fetch and Decode stages.
    // - It is stalled if the Decode stage is stalled (stall_d_i).
    // - It is flushed (loaded with a NOP) if a branch is mispredicted or an exception occurs.
    // - Otherwise, it latches the instruction received from memory.
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            if_id_reg_q.instr <= NOP_INSTRUCTION;
            if_id_reg_q.pc    <= '0;
            if_id_reg_q.valid <= 1'b0;
        end else if (!stall_d_i) begin
            // If the pipe is flowing, check for flushes or new valid instructions.
            if (flush_f_i) begin
                if_id_reg_q.instr <= NOP_INSTRUCTION;
                if_id_reg_q.pc    <= '0; // PC is irrelevant for a bubble
                if_id_reg_q.valid <= 1'b0;
            end else begin
                // Latch the incoming instruction from memory
                if_id_reg_q.instr <= i_rdata_i;
                if_id_reg_q.pc    <= pc_q; // Latch the PC that requested this instruction
                // AI_TAG: DESIGN_NOTE - The validity of the instruction in the D stage depends
                // on the memory system asserting i_rvalid and this stage being ready to accept it (i_rready_o).
                if_id_reg_q.valid <= i_rvalid_i & i_rready_o;
            end
        end
        // If stall_d_i is high, the register holds its previous value.
    end

    // AI_TAG: AXI4_LOGIC - Instruction Fetch AXI Read Channel
    // Description: Manages the AXI4 handshake to fetch instructions.
    assign i_araddr_o  = pc_q;
    // We issue a new read request if the stage is not stalled and not currently being redirected.
    assign i_arvalid_o = !stall_f_i && !pc_redirect_en_i;
    // We are ready to accept an instruction if the next stage is not stalled.
    assign i_rready_o  = !stall_d_i;

    // AXI constants for instruction fetch
    assign i_arprot_o  = 3'b010; // Privileged, Secure, Data access
    assign i_arcache_o = 4'b0010; // Normal Non-cacheable Bufferable
    assign i_arsize_o  = 2'b010;  // 4 bytes

    // --- Module Outputs ---
    assign if_id_reg_o = if_id_reg_q;
    assign pc_f_o      = pc_q;
    assign bp_prediction_o = {bp_predict_taken, bp_predict_target, bp_btb_hit};

endmodule : fetch_stage

`default_nettype wire