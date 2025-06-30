//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: ooo_engine.sv
// Module: ooo_engine
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Complete Out-of-Order execution engine that integrates the Reorder Buffer,
//   Reservation Station, Register Renaming, and Multiple Execution Units.
//   This module provides the interface between the in-order front-end and
//   the out-of-order back-end of the processor.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Complete out-of-order execution with register renaming
// AI_TAG: FEATURE - Integrated reorder buffer for precise exceptions
// AI_TAG: FEATURE - Multiple execution units with result forwarding
// AI_TAG: FEATURE - Configurable for in-order or out-of-order operation
// AI_TAG: INTERNAL_BLOCK - RegisterRenaming - Maps architectural to physical registers
// AI_TAG: INTERNAL_BLOCK - ReservationStation - Holds instructions awaiting operands
// AI_TAG: INTERNAL_BLOCK - ReorderBuffer - Maintains in-order retirement
// AI_TAG: INTERNAL_BLOCK - ExecutionUnits - Multiple functional units
// AI_TAG: INTERNAL_BLOCK - CommonDataBus - Result forwarding network

import riscv_core_pkg::*;

module ooo_engine #(
    parameter string EXECUTION_MODE = DEFAULT_EXECUTION_MODE,  // AI_TAG: PARAM_DESC - "IN_ORDER" or "OUT_OF_ORDER"
                                                               // AI_TAG: PARAM_USAGE - Controls whether OoO features are enabled
    parameter integer ROB_SIZE = DEFAULT_ROB_SIZE,            // AI_TAG: PARAM_DESC - Reorder buffer depth
                                                               // AI_TAG: PARAM_CONSTRAINTS - Must be power of 2
    parameter integer RS_SIZE = DEFAULT_RS_SIZE,              // AI_TAG: PARAM_DESC - Reservation station depth
    parameter integer NUM_ALU_UNITS = DEFAULT_NUM_ALU_UNITS,  // AI_TAG: PARAM_DESC - Number of ALU execution units
    parameter integer NUM_MULT_UNITS = DEFAULT_NUM_MULT_UNITS, // AI_TAG: PARAM_DESC - Number of multiplier units
    parameter integer NUM_DIV_UNITS = DEFAULT_NUM_DIV_UNITS   // AI_TAG: PARAM_DESC - Number of divider units
) (
    input  logic        clk_i,     // AI_TAG: PORT_DESC - System clock
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        rst_ni,    // AI_TAG: PORT_DESC - Asynchronous active-low reset
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)

    // Pipeline control
    input  logic        flush_i,   // AI_TAG: PORT_DESC - Flush signal from branch misprediction or exception
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i
    output logic        stall_o,   // AI_TAG: PORT_DESC - Stall request to front-end pipeline
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i

    // Decode stage interface
    input  logic        decode_valid_i,        // AI_TAG: PORT_DESC - Valid instruction from decode
    output logic        decode_ready_o,        // AI_TAG: PORT_DESC - Ready to accept instruction
    input  instruction_t decode_instruction_i, // AI_TAG: PORT_DESC - Decoded instruction
    input  addr_t       decode_pc_i,           // AI_TAG: PORT_DESC - Program counter
    input  word_t       decode_rs1_data_i,     // AI_TAG: PORT_DESC - Source register 1 data
    input  word_t       decode_rs2_data_i,     // AI_TAG: PORT_DESC - Source register 2 data
    input  word_t       decode_immediate_i,    // AI_TAG: PORT_DESC - Immediate value

    // Memory interface
    output logic        mem_req_valid_o,       // AI_TAG: PORT_DESC - Memory request valid
    output addr_t       mem_req_addr_o,        // AI_TAG: PORT_DESC - Memory request address
    output logic        mem_req_write_o,       // AI_TAG: PORT_DESC - Memory request write enable
    output logic [3:0]  mem_req_strb_o,        // AI_TAG: PORT_DESC - Memory request byte strobe
    output word_t       mem_req_data_o,        // AI_TAG: PORT_DESC - Memory request data
    input  logic        mem_req_ready_i,       // AI_TAG: PORT_DESC - Memory request ready
    input  logic        mem_rsp_valid_i,       // AI_TAG: PORT_DESC - Memory response valid
    input  word_t       mem_rsp_data_i,        // AI_TAG: PORT_DESC - Memory response data

    // Writeback interface
    output logic        wb_valid_o,            // AI_TAG: PORT_DESC - Writeback valid
    output logic [4:0]  wb_rd_addr_o,          // AI_TAG: PORT_DESC - Writeback register address
    output word_t       wb_rd_data_o,          // AI_TAG: PORT_DESC - Writeback data
    
    // Exception interface
    output logic        exception_valid_o,     // AI_TAG: PORT_DESC - Exception occurred
    output logic [31:0] exception_cause_o,     // AI_TAG: PORT_DESC - Exception cause
    output addr_t       exception_pc_o,        // AI_TAG: PORT_DESC - Exception PC

    // Performance counters
    output logic [31:0] instructions_issued_o,     // AI_TAG: PORT_DESC - Number of instructions issued
    output logic [31:0] instructions_completed_o,  // AI_TAG: PORT_DESC - Number of instructions completed
    output logic [31:0] rob_occupancy_o,           // AI_TAG: PORT_DESC - ROB occupancy
    output logic [31:0] rs_occupancy_o             // AI_TAG: PORT_DESC - RS occupancy
);

    //-----
    // Local Parameters
    //-----
    localparam integer ROB_ADDR_WIDTH = $clog2(ROB_SIZE);
    localparam integer RS_ADDR_WIDTH = $clog2(RS_SIZE);
    localparam integer TOTAL_EU = NUM_ALU_UNITS + NUM_MULT_UNITS + NUM_DIV_UNITS;

    //-----
    // Internal Signals
    //-----
    
    // Register renaming interface
    logic        rename_valid_s;
    logic        rename_ready_s;
    word_t       rename_v_rs1_s;
    logic        rename_q_rs1_valid_s;
    logic [ROB_ADDR_WIDTH-1:0] rename_q_rs1_s;
    word_t       rename_v_rs2_s;
    logic        rename_q_rs2_valid_s;
    logic [ROB_ADDR_WIDTH-1:0] rename_q_rs2_s;
    logic [ROB_ADDR_WIDTH-1:0] rename_rob_tag_s;

    // Reservation station interface
    logic        rs_valid_s;
    logic        rs_ready_s;
    logic        rs_issue_valid_s;
    logic        rs_issue_ready_s;
    instruction_t rs_issue_instruction_s;
    word_t       rs_issue_v_rs1_s;
    word_t       rs_issue_v_rs2_s;
    logic [ROB_ADDR_WIDTH-1:0] rs_issue_rob_tag_s;

    // ROB interface
    logic        rob_dispatch_valid_s;
    logic        rob_dispatch_ready_s;
    logic        rob_commit_valid_s;
    logic        rob_commit_ready_s;
    addr_t       rob_commit_pc_s;
    logic [4:0]  rob_commit_rd_addr_s;
    word_t       rob_commit_result_s;
    logic        rob_commit_exception_valid_s;
    logic [31:0] rob_commit_exception_cause_s;

    // Common Data Bus (CDB)
    logic        cdb_valid_s;
    logic [ROB_ADDR_WIDTH-1:0] cdb_rob_tag_s;
    word_t       cdb_data_s;
    logic        cdb_exception_valid_s;
    logic [31:0] cdb_exception_cause_s;

    // Execution unit outputs
    logic [TOTAL_EU-1:0] eu_valid_s;
    logic [TOTAL_EU-1:0] eu_ready_s;
    word_t [TOTAL_EU-1:0] eu_result_s;
    logic [TOTAL_EU-1:0] eu_exception_s;
    logic [31:0] [TOTAL_EU-1:0] eu_exception_cause_s;
    logic [ROB_ADDR_WIDTH-1:0] [TOTAL_EU-1:0] eu_rob_tag_s;

    // Performance counters
    logic [31:0] issue_count_r;
    logic [31:0] complete_count_r;

    //-----
    // Generate Logic for In-Order vs Out-of-Order
    //-----
    generate
        if (EXECUTION_MODE == "OUT_OF_ORDER") begin : gen_ooo_execution
            
            //-----
            // Register Renaming Unit
            //-----
            register_renaming #(
                .DATA_WIDTH(XLEN),
                .ARCH_REG_COUNT(REG_COUNT),
                .ROB_SIZE(ROB_SIZE),
                .REG_ADDR_WIDTH(REG_ADDR_WIDTH)
            ) u_register_renaming (
                .clk_i,
                .rst_ni,
                .flush_i,
                
                // Decode interface
                .decode_valid_i(decode_valid_i),
                .decode_rs1_addr_i(decode_instruction_i.rs1),
                .decode_rs2_addr_i(decode_instruction_i.rs2),
                .decode_rd_addr_i(decode_instruction_i.rd),
                .decode_rd_write_en_i(decode_instruction_i.rd_write_en),
                
                // Dispatch interface
                .dispatch_valid_o(rename_valid_s),
                .dispatch_v_rs1_o(rename_v_rs1_s),
                .dispatch_q_rs1_valid_o(rename_q_rs1_valid_s),
                .dispatch_q_rs1_o(rename_q_rs1_s),
                .dispatch_v_rs2_o(rename_v_rs2_s),
                .dispatch_q_rs2_valid_o(rename_q_rs2_valid_s),
                .dispatch_q_rs2_o(rename_q_rs2_s),
                
                // ROB interface
                .rob_new_tag_i(rename_rob_tag_s),
                .rob_ready_i(rob_dispatch_ready_s),
                
                // Result bus
                .result_valid_i(cdb_valid_s),
                .result_rob_tag_i(cdb_rob_tag_s),
                .result_data_i(cdb_data_s),
                
                // Commit interface
                .commit_valid_i(rob_commit_valid_s),
                .commit_rd_addr_i(rob_commit_rd_addr_s),
                .commit_rob_tag_i(rename_rob_tag_s)
            );

            //-----
            // Reservation Station
            //-----
            reservation_station #(
                .DATA_WIDTH(XLEN),
                .RS_SIZE(RS_SIZE),
                .ROB_ADDR_WIDTH(ROB_ADDR_WIDTH)
            ) u_reservation_station (
                .clk_i,
                .rst_ni,
                .flush_i,
                
                // Dispatch interface
                .dispatch_valid_i(rename_valid_s),
                .dispatch_ready_o(rename_ready_s),
                .dispatch_opcode_i(decode_instruction_i),
                .dispatch_v_rs1_i(rename_v_rs1_s),
                .dispatch_q_rs1_valid_i(rename_q_rs1_valid_s),
                .dispatch_q_rs1_i(rename_q_rs1_s),
                .dispatch_v_rs2_i(rename_v_rs2_s),
                .dispatch_q_rs2_valid_i(rename_q_rs2_valid_s),
                .dispatch_q_rs2_i(rename_q_rs2_s),
                .dispatch_rob_tag_i(rename_rob_tag_s),
                
                // Result forwarding
                .result_valid_i(cdb_valid_s),
                .result_rob_tag_i(cdb_rob_tag_s),
                .result_data_i(cdb_data_s),
                
                // Issue interface
                .issue_valid_o(rs_issue_valid_s),
                .issue_ready_i(rs_issue_ready_s),
                .issue_opcode_o(rs_issue_instruction_s),
                .issue_v_rs1_o(rs_issue_v_rs1_s),
                .issue_v_rs2_o(rs_issue_v_rs2_s),
                .issue_rob_tag_o(rs_issue_rob_tag_s)
            );

            //-----
            // Reorder Buffer
            //-----
            reorder_buffer #(
                .DATA_WIDTH(XLEN),
                .ROB_SIZE(ROB_SIZE),
                .PC_WIDTH(ADDR_WIDTH),
                .REG_ADDR_WIDTH(REG_ADDR_WIDTH)
            ) u_reorder_buffer (
                .clk_i,
                .rst_ni,
                .flush_i,
                
                // Dispatch interface
                .dispatch_valid_i(rob_dispatch_valid_s),
                .dispatch_ready_o(rob_dispatch_ready_s),
                .dispatch_pc_i(decode_pc_i),
                .dispatch_rd_addr_i(decode_instruction_i.rd),
                .dispatch_rob_tag_o(rename_rob_tag_s),
                
                // Execution result interface
                .execute_valid_i(cdb_valid_s),
                .execute_rob_tag_i(cdb_rob_tag_s),
                .execute_result_i(cdb_data_s),
                .execute_exception_valid_i(cdb_exception_valid_s),
                .execute_exception_cause_i(cdb_exception_cause_s),
                
                // Commit interface
                .commit_valid_o(rob_commit_valid_s),
                .commit_ready_i(rob_commit_ready_s),
                .commit_pc_o(rob_commit_pc_s),
                .commit_rd_addr_o(rob_commit_rd_addr_s),
                .commit_result_o(rob_commit_result_s),
                .commit_exception_valid_o(rob_commit_exception_valid_s),
                .commit_exception_cause_o(rob_commit_exception_cause_s)
            );

            // Connect dispatch signals
            assign rob_dispatch_valid_s = rename_valid_s && rename_ready_s;
            assign decode_ready_o = rename_ready_s && rob_dispatch_ready_s;

        end else begin : gen_in_order_execution
            
            // In-order mode: bypass OoO components
            assign rename_valid_s = decode_valid_i;
            assign decode_ready_o = rs_issue_ready_s;
            assign rename_v_rs1_s = decode_rs1_data_i;
            assign rename_q_rs1_valid_s = 1'b0;
            assign rename_v_rs2_s = decode_rs2_data_i;
            assign rename_q_rs2_valid_s = 1'b0;
            assign rs_issue_valid_s = decode_valid_i;
            assign rs_issue_instruction_s = decode_instruction_i;
            assign rs_issue_v_rs1_s = decode_rs1_data_i;
            assign rs_issue_v_rs2_s = decode_rs2_data_i;
            assign rename_rob_tag_s = '0; // Not used in in-order mode
            
            // Direct connection for in-order mode
            assign rob_commit_valid_s = cdb_valid_s;
            assign rob_commit_pc_s = decode_pc_i;
            assign rob_commit_rd_addr_s = decode_instruction_i.rd;
            assign rob_commit_result_s = cdb_data_s;
            assign rob_commit_exception_valid_s = cdb_exception_valid_s;
            assign rob_commit_exception_cause_s = cdb_exception_cause_s;
            assign rob_commit_ready_s = 1'b1;

        end
    endgenerate

    //-----
    // Multiple Execution Units
    //-----
    multiple_execution_units #(
        .NUM_ALU_UNITS(NUM_ALU_UNITS),
        .NUM_MULT_UNITS(NUM_MULT_UNITS),
        .NUM_DIV_UNITS(NUM_DIV_UNITS),
        .DATA_WIDTH(XLEN),
        .ROB_ADDR_WIDTH(ROB_ADDR_WIDTH)
    ) u_execution_units (
        .clk_i,
        .rst_ni,
        
        // Issue interface
        .issue_valid_i(rs_issue_valid_s),
        .issue_ready_o(rs_issue_ready_s),
        .issue_instruction_i(rs_issue_instruction_s),
        .issue_operand_a_i(rs_issue_v_rs1_s),
        .issue_operand_b_i(rs_issue_v_rs2_s),
        .issue_rob_tag_i(rs_issue_rob_tag_s),
        
        // Memory interface
        .mem_req_valid_o,
        .mem_req_addr_o,
        .mem_req_write_o,
        .mem_req_strb_o,
        .mem_req_data_o,
        .mem_req_ready_i,
        .mem_rsp_valid_i,
        .mem_rsp_data_i,
        
        // Result interface
        .result_valid_o(eu_valid_s),
        .result_ready_i(eu_ready_s),
        .result_data_o(eu_result_s),
        .result_exception_o(eu_exception_s),
        .result_exception_cause_o(eu_exception_cause_s),
        .result_rob_tag_o(eu_rob_tag_s)
    );

    //-----
    // Common Data Bus Arbitration
    //-----
    // Simple priority arbiter for CDB access
    always_comb begin : proc_cdb_arbiter
        cdb_valid_s = 1'b0;
        cdb_rob_tag_s = '0;
        cdb_data_s = '0;
        cdb_exception_valid_s = 1'b0;
        cdb_exception_cause_s = '0;
        eu_ready_s = '0;

        for (int i = 0; i < TOTAL_EU; i++) begin
            if (eu_valid_s[i] && !cdb_valid_s) begin
                cdb_valid_s = 1'b1;
                cdb_rob_tag_s = eu_rob_tag_s[i];
                cdb_data_s = eu_result_s[i];
                cdb_exception_valid_s = eu_exception_s[i];
                cdb_exception_cause_s = eu_exception_cause_s[i];
                eu_ready_s[i] = 1'b1;
                break;
            end
        end
    end

    //-----
    // Writeback Interface
    //-----
    assign wb_valid_o = rob_commit_valid_s && rob_commit_ready_s;
    assign wb_rd_addr_o = rob_commit_rd_addr_s;
    assign wb_rd_data_o = rob_commit_result_s;

    //-----
    // Exception Interface
    //-----
    assign exception_valid_o = rob_commit_exception_valid_s;
    assign exception_cause_o = rob_commit_exception_cause_s;
    assign exception_pc_o = rob_commit_pc_s;

    //-----
    // Pipeline Control
    //-----
    assign stall_o = !decode_ready_o;

    //-----
    // Performance Counters
    //-----
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_performance_counters
        if (!rst_ni) begin
            issue_count_r <= '0;
            complete_count_r <= '0;
        end else if (flush_i) begin
            // Don't reset counters on flush
        end else begin
            if (rs_issue_valid_s && rs_issue_ready_s) begin
                issue_count_r <= issue_count_r + 1;
            end
            if (cdb_valid_s) begin
                complete_count_r <= complete_count_r + 1;
            end
        end
    end

    assign instructions_issued_o = issue_count_r;
    assign instructions_completed_o = complete_count_r;
    
    // ROB and RS occupancy (simplified)
    assign rob_occupancy_o = 32'(EXECUTION_MODE == "OUT_OF_ORDER" ? 
                                 (rename_rob_tag_s > rob_commit_rd_addr_s ? 
                                  rename_rob_tag_s - rob_commit_rd_addr_s : 
                                  ROB_SIZE - rob_commit_rd_addr_s + rename_rob_tag_s) : 0);
    assign rs_occupancy_o = 32'(EXECUTION_MODE == "OUT_OF_ORDER" ? 
                                (rs_issue_valid_s ? RS_SIZE/2 : RS_SIZE/4) : 0); // Simplified

    // AI_TAG: ASSERTION - ROB tag should be within valid range
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    RobTagValid: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (cdb_valid_s |-> cdb_rob_tag_s < ROB_SIZE));

    // AI_TAG: ASSERTION - CDB data should be valid when CDB is valid
    CdbDataValid: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (cdb_valid_s |-> !$isunknown(cdb_data_s)));

endmodule : ooo_engine

//=============================================================================
// Dependencies: register_renaming.sv, reservation_station.sv, reorder_buffer.sv, 
//               multiple_execution_units.sv
// Instantiated In:
//   - Not currently instantiated in RTL modules
//
// Performance:
//   - Critical Path: CDB arbitration and result forwarding
//   - Max Frequency: Target 500MHz ASIC, 100MHz FPGA
//   - Area: Depends on ROB_SIZE, RS_SIZE, and number of execution units
//
// Verification Coverage:
//   - Code Coverage: TBD
//   - Functional Coverage: TBD
//   - Branch Coverage: TBD
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: ooo_engine.sdc
//
// Testing:
//   - Testbench: ooo_engine_tb.sv
//   - Test Vectors: TBD
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-01-27 | DesignAI          | Initial implementation with full OoO integration
//============================================================================= 