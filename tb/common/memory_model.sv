//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: memory_model.sv
// Module: memory_model
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   A simple memory model for testbenches.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module memory_model (
    input  logic        clk_i,
    input  logic        rst_ni,

    // Instruction memory interface
    input  logic        instr_req_valid_i,
    output logic        instr_req_ready_o,
    input  addr_t       instr_req_addr_i,
    output logic        instr_rsp_valid_o,
    input  logic        instr_rsp_ready_i,
    output word_t       instr_rsp_data_o,
    output logic        instr_rsp_error_o,

    // Data memory interface
    input  logic        data_req_valid_i,
    output logic        data_req_ready_o,
    input  addr_t       data_req_addr_i,
    input  logic        data_req_write_i,
    input  word_t       data_req_data_i,
    input  logic [3:0]  data_req_strb_i,
    output logic        data_rsp_valid_o,
    input  logic        data_rsp_ready_i,
    output word_t       data_rsp_data_o,
    output logic        data_rsp_error_o
);

    // Memory array
    logic [31:0] mem [0:1023];

    // Instruction memory logic
    assign instr_req_ready_o = 1'b1;
    assign instr_rsp_valid_o = instr_req_valid_i;
    assign instr_rsp_data_o  = mem[instr_req_addr_i >> 2];
    assign instr_rsp_error_o = 1'b0;

    // Data memory logic
    assign data_req_ready_o = 1'b1;
    assign data_rsp_valid_o = data_req_valid_i;
    assign data_rsp_data_o  = mem[data_req_addr_i >> 2];
    assign data_rsp_error_o = 1'b0;

    always_ff @(posedge clk_i) begin
        if (data_req_valid_i && data_req_write_i) begin
            if (data_req_strb_i[0]) mem[data_req_addr_i >> 2][7:0]   <= data_req_data_i[7:0];
            if (data_req_strb_i[1]) mem[data_req_addr_i >> 2][15:8]  <= data_req_data_i[15:8];
            if (data_req_strb_i[2]) mem[data_req_addr_i >> 2][23:16] <= data_req_data_i[23:16];
            if (data_req_strb_i[3]) mem[data_req_addr_i >> 2][31:24] <= data_req_data_i[31:24];
        end
    end

endmodule : memory_model
