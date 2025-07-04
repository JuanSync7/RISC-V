//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: memory_if.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: memory_if
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-29
// DESCRIPTION: Generic synchronous memory interface (request/response style).
// PRIMARY_PURPOSE: Provide a standard memory bus interface for core modules.
// ROLE_IN_SYSTEM: Base interface for instruction/data memories and cache subsystems.
// MODULE_TYPE: Interface
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: Custom simple memory protocol
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

interface memory_if #(
    parameter integer ADDR_WIDTH = 32,
    parameter integer DATA_WIDTH = 32,
    parameter integer BE_WIDTH   = DATA_WIDTH/8
) (
    input  logic clk,
    input  logic rst_n
);

    // Request channel
    logic                 req;
    logic                 we;
    logic [ADDR_WIDTH-1:0] addr;
    logic [DATA_WIDTH-1:0] wdata;
    logic [BE_WIDTH-1:0]   be;

    // Response channel
    logic [DATA_WIDTH-1:0] rdata;
    logic                 ready;

    // Simple task wrappers for testbenches
    task automatic write(input logic [ADDR_WIDTH-1:0] t_addr,
                         input logic [DATA_WIDTH-1:0] t_data,
                         input logic [BE_WIDTH-1:0]   t_be = {BE_WIDTH{1'b1}});
        req   <= 1'b1;
        we    <= 1'b1;
        addr  <= t_addr;
        wdata <= t_data;
        be    <= t_be;
        @(posedge clk);
        req <= 1'b0;
        we  <= 1'b0;
        @(posedge clk);
    endtask

    task automatic read(input logic [ADDR_WIDTH-1:0] t_addr,
                        output logic [DATA_WIDTH-1:0] t_data);
        req  <= 1'b1;
        we   <= 1'b0;
        addr <= t_addr;
        @(posedge clk);
        req <= 1'b0;
        @(posedge clk);
        t_data = rdata;
    endtask

endinterface : memory_if

`default_nettype wire