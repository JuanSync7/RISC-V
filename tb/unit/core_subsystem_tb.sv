//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: core_subsystem_tb.sv
// Module: core_subsystem_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Testbench for the core_subsystem module.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module core_subsystem_tb;

    import riscv_core_pkg::*;

    // Instantiate the core_subsystem
    core_subsystem dut (
        .clk_i(clk),
        .rst_ni(rst_n),
        .icache_if(mem_if.master),
        .dcache_if(mem_if.master)
    );

    // Memory model
    memory_req_rsp_if mem_if();
    memory_model mem (
        .clk_i(clk),
        .rst_ni(rst_n),
        .instr_req_valid_i(mem_if.req_valid),
        .instr_req_ready_o(mem_if.req_ready),
        .instr_req_addr_i(mem_if.req.addr),
        .instr_rsp_valid_o(mem_if.rsp_valid),
        .instr_rsp_ready_i(mem_if.rsp_ready),
        .instr_rsp_data_o(mem_if.rsp.data),
        .instr_rsp_error_o(mem_if.rsp.error),
        .data_req_valid_i(mem_if.req_valid),
        .data_req_ready_o(mem_if.req_ready),
        .data_req_addr_i(mem_if.req.addr),
        .data_req_write_i(mem_if.req.write),
        .data_req_data_i(mem_if.req.data),
        .data_req_strb_i(mem_if.req.strb),
        .data_rsp_valid_o(mem_if.rsp_valid),
        .data_rsp_ready_i(mem_if.rsp_ready),
        .data_rsp_data_o(mem_if.rsp.data),
        .data_rsp_error_o(mem_if.rsp.error)
    );

    // Clock and reset generation
    logic clk = 0;
    logic rst_n = 0;

    always #5 clk = ~clk;

    initial begin
        #10 rst_n = 1;
    end

    // Test sequence
    initial begin
        // Wait for reset to de-assert
        @(posedge rst_n);

        // TODO: Add test sequences here

        $finish;
    end

endmodule : core_subsystem_tb
