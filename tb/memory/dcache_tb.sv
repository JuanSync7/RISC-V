//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-07-05
//
// File: dcache_tb.sv
// Module: dcache_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Initial Testbench
//
// Description:
//   Testbench for the dcache module.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module dcache_tb;

    import riscv_core_pkg::*;
    import riscv_config_pkg::*;
    import riscv_mem_types_pkg::*;

    // Clock and Reset
    logic clk;
    logic rst_n;

    // D-Cache CPU Interface
    logic        req_valid;
    logic        req_ready;
    addr_t       req_addr;
    logic        req_write;
    word_t       req_wdata;
    logic [3:0]  req_wstrb;
    logic        rsp_valid;
    logic        rsp_ready;
    word_t       rsp_rdata;
    logic        rsp_error;

    // D-Cache Memory Interface
    logic        mem_req_valid;
    logic        mem_req_ready;
    memory_req_t mem_req;
    logic        mem_rsp_valid;
    logic        mem_rsp_ready;
    memory_rsp_t mem_rsp;

    // Instantiate the D-Cache Unit
    dcache #(
        .DCACHE_SIZE(DEFAULT_L1_DCACHE_SIZE),
        .DCACHE_LINE_SIZE(DEFAULT_L1_DCACHE_LINE_SIZE),
        .DCACHE_WAYS(DEFAULT_L1_DCACHE_WAYS)
    ) uut (
        .clk_i(clk),
        .rst_ni(rst_n),

        .req_valid_i(req_valid),
        .req_ready_o(req_ready),
        .req_addr_i(req_addr),
        .req_write_i(req_write),
        .req_wdata_i(req_wdata),
        .req_wstrb_i(req_wstrb),
        .rsp_valid_o(rsp_valid),
        .rsp_ready_i(rsp_ready),
        .rsp_rdata_o(rsp_rdata),
        .rsp_error_o(rsp_error),

        .mem_req_valid_o(mem_req_valid),
        .mem_req_ready_i(mem_req_ready),
        .mem_req_o(mem_req),
        .mem_rsp_valid_i(mem_rsp_valid),
        .mem_rsp_ready_o(mem_rsp_ready),
        .mem_rsp_i(mem_rsp)
    );

    // Simple Behavioral Memory Model
    word_t main_memory [1024]; // 4KB memory

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < 1024; i++) begin
                main_memory[i] <= '0;
            end
        end else begin
            if (mem_req_valid && mem_req_ready) begin
                if (mem_req.write) begin
                    // Write to memory
                    main_memory[mem_req.addr / (XLEN/8)] <= mem_req.data;
                end else begin
                    // Read from memory (simulate latency)
                    #10; // Simulate memory access latency
                    mem_rsp.data <= main_memory[mem_req.addr / (XLEN/8)];
                    mem_rsp.valid <= 1'b1;
                    mem_rsp.error <= 1'b0;
                    mem_rsp.id <= mem_req.id;
                end
            end else if (mem_rsp_valid && mem_rsp_ready) begin
                mem_rsp.valid <= 1'b0;
            }
        end
    end

    assign mem_req_ready = 1'b1; // Always ready to accept memory requests

    // Clock Generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period (100MHz)
    end

    // Test Stimulus
    initial begin
        $display("\n--------------------------------------------------");
        $display("Starting D-Cache Testbench");
        $display("--------------------------------------------------");

        // Initialize signals
        rst_n = 0;
        req_valid = 0;
        req_addr = '0;
        req_write = 0;
        req_wdata = '0;
        req_wstrb = '0;
        rsp_ready = 0;
        mem_rsp = '0;

        #10; // Wait for a bit
        rst_n = 1; // Release reset
        $display("Reset released.");

        // --- Test Scenario 1: Write to address 0x0 (Miss, then Allocate) ---
        $display("\n--- Test Scenario 1: Write to address 0x0 (Miss, then Allocate) ---");
        req_valid = 1;
        req_addr = 32'h0000_0000;
        req_write = 1;
        req_wdata = 32'hDEADBEEF;
        req_wstrb = 4'b1111;
        rsp_ready = 1;
        #10; // Request cycle
        wait(rsp_valid && rsp_ready); // Wait for response
        $display("Write 0xDEADBEEF to 0x0. Response Valid: %b, Error: %b", rsp_valid, rsp_error);
        req_valid = 0;
        rsp_ready = 0;
        #10;

        // --- Test Scenario 2: Read from address 0x0 (Hit) ---
        $display("\n--- Test Scenario 2: Read from address 0x0 (Hit) ---");
        req_valid = 1;
        req_addr = 32'h0000_0000;
        req_write = 0;
        req_wdata = '0;
        req_wstrb = '0;
        rsp_ready = 1;
        #10; // Request cycle
        wait(rsp_valid && rsp_ready); // Wait for response
        $display("Read from 0x0. Data: %h, Response Valid: %b, Error: %b", rsp_rdata, rsp_valid, rsp_error);
        req_valid = 0;
        rsp_ready = 0;
        #10;

        // --- Test Scenario 3: Read from address 0x100 (Miss, Clean Eviction) ---
        $display("\n--- Test Scenario 3: Read from address 0x100 (Miss, Clean Eviction) ---");
        req_valid = 1;
        req_addr = 32'h0000_0100;
        req_write = 0;
        rsp_ready = 1;
        #10; // Request cycle
        wait(rsp_valid && rsp_ready); // Wait for response
        $display("Read from 0x100. Data: %h, Response Valid: %b, Error: %b", rsp_rdata, rsp_valid, rsp_error);
        req_valid = 0;
        rsp_ready = 0;
        #10;

        // --- Test Scenario 4: Write to address 0x200 (Miss, Dirty Eviction) ---
        // First, make 0x0000_0000 dirty again
        $display("\n--- Test Scenario 4: Write to address 0x200 (Miss, Dirty Eviction) ---");
        req_valid = 1;
        req_addr = 32'h0000_0000;
        req_write = 1;
        req_wdata = 32'hCAFEBABE;
        req_wstrb = 4'b1111;
        rsp_ready = 1;
        #10; wait(rsp_valid && rsp_ready); req_valid = 0; rsp_ready = 0; #10;
        $display("Made 0x0000_0000 dirty.");

        // Now, request 0x200, which will evict 0x0000_0000 (assuming direct-mapped and same index)
        req_valid = 1;
        req_addr = 32'h0000_0200;
        req_write = 1;
        req_wdata = 32'h12345678;
        req_wstrb = 4'b1111;
        rsp_ready = 1;
        #10; wait(rsp_valid && rsp_ready); req_valid = 0; rsp_ready = 0; #10;
        $display("Write 0x12345678 to 0x200. Response Valid: %b, Error: %b", rsp_valid, rsp_error);

        $display("\n--------------------------------------------------");
        $display("D-Cache Testbench Finished");
        $display("--------------------------------------------------");
        $finish;
    end

endmodule : dcache_tb
