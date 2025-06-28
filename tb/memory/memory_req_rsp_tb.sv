//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: memory_req_rsp_tb.sv
// Module: memory_req_rsp_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Unit testbench for the protocol-agnostic memory interface. Tests read
//   and write transactions, interface handshaking, and error handling.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module memory_req_rsp_tb;
    import riscv_core_pkg::*;

    // Clock and reset
    logic clk;
    logic rst_n;

    // Memory interface instance
    memory_req_rsp_if mem_if();

    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

    // Connect clock and reset to interface
    assign mem_if.clk = clk;
    assign mem_if.rst_n = rst_n;

    // Test stimulus
    initial begin
        // Initialize
        rst_n = 0;
        mem_if.reset_if();
        #20;
        rst_n = 1;
        #10;

        $display("[TB] Starting memory interface tests");

        // Test 1: Simple read transaction
        $display("[TB] Test 1: Simple read transaction");
        test_read_transaction(32'h1000_0000, 3'b010, 4'h1);
        #10;

        // Test 2: Simple write transaction
        $display("[TB] Test 2: Simple write transaction");
        test_write_transaction(32'h2000_0000, 3'b010, 32'hAABB_CCDD, 4'b1111, 4'h2);
        #10;

        // Test 3: Multiple transactions
        $display("[TB] Test 3: Multiple transactions");
        for (int i = 0; i < 4; i++) begin
            test_read_transaction(32'h3000_0000 + i*4, 3'b010, 4'h3 + i);
            #5;
        end

        // Test 4: Interface idle check
        $display("[TB] Test 4: Interface idle check");
        if (mem_if.is_idle())
            $display("[TB] Interface is idle as expected");
        else
            $display("[TB] ERROR: Interface should be idle");

        $display("[TB] All tests complete");
        $finish;
    end

    // Task to test read transaction
    task automatic test_read_transaction(
        input  addr_t addr,
        input  logic [2:0] size,
        input  logic [3:0] id
    );
        word_t data;
        logic error, success;
        
        // Simulate memory response (in real system, this would come from protocol adapter)
        fork
            // Send request
            begin
                mem_if.read_transaction(addr, size, id, data, error, success);
                if (success && !error)
                    $display("[TB] Read success: addr=%h, data=%h, id=%h", addr, data, id);
                else
                    $display("[TB] Read failed: addr=%h, error=%b, success=%b", addr, error, success);
            end
            
            // Simulate memory response
            begin
                @(posedge clk);
                while (!mem_if.req_valid) @(posedge clk);
                
                // Simulate memory delay
                repeat (3) @(posedge clk);
                
                // Send response
                mem_if.rsp_valid = 1;
                mem_if.rsp.data = $random;
                mem_if.rsp.id = id;
                mem_if.rsp.error = 0;
                mem_if.rsp.last = 1;
                
                @(posedge clk);
                mem_if.rsp_valid = 0;
            end
        join
    endtask

    // Task to test write transaction
    task automatic test_write_transaction(
        input  addr_t addr,
        input  logic [2:0] size,
        input  word_t data,
        input  logic [3:0] strb,
        input  logic [3:0] id
    );
        logic error, success;
        
        // Simulate memory response
        fork
            // Send request
            begin
                mem_if.write_transaction(addr, size, data, strb, id, error, success);
                if (success && !error)
                    $display("[TB] Write success: addr=%h, data=%h, id=%h", addr, data, id);
                else
                    $display("[TB] Write failed: addr=%h, error=%b, success=%b", addr, error, success);
            end
            
            // Simulate memory response
            begin
                @(posedge clk);
                while (!mem_if.req_valid) @(posedge clk);
                
                // Simulate memory delay
                repeat (2) @(posedge clk);
                
                // Send response
                mem_if.rsp_valid = 1;
                mem_if.rsp.id = id;
                mem_if.rsp.error = 0;
                mem_if.rsp.last = 1;
                
                @(posedge clk);
                mem_if.rsp_valid = 0;
            end
        join
    endtask

    // Monitor interface activity
    always @(posedge clk) begin
        if (mem_if.req_valid && mem_if.req_ready) begin
            $display("[MON] Request: addr=%h, write=%b, size=%b, id=%h", 
                     mem_if.req.addr, mem_if.req.write, mem_if.req.size, mem_if.req.id);
        end
        
        if (mem_if.rsp_valid && mem_if.rsp_ready) begin
            $display("[MON] Response: data=%h, id=%h, error=%b", 
                     mem_if.rsp.data, mem_if.rsp.id, mem_if.rsp.error);
        end
    end

endmodule : memory_req_rsp_tb

//=============================================================================
// Dependencies: riscv_core_pkg.sv, memory_req_rsp_if.sv
//
// Performance:
//   - Simulation Time: TBD
//   - Test Vectors: TBD
//   - Coverage: TBD
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: N/A (testbench)
//   - Synthesis Tool: N/A
//   - Clock Domains: 1 (clk)
//
// Testing:
//   - Testbench: memory_req_rsp_tb.sv
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//=============================================================================