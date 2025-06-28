////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-28
// Design Name:   RV32IM Core
// Module Name:   memory_wrapper_tb
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   Testbench for the memory wrapper module.
//                Tests both instruction and data memory interfaces
//                with AXI4 protocol adapter.
//
// Dependencies:  memory_wrapper.sv, axi4_adapter.sv, memory_req_rsp_if.sv
//
// Revision:
// Revision 1.0.0 - File Created
// Additional Comments:
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps
`default_nettype none

module memory_wrapper_tb;

    // AI_TAG: TESTBENCH_PARAMETERS - Test configuration
    localparam integer CLK_PERIOD = 10; // 100MHz
    localparam integer TIMEOUT = 10000; // 10us timeout
    localparam integer NUM_TESTS = 100;
    
    // AI_TAG: TESTBENCH_SIGNALS - Clock and reset
    logic clk;
    logic rst_n;
    
    // AI_TAG: TESTBENCH_SIGNALS - Instruction memory interface
    logic        instr_req_valid;
    logic        instr_req_ready;
    addr_t       instr_req_addr;
    logic        instr_rsp_valid;
    logic        instr_rsp_ready;
    word_t       instr_rsp_data;
    logic        instr_rsp_error;
    
    // AI_TAG: TESTBENCH_SIGNALS - Data memory interface
    logic        data_req_valid;
    logic        data_req_ready;
    addr_t       data_req_addr;
    logic        data_req_write;
    logic [2:0]  data_req_size;
    word_t       data_req_data;
    logic [3:0]  data_req_strb;
    logic        data_rsp_valid;
    logic        data_rsp_ready;
    word_t       data_rsp_data;
    logic        data_rsp_error;
    
    // AI_TAG: TESTBENCH_SIGNALS - AXI4 interface (simulated memory)
    // Instruction Memory AXI4
    logic        i_arvalid;
    logic        i_arready;
    addr_t       i_araddr;
    logic [2:0]  i_arprot;
    logic [3:0]  i_arcache;
    logic [1:0]  i_arsize;
    word_t       i_rdata;
    logic        i_rvalid;
    logic        i_rready;
    
    // Data Memory AXI4
    logic        d_awvalid;
    logic        d_awready;
    addr_t       d_awaddr;
    logic [2:0]  d_awprot;
    logic        d_wvalid;
    logic        d_wready;
    word_t       d_wdata;
    logic [3:0]  d_wstrb;
    logic        d_bvalid;
    logic        d_bready;
    logic        d_arvalid;
    logic        d_arready;
    addr_t       d_araddr;
    logic [2:0]  d_arprot;
    logic        d_rvalid;
    logic        d_rready;
    word_t       d_rdata;
    
    // AI_TAG: TESTBENCH_SIGNALS - Test control
    integer test_count;
    integer error_count;
    logic test_done;
    
    // AI_TAG: TESTBENCH_INSTANTIATION - Memory wrapper under test
    memory_wrapper #(
        .PROTOCOL_TYPE("AXI4")
    ) u_memory_wrapper (
        .clk_i(clk),
        .rst_ni(rst_n),
        
        // Instruction memory interface
        .instr_req_valid_i(instr_req_valid),
        .instr_req_ready_o(instr_req_ready),
        .instr_req_addr_i(instr_req_addr),
        .instr_rsp_valid_o(instr_rsp_valid),
        .instr_rsp_ready_i(instr_rsp_ready),
        .instr_rsp_data_o(instr_rsp_data),
        .instr_rsp_error_o(instr_rsp_error),
        
        // Data memory interface
        .data_req_valid_i(data_req_valid),
        .data_req_ready_o(data_req_ready),
        .data_req_addr_i(data_req_addr),
        .data_req_write_i(data_req_write),
        .data_req_size_i(data_req_size),
        .data_req_data_i(data_req_data),
        .data_req_strb_i(data_req_strb),
        .data_rsp_valid_o(data_rsp_valid),
        .data_rsp_ready_i(data_rsp_ready),
        .data_rsp_data_o(data_rsp_data),
        .data_rsp_error_o(data_rsp_error),
        
        // AXI4 interface
        .i_arvalid_o(i_arvalid),
        .i_arready_i(i_arready),
        .i_araddr_o(i_araddr),
        .i_arprot_o(i_arprot),
        .i_arcache_o(i_arcache),
        .i_arsize_o(i_arsize),
        .i_rdata_i(i_rdata),
        .i_rvalid_i(i_rvalid),
        .i_rready_o(i_rready),
        .d_awvalid_o(d_awvalid),
        .d_awready_i(d_awready),
        .d_awaddr_o(d_awaddr),
        .d_awprot_o(d_awprot),
        .d_wvalid_o(d_wvalid),
        .d_wready_i(d_wready),
        .d_wdata_o(d_wdata),
        .d_wstrb_o(d_wstrb),
        .d_bvalid_i(d_bvalid),
        .d_bready_o(d_bready),
        .d_arvalid_o(d_arvalid),
        .d_arready_i(d_arready),
        .d_araddr_o(d_araddr),
        .d_arprot_o(d_arprot),
        .d_rvalid_i(d_rvalid),
        .d_rready_o(d_rready),
        .d_rdata_i(d_rdata)
    );
    
    // AI_TAG: TESTBENCH_INSTANTIATION - Simulated memory model
    axi4_memory_model u_axi4_memory (
        .clk_i(clk),
        .rst_ni(rst_n),
        
        // Instruction memory AXI4
        .i_arvalid_i(i_arvalid),
        .i_arready_o(i_arready),
        .i_araddr_i(i_araddr),
        .i_arprot_i(i_arprot),
        .i_arcache_i(i_arcache),
        .i_arsize_i(i_arsize),
        .i_rdata_o(i_rdata),
        .i_rvalid_o(i_rvalid),
        .i_rready_i(i_rready),
        
        // Data memory AXI4
        .d_awvalid_i(d_awvalid),
        .d_awready_o(d_awready),
        .d_awaddr_i(d_awaddr),
        .d_awprot_i(d_awprot),
        .d_wvalid_i(d_wvalid),
        .d_wready_o(d_wready),
        .d_wdata_i(d_wdata),
        .d_wstrb_i(d_wstrb),
        .d_bvalid_o(d_bvalid),
        .d_bready_i(d_bready),
        .d_arvalid_i(d_arvalid),
        .d_arready_o(d_arready),
        .d_araddr_i(d_araddr),
        .d_arprot_i(d_arprot),
        .d_rvalid_o(d_rvalid),
        .d_rready_i(d_rready),
        .d_rdata_o(d_rdata)
    );
    
    // AI_TAG: TESTBENCH_LOGIC - Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // AI_TAG: TESTBENCH_LOGIC - Reset generation
    initial begin
        rst_n = 0;
        #(CLK_PERIOD * 10);
        rst_n = 1;
    end
    
    // AI_TAG: TESTBENCH_LOGIC - Test stimulus
    initial begin
        // Initialize test signals
        instr_req_valid = 0;
        instr_req_addr = '0;
        instr_rsp_ready = 1;
        data_req_valid = 0;
        data_req_addr = '0;
        data_req_write = 0;
        data_req_size = '0;
        data_req_data = '0;
        data_req_strb = '0;
        data_rsp_ready = 1;
        
        test_count = 0;
        error_count = 0;
        test_done = 0;
        
        // Wait for reset
        wait(rst_n);
        #(CLK_PERIOD * 5);
        
        $display("=== Memory Wrapper Testbench Started ===");
        
        // Run tests
        run_instruction_tests();
        run_data_tests();
        run_concurrent_tests();
        run_error_tests();
        
        // Test summary
        $display("=== Test Summary ===");
        $display("Total tests: %0d", test_count);
        $display("Errors: %0d", error_count);
        $display("Success rate: %0.1f%%", (test_count - error_count) * 100.0 / test_count);
        
        if (error_count == 0) begin
            $display("✅ All tests passed!");
        end else begin
            $display("❌ %0d tests failed!", error_count);
        end
        
        test_done = 1;
        #(CLK_PERIOD * 10);
        $finish;
    end
    
    // AI_TAG: TESTBENCH_TASKS - Instruction memory tests
    task run_instruction_tests();
        $display("Running instruction memory tests...");
        
        // Test 1: Basic instruction fetch
        test_instruction_fetch(32'h0000_0000, 32'h1234_5678);
        test_instruction_fetch(32'h0000_0004, 32'h9ABC_DEF0);
        test_instruction_fetch(32'h0000_0008, 32'h5555_AAAA);
        
        // Test 2: Sequential instruction fetches
        for (int i = 0; i < 10; i++) begin
            test_instruction_fetch(32'h1000_0000 + i*4, 32'h1000_0000 + i);
        end
        
        // Test 3: Random instruction fetches
        for (int i = 0; i < 20; i++) begin
            addr_t addr = $random();
            word_t data = $random();
            test_instruction_fetch(addr, data);
        end
    endtask
    
    // AI_TAG: TESTBENCH_TASKS - Data memory tests
    task run_data_tests();
        $display("Running data memory tests...");
        
        // Test 1: Basic read/write operations
        test_data_write(32'h2000_0000, 32'hDEAD_BEEF, 3'b010, 4'b1111);
        test_data_read(32'h2000_0000, 32'hDEAD_BEEF, 3'b010);
        
        test_data_write(32'h2000_0004, 32'hCAFE_BABE, 3'b010, 4'b1111);
        test_data_read(32'h2000_0004, 32'hCAFE_BABE, 3'b010);
        
        // Test 2: Byte operations
        test_data_write(32'h2000_0008, 32'h0000_00AB, 3'b000, 4'b0001);
        test_data_read(32'h2000_0008, 32'h0000_00AB, 3'b000);
        
        // Test 3: Half-word operations
        test_data_write(32'h2000_000C, 32'h0000_CDEF, 3'b001, 4'b0011);
        test_data_read(32'h2000_000C, 32'h0000_CDEF, 3'b001);
        
        // Test 4: Random data operations
        for (int i = 0; i < 15; i++) begin
            addr_t addr = $random();
            word_t data = $random();
            logic [2:0] size = $random() % 3;
            logic [3:0] strb = (size == 0) ? 4'b0001 : (size == 1) ? 4'b0011 : 4'b1111;
            test_data_write(addr, data, size, strb);
            test_data_read(addr, data, size);
        end
    endtask
    
    // AI_TAG: TESTBENCH_TASKS - Concurrent tests
    task run_concurrent_tests();
        $display("Running concurrent instruction and data tests...");
        
        // Test concurrent instruction and data access
        fork
            // Instruction fetches
            for (int i = 0; i < 5; i++) begin
                test_instruction_fetch(32'h3000_0000 + i*4, 32'h3000_0000 + i);
            end
            // Data operations
            for (int i = 0; i < 5; i++) begin
                test_data_write(32'h4000_0000 + i*4, 32'h4000_0000 + i, 3'b010, 4'b1111);
                test_data_read(32'h4000_0000 + i*4, 32'h4000_0000 + i, 3'b010);
            end
        join
        
        $display("Concurrent tests completed");
    endtask
    
    // AI_TAG: TESTBENCH_TASKS - Error tests
    task run_error_tests();
        $display("Running error condition tests...");
        
        // Test 1: Invalid addresses (should not cause errors in this simple model)
        test_instruction_fetch(32'hFFFF_FFFF, 32'h0000_0000);
        test_data_read(32'hFFFF_FFFF, 32'h0000_0000, 3'b010);
        
        // Test 2: Back-to-back requests
        instr_req_valid = 1;
        instr_req_addr = 32'h5000_0000;
        #(CLK_PERIOD);
        instr_req_addr = 32'h5000_0004;
        #(CLK_PERIOD);
        instr_req_valid = 0;
        
        data_req_valid = 1;
        data_req_addr = 32'h6000_0000;
        data_req_write = 1;
        data_req_data = 32'h1111_1111;
        data_req_size = 3'b010;
        data_req_strb = 4'b1111;
        #(CLK_PERIOD);
        data_req_addr = 32'h6000_0004;
        data_req_data = 32'h2222_2222;
        #(CLK_PERIOD);
        data_req_valid = 0;
        
        $display("Error condition tests completed");
    endtask
    
    // AI_TAG: TESTBENCH_TASKS - Individual test tasks
    task test_instruction_fetch(input addr_t addr, input word_t expected_data);
        test_count++;
        
        // Send instruction request
        @(posedge clk);
        instr_req_valid = 1;
        instr_req_addr = addr;
        
        // Wait for request accepted
        @(posedge clk);
        while (!instr_req_ready) @(posedge clk);
        instr_req_valid = 0;
        
        // Wait for response
        while (!instr_rsp_valid) @(posedge clk);
        
        // Check response
        if (instr_rsp_data !== expected_data) begin
            $display("❌ Instruction fetch error at addr 0x%08X: expected 0x%08X, got 0x%08X", 
                     addr, expected_data, instr_rsp_data);
            error_count++;
        end else begin
            $display("✅ Instruction fetch at addr 0x%08X: 0x%08X", addr, instr_rsp_data);
        end
        
        @(posedge clk);
    endtask
    
    task test_data_write(input addr_t addr, input word_t data, input logic [2:0] size, input logic [3:0] strb);
        test_count++;
        
        // Send write request
        @(posedge clk);
        data_req_valid = 1;
        data_req_addr = addr;
        data_req_write = 1;
        data_req_data = data;
        data_req_size = size;
        data_req_strb = strb;
        
        // Wait for request accepted
        @(posedge clk);
        while (!data_req_ready) @(posedge clk);
        data_req_valid = 0;
        
        // Wait for write response
        while (!data_rsp_valid) @(posedge clk);
        
        if (data_rsp_error) begin
            $display("❌ Data write error at addr 0x%08X", addr);
            error_count++;
        end else begin
            $display("✅ Data write at addr 0x%08X: 0x%08X", addr, data);
        end
        
        @(posedge clk);
    endtask
    
    task test_data_read(input addr_t addr, input word_t expected_data, input logic [2:0] size);
        test_count++;
        
        // Send read request
        @(posedge clk);
        data_req_valid = 1;
        data_req_addr = addr;
        data_req_write = 0;
        data_req_size = size;
        data_req_data = '0;
        data_req_strb = '0;
        
        // Wait for request accepted
        @(posedge clk);
        while (!data_req_ready) @(posedge clk);
        data_req_valid = 0;
        
        // Wait for response
        while (!data_rsp_valid) @(posedge clk);
        
        // Check response
        if (data_rsp_data !== expected_data) begin
            $display("❌ Data read error at addr 0x%08X: expected 0x%08X, got 0x%08X", 
                     addr, expected_data, data_rsp_data);
            error_count++;
        end else begin
            $display("✅ Data read at addr 0x%08X: 0x%08X", addr, data_rsp_data);
        end
        
        @(posedge clk);
    endtask
    
    // AI_TAG: TESTBENCH_MONITORING - Timeout monitoring
    initial begin
        #(TIMEOUT * CLK_PERIOD);
        if (!test_done) begin
            $display("❌ Testbench timeout!");
            $finish;
        end
    end

endmodule : memory_wrapper_tb

// AI_TAG: TESTBENCH_MODULE - Simple AXI4 memory model
module axi4_memory_model (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Instruction memory AXI4
    input  logic        i_arvalid_i,
    output logic        i_arready_o,
    input  addr_t       i_araddr_i,
    input  logic [2:0]  i_arprot_i,
    input  logic [3:0]  i_arcache_i,
    input  logic [1:0]  i_arsize_i,
    output word_t       i_rdata_o,
    output logic        i_rvalid_o,
    input  logic        i_rready_i,
    
    // Data memory AXI4
    input  logic        d_awvalid_i,
    output logic        d_awready_o,
    input  addr_t       d_awaddr_i,
    input  logic [2:0]  d_awprot_i,
    input  logic        d_wvalid_i,
    output logic        d_wready_o,
    input  word_t       d_wdata_i,
    input  logic [3:0]  d_wstrb_i,
    output logic        d_bvalid_o,
    input  logic        d_bready_i,
    input  logic        d_arvalid_i,
    output logic        d_arready_o,
    input  addr_t       d_araddr_i,
    input  logic [2:0]  d_arprot_i,
    output logic        d_rvalid_o,
    input  logic        d_rready_i,
    output word_t       d_rdata_o
);
    
    // AI_TAG: INTERNAL_STORAGE - Memory array
    word_t memory [0:1023]; // 4KB memory
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 handshake logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            i_arready_o <= 1'b0;
            i_rvalid_o <= 1'b0;
            i_rdata_o <= '0;
            d_awready_o <= 1'b0;
            d_wready_o <= 1'b0;
            d_bvalid_o <= 1'b0;
            d_arready_o <= 1'b0;
            d_rvalid_o <= 1'b0;
            d_rdata_o <= '0;
        end else begin
            // Instruction read handshake
            if (i_arvalid_i && i_arready_o) begin
                i_arready_o <= 1'b0;
                i_rvalid_o <= 1'b1;
                i_rdata_o <= memory[i_araddr_i[11:2]]; // Word-aligned access
            end else if (i_rvalid_o && i_rready_i) begin
                i_rvalid_o <= 1'b0;
                i_arready_o <= 1'b1;
            end else if (!i_arready_o && !i_rvalid_o) begin
                i_arready_o <= 1'b1;
            end
            
            // Data write handshake
            if (d_awvalid_i && d_awready_o) begin
                d_awready_o <= 1'b0;
            end else if (d_wvalid_i && d_wready_o) begin
                d_wready_o <= 1'b0;
                d_bvalid_o <= 1'b1;
                // Write data to memory
                memory[d_awaddr_i[11:2]] <= d_wdata_i;
            end else if (d_bvalid_o && d_bready_i) begin
                d_bvalid_o <= 1'b0;
                d_awready_o <= 1'b1;
                d_wready_o <= 1'b1;
            end else if (!d_awready_o && !d_wready_o && !d_bvalid_o) begin
                d_awready_o <= 1'b1;
                d_wready_o <= 1'b1;
            end
            
            // Data read handshake
            if (d_arvalid_i && d_arready_o) begin
                d_arready_o <= 1'b0;
                d_rvalid_o <= 1'b1;
                d_rdata_o <= memory[d_araddr_i[11:2]]; // Word-aligned access
            end else if (d_rvalid_o && d_rready_i) begin
                d_rvalid_o <= 1'b0;
                d_arready_o <= 1'b1;
            end else if (!d_arready_o && !d_rvalid_o) begin
                d_arready_o <= 1'b1;
            end
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - Memory initialization
    initial begin
        for (int i = 0; i < 1024; i++) begin
            memory[i] = i; // Initialize with address value
        end
    end

endmodule : axi4_memory_model

`default_nettype wire 