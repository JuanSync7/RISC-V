//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: riscv_core_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: riscv_core_tb
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-29
// DESCRIPTION: Basic testbench for RISC-V core verification.
// PRIMARY_PURPOSE: Demonstrate core functionality with simple test programs.
// ROLE_IN_SYSTEM: Top-level testbench for simulation and verification.
// PROBLEM_SOLVED: Provides test infrastructure for RISC-V core validation.
// MODULE_TYPE: Testbench
// TARGET_TECHNOLOGY_PREF: Simulation
// RELATED_SPECIFICATION: RISC-V ISA Tests
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Basic
// QUALITY_STATUS: Example
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

module riscv_core_tb;

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    parameter CLK_PERIOD = 10;  // 10ns = 100MHz
    parameter TIMEOUT_CYCLES = 10000;
    parameter MEM_SIZE = 65536; // 64KB memory
    
    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    logic clk;
    logic rst_n;
    
    // Instruction memory interface
    logic        imem_req;
    logic [31:0] imem_addr;
    logic [31:0] imem_rdata;
    logic        imem_ready;
    
    // Data memory interface
    logic        dmem_req;
    logic        dmem_we;
    logic [31:0] dmem_addr;
    logic [31:0] dmem_wdata;
    logic [3:0]  dmem_be;
    logic [31:0] dmem_rdata;
    logic        dmem_ready;
    
    // Interrupts
    logic        irq_software;
    logic        irq_timer;
    logic        irq_external;
    
    // Test control
    integer      cycle_count;
    integer      instr_count;
    logic        test_pass;
    string       test_name;
    
    //-------------------------------------------------------------------------
    // Memory Model
    //-------------------------------------------------------------------------
    logic [7:0] memory [MEM_SIZE];
    
    // Initialize memory with test program
    initial begin
        // Clear memory
        for (int i = 0; i < MEM_SIZE; i++) begin
            memory[i] = 8'h00;
        end
        
        // Load test program based on test selection
        if ($test$plusargs("test_name=%s", test_name)) begin
            $display("Loading test: %s", test_name);
            $readmemh({test_name, ".hex"}, memory);
        end else begin
            // Default test program - simple add immediate
            load_default_program();
        end
    end
    
    //-------------------------------------------------------------------------
    // Clock Generation
    //-------------------------------------------------------------------------
    initial begin
        clk = 1'b0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    //-------------------------------------------------------------------------
    // DUT Instantiation
    //-------------------------------------------------------------------------
    riscv_core #(
        .RESET_VECTOR(32'h0000_0000)
    ) u_dut (
        .clk_i          (clk),
        .rst_ni         (rst_n),
        
        // Instruction memory
        .imem_req_o     (imem_req),
        .imem_addr_o    (imem_addr),
        .imem_rdata_i   (imem_rdata),
        .imem_ready_i   (imem_ready),
        
        // Data memory
        .dmem_req_o     (dmem_req),
        .dmem_we_o      (dmem_we),
        .dmem_addr_o    (dmem_addr),
        .dmem_wdata_o   (dmem_wdata),
        .dmem_be_o      (dmem_be),
        .dmem_rdata_i   (dmem_rdata),
        .dmem_ready_i   (dmem_ready),
        
        // Interrupts
        .irq_software_i (irq_software),
        .irq_timer_i    (irq_timer),
        .irq_external_i (irq_external)
    );
    
    //-------------------------------------------------------------------------
    // Instruction Memory Model
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            imem_rdata <= 32'h0;
            imem_ready <= 1'b0;
        end else begin
            if (imem_req && imem_addr < MEM_SIZE) begin
                imem_rdata <= {memory[imem_addr+3], memory[imem_addr+2], 
                               memory[imem_addr+1], memory[imem_addr]};
                imem_ready <= 1'b1;
            end else begin
                imem_ready <= 1'b0;
            end
        end
    end
    
    //-------------------------------------------------------------------------
    // Data Memory Model
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dmem_rdata <= 32'h0;
            dmem_ready <= 1'b0;
        end else begin
            if (dmem_req) begin
                if (dmem_we) begin
                    // Write operation
                    if (dmem_addr < MEM_SIZE) begin
                        if (dmem_be[0]) memory[dmem_addr]   <= dmem_wdata[7:0];
                        if (dmem_be[1]) memory[dmem_addr+1] <= dmem_wdata[15:8];
                        if (dmem_be[2]) memory[dmem_addr+2] <= dmem_wdata[23:16];
                        if (dmem_be[3]) memory[dmem_addr+3] <= dmem_wdata[31:24];
                    end
                    dmem_ready <= 1'b1;
                end else begin
                    // Read operation
                    if (dmem_addr < MEM_SIZE) begin
                        dmem_rdata <= {memory[dmem_addr+3], memory[dmem_addr+2],
                                       memory[dmem_addr+1], memory[dmem_addr]};
                    end else begin
                        dmem_rdata <= 32'hDEADBEEF; // Invalid address
                    end
                    dmem_ready <= 1'b1;
                end
            end else begin
                dmem_ready <= 1'b0;
            end
        end
    end
    
    //-------------------------------------------------------------------------
    // Test Stimulus
    //-------------------------------------------------------------------------
    initial begin
        // Initialize signals
        rst_n = 1'b0;
        irq_software = 1'b0;
        irq_timer = 1'b0;
        irq_external = 1'b0;
        cycle_count = 0;
        instr_count = 0;
        test_pass = 1'b0;
        
        // Dump waveforms if requested
        if ($test$plusargs("dump_vcd")) begin
            $dumpfile("riscv_core_tb.vcd");
            $dumpvars(0, riscv_core_tb);
        end
        
        // Reset sequence
        $display("=== RISC-V Core Testbench ===");
        $display("Time: %0t - Asserting reset", $time);
        repeat(10) @(posedge clk);
        rst_n = 1'b1;
        $display("Time: %0t - Reset released", $time);
        
        // Run test
        fork
            // Monitor instruction execution
            monitor_execution();
            
            // Timeout watchdog
            begin
                repeat(TIMEOUT_CYCLES) @(posedge clk);
                $display("ERROR: Test timeout after %0d cycles", TIMEOUT_CYCLES);
                $finish(1);
            end
            
            // Wait for test completion
            wait_for_completion();
        join_any
        
        // Report results
        report_results();
        
        $finish(0);
    end
    
    //-------------------------------------------------------------------------
    // Monitor Tasks
    //-------------------------------------------------------------------------
    task monitor_execution();
        forever begin
            @(posedge clk);
            if (rst_n) begin
                cycle_count++;
                
                // Count instructions
                if (imem_req && imem_ready) begin
                    instr_count++;
                    if ($test$plusargs("trace")) begin
                        $display("PC: %08h  Instr: %08h", imem_addr, imem_rdata);
                    end
                end
                
                // Check for special addresses (test markers)
                if (dmem_req && dmem_we) begin
                    case (dmem_addr)
                        32'h1000_0000: begin  // Test pass marker
                            $display("TEST PASSED at cycle %0d", cycle_count);
                            test_pass = 1'b1;
                            -> test_done;
                        end
                        32'h1000_0004: begin  // Test fail marker
                            $display("TEST FAILED with code %0d at cycle %0d", 
                                     dmem_wdata, cycle_count);
                            test_pass = 1'b0;
                            -> test_done;
                        end
                        32'h1000_0008: begin  // Print character
                            $write("%c", dmem_wdata[7:0]);
                        end
                        32'h1000_000C: begin  // Print hex value
                            $display("Value: 0x%08h", dmem_wdata);
                        end
                    endcase
                end
            end
        end
    endtask
    
    event test_done;
    
    task wait_for_completion();
        @(test_done);
    endtask
    
    task report_results();
        $display("\n=== Test Results ===");
        $display("Test: %s", test_name);
        $display("Status: %s", test_pass ? "PASSED" : "FAILED");
        $display("Cycles: %0d", cycle_count);
        $display("Instructions: %0d", instr_count);
        $display("IPC: %.2f", real'(instr_count) / real'(cycle_count));
        $display("===================\n");
    endtask
    
    //-------------------------------------------------------------------------
    // Default Test Program
    //-------------------------------------------------------------------------
    task load_default_program();
        // Simple test: Add immediate and store result
        // x1 = 0 + 10
        // x2 = x1 + 20
        // x3 = x2 + 30
        // Store x3 to test pass address
        
        // addi x1, x0, 10
        {memory[3], memory[2], memory[1], memory[0]} = 32'h00A00093;
        
        // addi x2, x1, 20
        {memory[7], memory[6], memory[5], memory[4]} = 32'h01408113;
        
        // addi x3, x2, 30
        {memory[11], memory[10], memory[9], memory[8]} = 32'h01E10193;
        
        // lui x4, 0x10000
        {memory[15], memory[14], memory[13], memory[12]} = 32'h10000237;
        
        // sw x3, 0(x4)  # Store to pass marker
        {memory[19], memory[18], memory[17], memory[16]} = 32'h00322023;
        
        // Infinite loop: j .
        {memory[23], memory[22], memory[21], memory[20]} = 32'h0000006F;
        
        $display("Loaded default test program");
    endtask
    
    //-------------------------------------------------------------------------
    // Interrupt Generation (Optional)
    //-------------------------------------------------------------------------
    initial begin
        if ($test$plusargs("test_interrupts")) begin
            // Generate timer interrupt every 1000 cycles
            forever begin
                repeat(1000) @(posedge clk);
                if (rst_n) begin
                    irq_timer = 1'b1;
                    @(posedge clk);
                    irq_timer = 1'b0;
                end
            end
        end
    end

endmodule : riscv_core_tb

//=============================================================================
// Test Programs
//=============================================================================
// Create test programs as separate .hex files:
//
// test_add.hex - Test ADD instructions
// test_branch.hex - Test branch instructions
// test_load_store.hex - Test memory operations
// test_multiply.hex - Test M extension
// test_csr.hex - Test CSR operations
// test_interrupt.hex - Test interrupt handling
//
// Run with: vsim riscv_core_tb +test_name=test_add +dump_vcd
//=============================================================================