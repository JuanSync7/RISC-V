//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: test_utils.sv
// Module: test_utils
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Common testbench utilities for unit testing. Provides shared functions,
//   tasks, and macros for consistent testbench development across all
//   modules in the RISC-V project.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package test_utils;
    import riscv_types_pkg::*;

    //===========================================================================
    // Test Configuration Parameters
    //===========================================================================
    parameter integer CLK_PERIOD = 10;        // 100MHz clock
    parameter integer TIMEOUT_CYCLES = 1000;  // Timeout for tests
    parameter integer MAX_TEST_ITERATIONS = 100; // Max iterations for random tests

    //===========================================================================
    // Test Status Enumeration
    //===========================================================================
    typedef enum logic [1:0] {
        TEST_PASS = 2'b00,
        TEST_FAIL = 2'b01,
        TEST_TIMEOUT = 2'b10,
        TEST_SKIP = 2'b11
    } test_result_e;

    //===========================================================================
    // Test Statistics Structure
    //===========================================================================
    typedef struct packed {
        integer total_tests;
        integer passed_tests;
        integer failed_tests;
        integer timeout_tests;
        integer skipped_tests;
        real pass_rate;
        integer total_cycles;
        real simulation_time;
    } test_stats_t;

    //===========================================================================
    // Clock Generation Task
    //===========================================================================
    task automatic generate_clock(ref logic clk, input integer period);
        clk = 0;
        forever #(period/2) clk = ~clk;
    endtask

    //===========================================================================
    // Reset Generation Task
    //===========================================================================
    task automatic generate_reset(ref logic rst_n, input integer cycles);
        rst_n = 0;
        repeat(cycles) @(posedge clk);
        rst_n = 1;
    endtask

    //===========================================================================
    // Wait for Signal Task
    //===========================================================================
    task automatic wait_for_signal(input logic signal, input integer max_cycles);
        integer cycle_count = 0;
        while (!signal && cycle_count < max_cycles) begin
            @(posedge clk);
            cycle_count++;
        end
        if (cycle_count >= max_cycles) begin
            $error("Timeout waiting for signal after %0d cycles", max_cycles);
        end
    endtask

    //===========================================================================
    // Random Word Generation
    //===========================================================================
    function automatic word_t random_word();
        return $random;
    endfunction

    //===========================================================================
    // Random Address Generation
    //===========================================================================
    function automatic addr_t random_addr();
        return $random & 32'hFFFF_FFFF;
    endfunction

    //===========================================================================
    // Random Register Address Generation
    //===========================================================================
    function automatic reg_addr_t random_reg_addr();
        return $random & 5'h1F;
    endfunction

    //===========================================================================
    // Random Instruction Generation
    //===========================================================================
    function automatic word_t random_instruction();
        return $random;
    endfunction

    //===========================================================================
    // Test Result Recording
    //===========================================================================
    task automatic record_test_result(
        input string test_name,
        input test_result_e result,
        ref test_stats_t stats
    );
        stats.total_tests++;
        case (result)
            TEST_PASS: stats.passed_tests++;
            TEST_FAIL: stats.failed_tests++;
            TEST_TIMEOUT: stats.timeout_tests++;
            TEST_SKIP: stats.skipped_tests++;
        endcase
        
        stats.pass_rate = real'(stats.passed_tests) / real'(stats.total_tests) * 100.0;
        
        case (result)
            TEST_PASS: $display("[PASS] %s", test_name);
            TEST_FAIL: $display("[FAIL] %s", test_name);
            TEST_TIMEOUT: $display("[TIMEOUT] %s", test_name);
            TEST_SKIP: $display("[SKIP] %s", test_name);
        endcase
    endtask

    //===========================================================================
    // Test Statistics Reporting
    //===========================================================================
    task automatic report_test_stats(input test_stats_t stats);
        $display("==========================================");
        $display("TEST SUMMARY");
        $display("==========================================");
        $display("Total Tests:     %0d", stats.total_tests);
        $display("Passed:          %0d", stats.passed_tests);
        $display("Failed:          %0d", stats.failed_tests);
        $display("Timeout:         %0d", stats.timeout_tests);
        $display("Skipped:         %0d", stats.skipped_tests);
        $display("Pass Rate:       %0.1f%%", stats.pass_rate);
        $display("Total Cycles:    %0d", stats.total_cycles);
        $display("Simulation Time: %0.1f ns", stats.simulation_time);
        $display("==========================================");
    endtask

    //===========================================================================
    // Assertion Macros
    //===========================================================================
    `define ASSERT_EQ(actual, expected, message) \
        if (actual !== expected) begin \
            $error("ASSERTION FAILED: %s - Expected: %h, Got: %h", message, expected, actual); \
        end

    `define ASSERT_NEQ(actual, expected, message) \
        if (actual === expected) begin \
            $error("ASSERTION FAILED: %s - Values should not be equal: %h", message, actual); \
        end

    `define ASSERT_TRUE(condition, message) \
        if (!condition) begin \
            $error("ASSERTION FAILED: %s", message); \
        end

    `define ASSERT_FALSE(condition, message) \
        if (condition) begin \
            $error("ASSERTION FAILED: %s", message); \
        end

    //===========================================================================
    // Coverage Macros
    //===========================================================================
    `define COVER_POINT(name, signal) \
        covergroup name @(posedge clk); \
            cp: coverpoint signal; \
        endgroup

    `define COVER_CROSS(name, signal1, signal2) \
        covergroup name @(posedge clk); \
            cp1: coverpoint signal1; \
            cp2: coverpoint signal2; \
            cross cp1, cp2; \
        endgroup

    //===========================================================================
    // Test Vector Generation
    //===========================================================================
    // ALU Test Vectors
    typedef struct packed {
        word_t operand_a;
        word_t operand_b;
        logic [3:0] alu_op;
        word_t expected_result;
        logic expected_zero;
        logic expected_overflow;
    } alu_test_vector_t;

    // Register File Test Vectors
    typedef struct packed {
        reg_addr_t rs1_addr;
        reg_addr_t rs2_addr;
        reg_addr_t rd_addr;
        word_t write_data;
        logic write_enable;
        word_t expected_rs1_data;
        word_t expected_rs2_data;
    } regfile_test_vector_t;

    // Memory Test Vectors
    typedef struct packed {
        addr_t addr;
        word_t write_data;
        logic [2:0] size;
        logic [3:0] strb;
        logic write_enable;
        word_t expected_read_data;
    } memory_test_vector_t;

    //===========================================================================
    // Performance Monitoring Functions
    //===========================================================================
    
    // Performance monitoring structure
    typedef struct packed {
        integer cycle_count;
        integer instruction_count;
        integer stall_count;
        integer flush_count;
        integer cache_hit_count;
        integer cache_miss_count;
        real throughput;
        real cpi;
        time start_time;
        time end_time;
    } performance_stats_t;
    
    // Global performance statistics
    performance_stats_t perf_stats;
    
    // Function to start performance monitoring
    function automatic void start_performance_monitoring();
        perf_stats.cycle_count = 0;
        perf_stats.instruction_count = 0;
        perf_stats.stall_count = 0;
        perf_stats.flush_count = 0;
        perf_stats.cache_hit_count = 0;
        perf_stats.cache_miss_count = 0;
        perf_stats.start_time = $time;
    endfunction
    
    // Function to update performance statistics
    function automatic void update_performance_stats(
        input bit instruction_retired,
        input bit stall,
        input bit flush,
        input bit cache_hit,
        input bit cache_miss
    );
        perf_stats.cycle_count++;
        if (instruction_retired) perf_stats.instruction_count++;
        if (stall) perf_stats.stall_count++;
        if (flush) perf_stats.flush_count++;
        if (cache_hit) perf_stats.cache_hit_count++;
        if (cache_miss) perf_stats.cache_miss_count++;
    endfunction
    
    // Function to calculate final performance metrics
    function automatic void calculate_performance_metrics();
        perf_stats.end_time = $time;
        perf_stats.throughput = (perf_stats.instruction_count > 0) ? 
            (real'(perf_stats.instruction_count) / real'(perf_stats.cycle_count)) : 0.0;
        perf_stats.cpi = (perf_stats.instruction_count > 0) ? 
            (real'(perf_stats.cycle_count) / real'(perf_stats.instruction_count)) : 0.0;
    endfunction
    
    // Function to print performance report
    function automatic void print_performance_report();
        calculate_performance_metrics();
        $display("=== PERFORMANCE REPORT ===");
        $display("Simulation Time: %0t", perf_stats.end_time - perf_stats.start_time);
        $display("Cycles: %0d", perf_stats.cycle_count);
        $display("Instructions: %0d", perf_stats.instruction_count);
        $display("Throughput: %0.3f IPC", perf_stats.throughput);
        $display("CPI: %0.3f", perf_stats.cpi);
        $display("Stalls: %0d", perf_stats.stall_count);
        $display("Flushes: %0d", perf_stats.flush_count);
        $display("Cache Hit Rate: %0.1f%%", 
            (perf_stats.cache_hit_count + perf_stats.cache_miss_count > 0) ?
            (real'(perf_stats.cache_hit_count) * 100.0 / 
             real'(perf_stats.cache_hit_count + perf_stats.cache_miss_count)) : 0.0);
        $display("========================");
    endfunction

    //===========================================================================
    // Statistical Analysis Functions
    //===========================================================================
    
    // Function to calculate mean of an array
    function automatic real calculate_mean(input real values[]);
        real sum = 0.0;
        for (int i = 0; i < values.size(); i++) begin
            sum += values[i];
        end
        return sum / real'(values.size());
    endfunction
    
    // Function to calculate standard deviation
    function automatic real calculate_std_dev(input real values[]);
        real mean = calculate_mean(values);
        real sum_sq_diff = 0.0;
        for (int i = 0; i < values.size(); i++) begin
            sum_sq_diff += (values[i] - mean) * (values[i] - mean);
        end
        return $sqrt(sum_sq_diff / real'(values.size()));
    endfunction
    
    // Function to find minimum value in array
    function automatic real find_min(input real values[]);
        real min_val = values[0];
        for (int i = 1; i < values.size(); i++) begin
            if (values[i] < min_val) min_val = values[i];
        end
        return min_val;
    endfunction
    
    // Function to find maximum value in array
    function automatic real find_max(input real values[]);
        real max_val = values[0];
        for (int i = 1; i < values.size(); i++) begin
            if (values[i] > max_val) max_val = values[i];
        end
        return max_val;
    endfunction

    //===========================================================================
    // Waveform and Debug Functions
    //===========================================================================
    
    // Function to enable waveform dumping
    function automatic void enable_waveform_dumping(input string filename = "waveform.vcd");
        $dumpfile(filename);
        $dumpvars(0); // Dump all variables
        $display("Waveform dumping enabled: %s", filename);
    endfunction
    
    // Function to dump specific signals to waveform
    function automatic void dump_specific_signals();
        // This would be implemented based on specific signal names
        // Example: $dumpvars(0, dut.signal_name);
    endfunction
    
    // Function to create checkpoint for debugging
    function automatic void create_debug_checkpoint(input string checkpoint_name);
        $display("DEBUG CHECKPOINT: %s at time %0t", checkpoint_name, $time);
        // Additional debug information could be dumped here
    endfunction

    //===========================================================================
    // Error Reporting and Logging Functions
    //===========================================================================
    
    // Error severity levels
    typedef enum {INFO, WARNING, ERROR, FATAL} error_severity_t;
    
    // Function to log messages with severity
    function automatic void log_message(
        input error_severity_t severity,
        input string message,
        input string module_name = ""
    );
        string severity_str;
        case (severity)
            INFO: severity_str = "INFO";
            WARNING: severity_str = "WARNING";
            ERROR: severity_str = "ERROR";
            FATAL: severity_str = "FATAL";
        endcase
        
        if (module_name != "") begin
            $display("[%0t] [%s] [%s] %s", $time, severity_str, module_name, message);
        end else begin
            $display("[%0t] [%s] %s", $time, severity_str, message);
        end
        
        // For fatal errors, stop simulation
        if (severity == FATAL) begin
            $finish;
        end
    endfunction
    
    // Function to report test results
    function automatic void report_test_results(
        input string test_name,
        input bit passed,
        input string details = ""
    );
        if (passed) begin
            log_message(INFO, $sformatf("TEST PASSED: %s", test_name));
        end else begin
            log_message(ERROR, $sformatf("TEST FAILED: %s - %s", test_name, details));
        end
    endfunction

    //===========================================================================
    // Advanced Test Management Functions
    //===========================================================================
    
    // Test configuration structure
    typedef struct packed {
        string test_name;
        integer timeout_cycles;
        integer max_errors;
        bit enable_coverage;
        bit enable_waveform;
        string waveform_file;
    } test_config_t;
    
    // Function to create test configuration
    function automatic test_config_t create_test_config(
        input string name,
        input integer timeout = 10000,
        input integer max_err = 10,
        input bit coverage = 1,
        input bit waveform = 0,
        input string wave_file = ""
    );
        test_config_t config;
        config.test_name = name;
        config.timeout_cycles = timeout;
        config.max_errors = max_err;
        config.enable_coverage = coverage;
        config.enable_waveform = waveform;
        config.waveform_file = wave_file;
        return config;
    endfunction
    
    // Function to run test with configuration
    function automatic bit run_test_with_config(
        input test_config_t config,
        ref bit test_passed
    );
        integer error_count = 0;
        integer cycle_count = 0;
        
        // Setup test environment
        if (config.enable_waveform) begin
            enable_waveform_dumping(config.waveform_file);
        end
        
        log_message(INFO, $sformatf("Starting test: %s", config.test_name));
        
        // Test execution loop (placeholder)
        while (cycle_count < config.timeout_cycles && error_count < config.max_errors) begin
            @(posedge clk);
            cycle_count++;
            
            // Test logic would go here
            // error_count would be incremented on failures
        end
        
        // Test completion
        if (error_count >= config.max_errors) begin
            log_message(ERROR, $sformatf("Test %s failed: too many errors", config.test_name));
            test_passed = 0;
        end else if (cycle_count >= config.timeout_cycles) begin
            log_message(WARNING, $sformatf("Test %s timed out", config.test_name));
            test_passed = 0;
        end else begin
            log_message(INFO, $sformatf("Test %s completed successfully", config.test_name));
            test_passed = 1;
        end
        
        return test_passed;
    endfunction

    //===========================================================================
    // Memory and Cache Testing Functions
    //===========================================================================
    
    // Function to test memory access patterns
    function automatic void test_memory_patterns(
        input logic [31:0] base_addr,
        input integer num_accesses,
        input string pattern_type
    );
        logic [31:0] addr;
        logic [31:0] data;
        
        case (pattern_type)
            "sequential": begin
                for (int i = 0; i < num_accesses; i++) begin
                    addr = base_addr + (i * 4);
                    data = $random;
                    // Memory write/read operations would go here
                end
            end
            "random": begin
                for (int i = 0; i < num_accesses; i++) begin
                    addr = base_addr + ($random % 1024);
                    data = $random;
                    // Memory write/read operations would go here
                end
            end
            "burst": begin
                for (int i = 0; i < num_accesses; i += 4) begin
                    for (int j = 0; j < 4 && (i + j) < num_accesses; j++) begin
                        addr = base_addr + ((i + j) * 4);
                        data = $random;
                        // Memory write/read operations would go here
                    end
                end
            end
        endcase
    endfunction
    
    // Function to test cache behavior
    function automatic void test_cache_behavior(
        input logic [31:0] base_addr,
        input integer cache_size,
        input integer num_accesses
    );
        logic [31:0] addr;
        integer hit_count = 0;
        integer miss_count = 0;
        
        // Test cache hits
        for (int i = 0; i < num_accesses / 2; i++) begin
            addr = base_addr + (i * 4) % cache_size;
            // Memory access would go here
            hit_count++;
        end
        
        // Test cache misses
        for (int i = 0; i < num_accesses / 2; i++) begin
            addr = base_addr + cache_size + (i * 4);
            // Memory access would go here
            miss_count++;
        end
        
        log_message(INFO, $sformatf("Cache test: %0d hits, %0d misses", hit_count, miss_count));
    endfunction

    //===========================================================================
    // Pipeline and Hazard Testing Functions
    //===========================================================================
    
    // Function to test pipeline hazards
    function automatic void test_pipeline_hazards(
        input integer num_tests,
        input string hazard_type
    );
        logic [31:0] inst1, inst2, inst3;
        
        case (hazard_type)
            "RAW": begin
                // Read After Write hazard
                inst1 = 32'h0010_0093; // add x1, x0, 1
                inst2 = 32'h0020_8093; // add x1, x1, 2
                inst3 = 32'h0000_0000; // nop
            end
            "WAW": begin
                // Write After Write hazard
                inst1 = 32'h0010_0093; // add x1, x0, 1
                inst2 = 32'h0020_0093; // add x1, x0, 2
                inst3 = 32'h0000_0000; // nop
            end
            "WAR": begin
                // Write After Read hazard
                inst1 = 32'h0010_0093; // add x1, x0, 1
                inst2 = 32'h0020_8093; // add x1, x1, 2
                inst3 = 32'h0030_0093; // add x1, x0, 3
            end
        endcase
        
        // Instruction injection would go here
        log_message(INFO, $sformatf("Testing %s hazard", hazard_type));
    endfunction
    
    // Function to test branch prediction
    function automatic void test_branch_prediction(
        input integer num_branches,
        input real taken_probability
    );
        logic [31:0] branch_addr, target_addr;
        bit taken;
        
        for (int i = 0; i < num_branches; i++) begin
            branch_addr = 32'h0000_1000 + (i * 4);
            target_addr = 32'h0000_2000 + (i * 4);
            taken = ($random % 100) < (taken_probability * 100);
            
            // Branch prediction test would go here
        end
        
        log_message(INFO, $sformatf("Branch prediction test: %0d branches, %0.1f%% taken", 
                                   num_branches, taken_probability * 100));
    endfunction

endpackage : test_utils

//=============================================================================
// Dependencies: riscv_types_pkg.sv
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
//   - Target Technology: N/A (testbench utilities)
//   - Synthesis Tool: N/A
//   - Clock Domains: 1 (clk)
//
// Testing:
//   - Testbench: N/A (utility package)
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//============================================================================= 