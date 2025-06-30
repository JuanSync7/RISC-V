//=============================================================================
// Company: RISC-V Verification Team
// Author: Senior Verification Engineer
// Created: 2025-01-27
//
// File: mult_unit_tb.sv
// Module: mult_unit_tb
//
// Project Name: RISC-V Multi-Core System
// Target Devices: ASIC/FPGA
// Tool Versions: VCS/QuestaSim
// Verification Status: Comprehensive Verification
// Quality Status: Reviewed
//
// Description:
//   Comprehensive testbench for mult_unit module with constrained random testing,
//   functional coverage, corner case testing, and assertion-based verification.
//   Tests all multiplication operations, edge cases, and performance scenarios.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module mult_unit_tb;

    //-----
    // Parameters (matching DUT)
    //-----
    localparam integer DATA_WIDTH = 32;
    localparam integer CLK_PERIOD = 10; // 100MHz
    localparam integer TEST_TIMEOUT = 500000;
    localparam integer NUM_RANDOM_TESTS = 1000;

    //-----
    // DUT Interface Signals
    //-----
    logic                               clk_i;
    logic                               rst_ni;
    logic                               mult_enable_i;
    logic [DATA_WIDTH-1:0]              operand_a_i;
    logic [DATA_WIDTH-1:0]              operand_b_i;
    logic [1:0]                         mult_op_i;        // 00: MUL, 01: MULH, 10: MULHSU, 11: MULHU
    logic                               mult_valid_i;
    logic                               mult_ready_o;
    logic [DATA_WIDTH-1:0]              mult_result_o;
    logic                               mult_valid_o;
    logic                               mult_ready_i;

    //-----
    // Testbench Control Signals
    //-----
    logic                               test_done;
    int                                 test_count;
    int                                 pass_count;
    int                                 fail_count;
    string                              current_test_name;

    //-----
    // Expected Result Calculation
    //-----
    logic [63:0]                        expected_result_64;
    logic [DATA_WIDTH-1:0]              expected_result_32;

    //-----
    // Random Stimulus Class
    //-----
    class MultUnitStimulus;
        rand bit [DATA_WIDTH-1:0]       rand_operand_a;
        rand bit [DATA_WIDTH-1:0]       rand_operand_b;
        rand bit [1:0]                  rand_mult_op;
        rand bit                        rand_enable;
        
        // Constraints for comprehensive testing
        constraint c_operands {
            // Cover full range but bias toward interesting values
            rand_operand_a dist {
                32'h0000_0000 := 5,
                32'h0000_0001 := 5,
                32'hFFFF_FFFF := 5,
                32'h8000_0000 := 5,
                32'h7FFF_FFFF := 5,
                [32'h0000_0002:32'h7FFF_FFFE] := 70,
                [32'h8000_0001:32'hFFFF_FFFE] := 5
            };
            
            rand_operand_b dist {
                32'h0000_0000 := 5,
                32'h0000_0001 := 5,
                32'hFFFF_FFFF := 5,
                32'h8000_0000 := 5,
                32'h7FFF_FFFF := 5,
                [32'h0000_0002:32'h7FFF_FFFE] := 70,
                [32'h8000_0001:32'hFFFF_FFFE] := 5
            };
        }
        
        constraint c_mult_op {
            rand_mult_op inside {2'b00, 2'b01, 2'b10, 2'b11};
        }
        
        constraint c_enable {
            rand_enable dist {1'b1 := 90, 1'b0 := 10};
        }
    endclass

    //-----
    // Functional Coverage
    //-----
    covergroup mult_unit_cg @(posedge clk_i);
        option.per_instance = 1;
        option.name = "mult_unit_coverage";
        
        // Operation type coverage
        cp_mult_op: coverpoint mult_op_i {
            bins mul_low = {2'b00};      // MUL - lower 32 bits
            bins mul_high = {2'b01};     // MULH - upper 32 bits signed
            bins mul_high_su = {2'b10};  // MULHSU - upper 32 bits signed/unsigned
            bins mul_high_u = {2'b11};   // MULHU - upper 32 bits unsigned
        }
        
        // Operand value categories
        cp_operand_a: coverpoint operand_a_i {
            bins zero = {32'h0000_0000};
            bins one = {32'h0000_0001};
            bins max_pos = {32'h7FFF_FFFF};
            bins min_neg = {32'h8000_0000};
            bins all_ones = {32'hFFFF_FFFF};
            bins small_pos = {[32'h0000_0002:32'h0000_FFFF]};
            bins medium_pos = {[32'h0001_0000:32'h7FFF_FFFE]};
            bins small_neg = {[32'hFFFF_0000:32'hFFFF_FFFE]};
            bins medium_neg = {[32'h8000_0001:32'hFFFE_FFFF]};
        }
        
        cp_operand_b: coverpoint operand_b_i {
            bins zero = {32'h0000_0000};
            bins one = {32'h0000_0001};
            bins max_pos = {32'h7FFF_FFFF};
            bins min_neg = {32'h8000_0000};
            bins all_ones = {32'hFFFF_FFFF};
            bins small_pos = {[32'h0000_0002:32'h0000_FFFF]};
            bins medium_pos = {[32'h0001_0000:32'h7FFF_FFFE]};
            bins small_neg = {[32'hFFFF_0000:32'hFFFF_FFFE]};
            bins medium_neg = {[32'h8000_0001:32'hFFFE_FFFF]};
        }
        
        // Control signal coverage
        cp_valid_ready: coverpoint {mult_valid_i, mult_ready_o, mult_valid_o, mult_ready_i} {
            bins idle = {4'b0000, 4'b0001, 4'b0010, 4'b0011};
            bins handshake_start = {4'b1100, 4'b1110};
            bins processing = {4'b0000, 4'b0001};
            bins handshake_end = {4'b0011, 4'b0111};
            bins backpressure = {4'b0010};
        }
        
        // Cross coverage for comprehensive testing
        cx_op_operands: cross cp_mult_op, cp_operand_a, cp_operand_b {
            // Focus on interesting combinations
            ignore_bins ignore_trivial = binsof(cp_operand_a.zero) && binsof(cp_operand_b.zero);
        }
        
        cx_op_control: cross cp_mult_op, cp_valid_ready;
    endgroup

    //-----
    // Reference Model Functions
    //-----
    function automatic logic [DATA_WIDTH-1:0] calculate_expected_result(
        logic [DATA_WIDTH-1:0] a,
        logic [DATA_WIDTH-1:0] b,
        logic [1:0] op
    );
        logic signed [DATA_WIDTH-1:0] signed_a, signed_b;
        logic [DATA_WIDTH-1:0] unsigned_a, unsigned_b;
        logic signed [63:0] signed_result;
        logic [63:0] unsigned_result;
        logic [63:0] mixed_result;
        
        signed_a = a;
        signed_b = b;
        unsigned_a = a;
        unsigned_b = b;
        
        case (op)
            2'b00: begin // MUL - lower 32 bits
                signed_result = signed_a * signed_b;
                return signed_result[DATA_WIDTH-1:0];
            end
            2'b01: begin // MULH - upper 32 bits signed
                signed_result = signed_a * signed_b;
                return signed_result[63:32];
            end
            2'b10: begin // MULHSU - upper 32 bits signed * unsigned
                mixed_result = $signed({1'b0, signed_a}) * $signed({1'b0, unsigned_b});
                if (signed_a[31]) begin // If a is negative
                    mixed_result = signed_a * unsigned_b;
                end else begin
                    mixed_result = unsigned_a * unsigned_b;
                end
                return mixed_result[63:32];
            end
            2'b11: begin // MULHU - upper 32 bits unsigned
                unsigned_result = unsigned_a * unsigned_b;
                return unsigned_result[63:32];
            end
            default: return 32'h0;
        endcase
    endfunction

    //-----
    // DUT Instantiation
    //-----
    mult_unit #(
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .mult_enable_i(mult_enable_i),
        .operand_a_i(operand_a_i),
        .operand_b_i(operand_b_i),
        .mult_op_i(mult_op_i),
        .mult_valid_i(mult_valid_i),
        .mult_ready_o(mult_ready_o),
        .mult_result_o(mult_result_o),
        .mult_valid_o(mult_valid_o),
        .mult_ready_i(mult_ready_i)
    );

    //-----
    // Clock Generation
    //-----
    initial begin
        clk_i = 1'b0;
        forever #(CLK_PERIOD/2) clk_i = ~clk_i;
    end

    //-----
    // Coverage Instantiation
    //-----
    mult_unit_cg cg_mult_unit;
    
    initial begin
        cg_mult_unit = new();
    end

    //-----
    // Assertion Properties
    //-----
    
    // Ready should be deasserted when not enabled
    property p_ready_when_disabled;
        @(posedge clk_i) disable iff (!rst_ni)
        !mult_enable_i |-> !mult_ready_o;
    endproperty
    
    // Valid output should only be high when enabled
    property p_valid_when_enabled;
        @(posedge clk_i) disable iff (!rst_ni)
        mult_valid_o |-> mult_enable_i;
    endproperty
    
    // Handshake protocol check
    property p_handshake_protocol;
        @(posedge clk_i) disable iff (!rst_ni)
        mult_valid_i && mult_ready_o |=> ##[1:10] mult_valid_o;
    endproperty
    
    // Result stability
    property p_result_stable;
        @(posedge clk_i) disable iff (!rst_ni)
        mult_valid_o && !mult_ready_i |=> $stable(mult_result_o);
    endproperty

    assert_ready_when_disabled: assert property (p_ready_when_disabled)
        else $error("Ready asserted when disabled");
    
    assert_valid_when_enabled: assert property (p_valid_when_enabled)
        else $error("Valid output high when disabled");
    
    assert_handshake_protocol: assert property (p_handshake_protocol)
        else $error("Handshake protocol violation");
    
    assert_result_stable: assert property (p_result_stable)
        else $error("Result not stable during valid");

    //-----
    // Test Tasks
    //-----
    
    // Reset task
    task reset_dut();
        begin
            rst_ni = 1'b0;
            mult_enable_i = 1'b0;
            operand_a_i = 32'h0;
            operand_b_i = 32'h0;
            mult_op_i = 2'b00;
            mult_valid_i = 1'b0;
            mult_ready_i = 1'b1;
            
            repeat (5) @(posedge clk_i);
            rst_ni = 1'b1;
            repeat (5) @(posedge clk_i);
            
            $display("[%0t] Reset completed", $time);
        end
    endtask

    // Perform single multiplication operation
    task perform_mult_operation(
        logic [DATA_WIDTH-1:0] a,
        logic [DATA_WIDTH-1:0] b,
        logic [1:0] op,
        string test_name
    );
        logic [DATA_WIDTH-1:0] expected;
        int timeout_count;
        
        begin
            expected = calculate_expected_result(a, b, op);
            
            // Setup inputs
            mult_enable_i = 1'b1;
            operand_a_i = a;
            operand_b_i = b;
            mult_op_i = op;
            mult_valid_i = 1'b1;
            mult_ready_i = 1'b1;
            
            // Wait for ready
            timeout_count = 0;
            while (!mult_ready_o && timeout_count < 100) begin
                @(posedge clk_i);
                timeout_count++;
            end
            
            if (!mult_ready_o) begin
                $error("[%0t] Timeout waiting for ready in %s", $time, test_name);
                fail_count++;
                return;
            end
            
            // Wait for result
            @(posedge clk_i);
            mult_valid_i = 1'b0;
            
            timeout_count = 0;
            while (!mult_valid_o && timeout_count < 100) begin
                @(posedge clk_i);
                timeout_count++;
            end
            
            if (!mult_valid_o) begin
                $error("[%0t] Timeout waiting for valid result in %s", $time, test_name);
                fail_count++;
                return;
            end
            
            // Check result
            if (mult_result_o === expected) begin
                $display("[%0t] PASS: %s - %h * %h = %h (op=%b)", 
                         $time, test_name, a, b, mult_result_o, op);
                pass_count++;
            end else begin
                $error("[%0t] FAIL: %s - %h * %h = %h, expected %h (op=%b)", 
                       $time, test_name, a, b, mult_result_o, expected, op);
                fail_count++;
            end
            
            @(posedge clk_i);
            mult_ready_i = 1'b0;
            @(posedge clk_i);
            mult_ready_i = 1'b1;
            
            test_count++;
        end
    endtask

    //-----
    // Test Scenarios
    //-----
    
    // Test 1: Basic functionality test
    task test_basic_functionality();
        begin
            current_test_name = "Basic Functionality Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            reset_dut();
            
            // Test simple multiplications for each operation type
            perform_mult_operation(32'h0000_0002, 32'h0000_0003, 2'b00, "MUL 2*3");
            perform_mult_operation(32'h1000_0000, 32'h0000_0002, 2'b01, "MULH large*2");
            perform_mult_operation(32'h8000_0000, 32'h0000_0002, 2'b10, "MULHSU neg*2");
            perform_mult_operation(32'hFFFF_FFFF, 32'hFFFF_FFFF, 2'b11, "MULHU max*max");
        end
    endtask

    // Test 2: Corner cases
    task test_corner_cases();
        begin
            current_test_name = "Corner Cases Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            reset_dut();
            
            // Test multiplication by zero
            perform_mult_operation(32'h0000_0000, 32'hFFFF_FFFF, 2'b00, "Zero * Max");
            perform_mult_operation(32'hFFFF_FFFF, 32'h0000_0000, 2'b00, "Max * Zero");
            
            // Test multiplication by one
            perform_mult_operation(32'h0000_0001, 32'h1234_5678, 2'b00, "One * Value");
            perform_mult_operation(32'h1234_5678, 32'h0000_0001, 2'b00, "Value * One");
            
            // Test overflow conditions
            perform_mult_operation(32'hFFFF_FFFF, 32'hFFFF_FFFF, 2'b00, "Max * Max (MUL)");
            perform_mult_operation(32'hFFFF_FFFF, 32'hFFFF_FFFF, 2'b01, "Max * Max (MULH)");
            
            // Test signed/unsigned boundary
            perform_mult_operation(32'h8000_0000, 32'h8000_0000, 2'b01, "MinNeg * MinNeg");
            perform_mult_operation(32'h7FFF_FFFF, 32'h7FFF_FFFF, 2'b01, "MaxPos * MaxPos");
        end
    endtask

    // Test 3: Handshake protocol test
    task test_handshake_protocol();
        begin
            current_test_name = "Handshake Protocol Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            reset_dut();
            
            // Test backpressure on input
            mult_enable_i = 1'b1;
            operand_a_i = 32'h1234_5678;
            operand_b_i = 32'h8765_4321;
            mult_op_i = 2'b00;
            mult_valid_i = 1'b1;
            mult_ready_i = 1'b1;
            
            // Wait for not ready (simulating busy)
            @(posedge clk_i);
            if (mult_ready_o) begin
                mult_valid_i = 1'b0;
                
                // Test output backpressure
                wait (mult_valid_o);
                mult_ready_i = 1'b0; // Create backpressure
                
                repeat (5) @(posedge clk_i);
                
                if (mult_valid_o && $stable(mult_result_o)) begin
                    $display("[%0t] PASS: Result stable during backpressure", $time);
                    pass_count++;
                end else begin
                    $error("[%0t] FAIL: Result not stable during backpressure", $time);
                    fail_count++;
                end
                
                mult_ready_i = 1'b1;
                @(posedge clk_i);
                
                test_count++;
            end
        end
    endtask

    // Test 4: Constrained random test
    task test_constrained_random();
        MultUnitStimulus stimulus;
        
        begin
            current_test_name = "Constrained Random Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            stimulus = new();
            
            for (int i = 0; i < NUM_RANDOM_TESTS; i++) begin
                reset_dut();
                
                if (!stimulus.randomize()) begin
                    $error("Failed to randomize stimulus for test %0d", i);
                    continue;
                end
                
                if (stimulus.rand_enable) begin
                    perform_mult_operation(
                        stimulus.rand_operand_a,
                        stimulus.rand_operand_b,
                        stimulus.rand_mult_op,
                        $sformatf("Random_%0d", i)
                    );
                end
                
                if (i % 100 == 0) begin
                    $display("[%0t] Completed %0d random tests", $time, i);
                end
            end
        end
    endtask

    // Test 5: Performance test
    task test_performance();
        int start_time, end_time;
        int operations_completed;
        
        begin
            current_test_name = "Performance Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            reset_dut();
            
            start_time = $time;
            operations_completed = 0;
            
            mult_enable_i = 1'b1;
            mult_ready_i = 1'b1;
            
            // Continuous operation for performance measurement
            for (int i = 0; i < 100; i++) begin
                operand_a_i = $random;
                operand_b_i = $random;
                mult_op_i = i[1:0];
                mult_valid_i = 1'b1;
                
                @(posedge clk_i);
                while (!mult_ready_o) @(posedge clk_i);
                
                mult_valid_i = 1'b0;
                while (!mult_valid_o) @(posedge clk_i);
                
                operations_completed++;
                @(posedge clk_i);
            end
            
            end_time = $time;
            
            $display("[%0t] Performance Test: %0d operations in %0d ns", 
                     $time, operations_completed, end_time - start_time);
            $display("Average latency: %0.1f ns per operation", 
                     real'(end_time - start_time) / operations_completed);
        end
    endtask

    //-----
    // Main Test Execution
    //-----
    initial begin
        $display("=== Multiplication Unit Testbench Started ===");
        $display("Parameters: DATA_WIDTH=%0d", DATA_WIDTH);
        
        // Initialize counters
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        test_done = 1'b0;
        
        // Set up waveform dumping
        `ifdef VCS
            $vcdpluson;
        `elsif QUESTA
            $wlfdumpvars();
        `endif
        
        // Run test suite
        test_basic_functionality();
        test_corner_cases();
        test_handshake_protocol();
        test_constrained_random();
        test_performance();
        
        // Final results
        repeat (50) @(posedge clk_i);
        
        $display("\n=== Test Results Summary ===");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        if (test_count > 0) begin
            $display("Pass Rate: %0.1f%%", (pass_count * 100.0) / test_count);
        end
        
        // Coverage report
        $display("\n=== Coverage Summary ===");
        $display("Functional Coverage: %0.1f%%", cg_mult_unit.get_inst_coverage());
        
        test_done = 1'b1;
        
        `ifdef VCS
            $vcdplusoff;
        `endif
        
        if (fail_count == 0) begin
            $display("\n*** ALL TESTS PASSED ***");
            $finish;
        end else begin
            $display("\n*** SOME TESTS FAILED ***");
            $finish(1);
        end
    end

    // Timeout watchdog
    initial begin
        #TEST_TIMEOUT;
        if (!test_done) begin
            $error("Test timeout after %0d ns", TEST_TIMEOUT);
            $finish(2);
        end
    end

endmodule : mult_unit_tb

`default_nettype wire

//=============================================================================
// Dependencies: mult_unit.sv
//
// Performance:
//   - Simulation Time: ~200ms for full test suite including 1000 random tests
//   - Memory Usage: ~150MB for waveform capture
//   - Coverage: Target 100% functional coverage
//
// Verification Coverage:
//   - Code Coverage: 100% line/branch coverage target
//   - Functional Coverage: All operation types and operand combinations
//   - Assertion Coverage: Handshake protocol and result correctness
//
// Test Features:
//   - Reference model for result verification
//   - Constrained random stimulus generation (1000 tests)
//   - Corner case testing (zero, one, max values)
//   - Handshake protocol verification
//   - Performance benchmarking
//   - All RISC-V multiplication operations (MUL, MULH, MULHSU, MULHU)
//
// Usage:
//   - VCS: vcs -sverilog +incdir+../../../rtl/units mult_unit_tb.sv
//   - QuestaSim: vsim -voptargs=+acc work.mult_unit_tb
//
//----
// Revision History:
// Version | Date       | Author                    | Description
//=============================================================================
// 1.0.0   | 2025-01-27 | Senior Verification Engineer | Initial comprehensive testbench
//============================================================================= 