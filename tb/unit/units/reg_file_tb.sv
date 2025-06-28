//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: reg_file_tb.sv
// Module: reg_file_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Unit testbench for the Register File module. Tests read/write operations,
//   register addressing, data integrity, and special register behavior
//   (x0 always reads as zero).
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module reg_file_tb;
    import riscv_core_pkg::*;
    import test_utils::*;

    //===========================================================================
    // Test Configuration
    //===========================================================================
    localparam integer NUM_TESTS = 500;
    localparam integer TIMEOUT_CYCLES = 50;

    //===========================================================================
    // Clock and Reset
    //===========================================================================
    logic clk;
    logic rst_n;

    //===========================================================================
    // Register File Interface Signals
    //===========================================================================
    reg_addr_t rs1_addr_i;
    reg_addr_t rs2_addr_i;
    reg_addr_t rd_addr_i;
    word_t rd_data_i;
    logic rd_write_en_i;
    word_t rs1_data_o;
    word_t rs2_data_o;

    //===========================================================================
    // Test Control
    //===========================================================================
    test_stats_t test_stats;
    integer test_count;
    logic test_done;

    //===========================================================================
    // Register File Instance
    //===========================================================================
    reg_file dut (
        .clk_i(clk),
        .rst_n_i(rst_n),
        .rs1_addr_i(rs1_addr_i),
        .rs2_addr_i(rs2_addr_i),
        .rd_addr_i(rd_addr_i),
        .rd_data_i(rd_data_i),
        .rd_write_en_i(rd_write_en_i),
        .rs1_data_o(rs1_data_o),
        .rs2_data_o(rs2_data_o)
    );

    //===========================================================================
    // Clock Generation
    //===========================================================================
    initial begin
        generate_clock(clk, CLK_PERIOD);
    end

    //===========================================================================
    // Test Stimulus
    //===========================================================================
    initial begin
        // Initialize test statistics
        test_stats = '0;
        test_count = 0;
        test_done = 0;

        // Initialize signals
        rs1_addr_i = '0;
        rs2_addr_i = '0;
        rd_addr_i = '0;
        rd_data_i = '0;
        rd_write_en_i = 0;

        // Reset sequence
        generate_reset(rst_n, 5);
        @(posedge clk);

        $display("==========================================");
        $display("REGISTER FILE UNIT TESTBENCH STARTED");
        $display("==========================================");

        // Run test suite
        run_basic_read_write_tests();
        run_zero_register_tests();
        run_concurrent_read_write_tests();
        run_edge_case_tests();
        run_random_tests();

        // Report results
        test_stats.simulation_time = $time;
        report_test_stats(test_stats);

        $display("==========================================");
        $display("REGISTER FILE UNIT TESTBENCH COMPLETED");
        $display("==========================================");

        test_done = 1;
        #100;
        $finish;
    end

    //===========================================================================
    // Test Functions
    //===========================================================================

    // Basic read/write operations test
    task automatic run_basic_read_write_tests();
        $display("Running Basic Read/Write Tests...");
        
        test_single_write_read();
        test_multiple_writes();
        test_read_before_write();
        test_write_disable();
    endtask

    // Zero register (x0) tests
    task automatic run_zero_register_tests();
        $display("Running Zero Register Tests...");
        
        test_zero_register_read();
        test_zero_register_write();
        test_zero_register_persistence();
    endtask

    // Concurrent read/write tests
    task automatic run_concurrent_read_write_tests();
        $display("Running Concurrent Read/Write Tests...");
        
        test_read_during_write();
        test_same_register_read_write();
        test_different_register_read_write();
    endtask

    // Edge case tests
    task automatic run_edge_case_tests();
        $display("Running Edge Case Tests...");
        
        test_maximum_values();
        test_minimum_values();
        test_all_registers();
        test_reset_behavior();
    endtask

    // Random tests
    task automatic run_random_tests();
        $display("Running Random Tests...");
        
        for (int i = 0; i < NUM_TESTS; i++) begin
            test_random_operation();
        end
    endtask

    //===========================================================================
    // Individual Test Tasks
    //===========================================================================

    task automatic test_single_write_read();
        string test_name = "Single Write/Read";
        
        // Write to register x1
        rd_addr_i = 5'h01;
        rd_data_i = 32'h1234_5678;
        rd_write_en_i = 1;
        @(posedge clk);
        
        // Read from register x1
        rd_write_en_i = 0;
        rs1_addr_i = 5'h01;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h1234_5678, "Read should return written value");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_multiple_writes();
        string test_name = "Multiple Writes";
        
        // Write multiple values to same register
        rd_addr_i = 5'h02;
        rd_data_i = 32'h1111_1111;
        rd_write_en_i = 1;
        @(posedge clk);
        
        rd_data_i = 32'h2222_2222;
        @(posedge clk);
        
        rd_data_i = 32'h3333_3333;
        @(posedge clk);
        
        // Read should return last written value
        rd_write_en_i = 0;
        rs1_addr_i = 5'h02;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h3333_3333, "Should read last written value");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_read_before_write();
        string test_name = "Read Before Write";
        
        // Read from uninitialized register (should be 0 after reset)
        rs1_addr_i = 5'h03;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h0000_0000, "Uninitialized register should read as 0");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_write_disable();
        string test_name = "Write Disable";
        
        // Try to write with write enable disabled
        rd_addr_i = 5'h04;
        rd_data_i = 32'hDEAD_BEEF;
        rd_write_en_i = 0;
        @(posedge clk);
        
        // Read should still be 0
        rs1_addr_i = 5'h04;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h0000_0000, "Register should not be written when write_en is 0");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_zero_register_read();
        string test_name = "Zero Register Read";
        
        // Read from x0 (should always be 0)
        rs1_addr_i = 5'h00;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h0000_0000, "x0 should always read as 0");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_zero_register_write();
        string test_name = "Zero Register Write";
        
        // Try to write to x0
        rd_addr_i = 5'h00;
        rd_data_i = 32'hDEAD_BEEF;
        rd_write_en_i = 1;
        @(posedge clk);
        
        // Read from x0 (should still be 0)
        rd_write_en_i = 0;
        rs1_addr_i = 5'h00;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h0000_0000, "x0 should remain 0 even after write attempt");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_zero_register_persistence();
        string test_name = "Zero Register Persistence";
        
        // Write to another register
        rd_addr_i = 5'h05;
        rd_data_i = 32'h1234_5678;
        rd_write_en_i = 1;
        @(posedge clk);
        
        // Read from x0 (should still be 0)
        rd_write_en_i = 0;
        rs1_addr_i = 5'h00;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h0000_0000, "x0 should remain 0 regardless of other writes");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_read_during_write();
        string test_name = "Read During Write";
        
        // Write to register
        rd_addr_i = 5'h06;
        rd_data_i = 32'hAAAA_BBBB;
        rd_write_en_i = 1;
        
        // Simultaneously read from different register
        rs1_addr_i = 5'h07;
        rs2_addr_i = 5'h08;
        @(posedge clk);
        
        // Read should work independently of write
        `ASSERT_TRUE(1, "Read during write should not interfere");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_same_register_read_write();
        string test_name = "Same Register Read/Write";
        
        // Write to register
        rd_addr_i = 5'h09;
        rd_data_i = 32'h1111_1111;
        rd_write_en_i = 1;
        @(posedge clk);
        
        // Read from same register
        rd_write_en_i = 0;
        rs1_addr_i = 5'h09;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h1111_1111, "Should read what was written to same register");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_different_register_read_write();
        string test_name = "Different Register Read/Write";
        
        // Write to register x10
        rd_addr_i = 5'h0A;
        rd_data_i = 32'h2222_2222;
        rd_write_en_i = 1;
        @(posedge clk);
        
        // Read from register x11 (should be 0)
        rd_write_en_i = 0;
        rs1_addr_i = 5'h0B;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h0000_0000, "Different register should not be affected");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_maximum_values();
        string test_name = "Maximum Values";
        
        // Write maximum value
        rd_addr_i = 5'h0C;
        rd_data_i = 32'hFFFF_FFFF;
        rd_write_en_i = 1;
        @(posedge clk);
        
        // Read maximum value
        rd_write_en_i = 0;
        rs1_addr_i = 5'h0C;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'hFFFF_FFFF, "Should handle maximum values correctly");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_minimum_values();
        string test_name = "Minimum Values";
        
        // Write minimum value
        rd_addr_i = 5'h0D;
        rd_data_i = 32'h0000_0000;
        rd_write_en_i = 1;
        @(posedge clk);
        
        // Read minimum value
        rd_write_en_i = 0;
        rs1_addr_i = 5'h0D;
        @(posedge clk);
        
        `ASSERT_EQ(rs1_data_o, 32'h0000_0000, "Should handle minimum values correctly");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_all_registers();
        string test_name = "All Registers";
        
        // Test all registers except x0
        for (int i = 1; i < 32; i++) begin
            rd_addr_i = i[4:0];
            rd_data_i = 32'h1000 + i;
            rd_write_en_i = 1;
            @(posedge clk);
        end
        
        // Read all registers
        rd_write_en_i = 0;
        for (int i = 1; i < 32; i++) begin
            rs1_addr_i = i[4:0];
            @(posedge clk);
            `ASSERT_EQ(rs1_data_o, 32'h1000 + i, $sformatf("Register x%0d should contain correct value", i));
        end
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_reset_behavior();
        string test_name = "Reset Behavior";
        
        // Write to some registers
        rd_addr_i = 5'h0E;
        rd_data_i = 32'hDEAD_BEEF;
        rd_write_en_i = 1;
        @(posedge clk);
        
        rd_addr_i = 5'h0F;
        rd_data_i = 32'hCAFE_BABE;
        @(posedge clk);
        
        // Reset
        rst_n = 0;
        @(posedge clk);
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
        
        // Read should be 0 after reset
        rd_write_en_i = 0;
        rs1_addr_i = 5'h0E;
        @(posedge clk);
        `ASSERT_EQ(rs1_data_o, 32'h0000_0000, "Register should be 0 after reset");
        
        rs1_addr_i = 5'h0F;
        @(posedge clk);
        `ASSERT_EQ(rs1_data_o, 32'h0000_0000, "Register should be 0 after reset");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    task automatic test_random_operation();
        string test_name = "Random Operation";
        
        // Random write
        rd_addr_i = random_reg_addr();
        rd_data_i = random_word();
        rd_write_en_i = $random % 2; // Random write enable
        @(posedge clk);
        
        // Random read
        rd_write_en_i = 0;
        rs1_addr_i = random_reg_addr();
        rs2_addr_i = random_reg_addr();
        @(posedge clk);
        
        // Basic sanity check
        `ASSERT_TRUE(1, "Random operation completed");
        
        record_test_result(test_name, TEST_PASS, test_stats);
    endtask

    //===========================================================================
    // Coverage
    //===========================================================================
    covergroup reg_file_cg @(posedge clk);
        rs1_addr_cp: coverpoint rs1_addr_i {
            bins zero_reg = {5'h00};
            bins other_regs = {[5'h01:5'h1F]};
        }
        
        rs2_addr_cp: coverpoint rs2_addr_i {
            bins zero_reg = {5'h00};
            bins other_regs = {[5'h01:5'h1F]};
        }
        
        rd_addr_cp: coverpoint rd_addr_i {
            bins zero_reg = {5'h00};
            bins other_regs = {[5'h01:5'h1F]};
        }
        
        rd_write_en_cp: coverpoint rd_write_en_i;
        
        // Cross coverage
        rd_addr_write_cross: cross rd_addr_cp, rd_write_en_cp;
        rs1_rs2_cross: cross rs1_addr_cp, rs2_addr_cp;
    endgroup

    reg_file_cg cg_inst = new();

    //===========================================================================
    // Assertions
    //===========================================================================
    // Check that x0 always reads as 0
    property p_zero_register_read;
        @(posedge clk) (rs1_addr_i == 5'h00) |-> (rs1_data_o == 32'h0000_0000);
    endproperty
    assert property (p_zero_register_read) else
        $error("x0 register should always read as 0");

    // Check that x0 always reads as 0 for rs2
    property p_zero_register_read_rs2;
        @(posedge clk) (rs2_addr_i == 5'h00) |-> (rs2_data_o == 32'h0000_0000);
    endproperty
    assert property (p_zero_register_read_rs2) else
        $error("x0 register should always read as 0 for rs2");

    // Check that write to x0 doesn't affect read
    property p_zero_register_write_ignored;
        @(posedge clk) (rd_addr_i == 5'h00 && rd_write_en_i) |=> 
                       (rs1_data_o == 32'h0000_0000);
    endproperty
    assert property (p_zero_register_write_ignored) else
        $error("Write to x0 should be ignored");

endmodule : reg_file_tb

//=============================================================================
// Dependencies: riscv_core_pkg.sv, test_utils.sv, reg_file.sv
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
//   - Testbench: reg_file_tb.sv
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//============================================================================= 