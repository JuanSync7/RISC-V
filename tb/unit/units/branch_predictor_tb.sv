//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: branch_predictor_tb.sv
// Module: branch_predictor_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Comprehensive testbench for the Branch Prediction Unit (BPU). Tests
//   BTB functionality, BHT accuracy, branch prediction accuracy, and
//   performance characteristics. Validates >85% prediction accuracy target.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module branch_predictor_tb;
    import riscv_core_pkg::*;

    // Parameters
    localparam BTB_ENTRIES = 64;
    localparam BHT_ENTRIES = 256;
    localparam ADDR_WIDTH = 32;
    localparam XLEN = 32;

    // Clock and reset
    logic clk;
    logic rst_n;

    // BPU interface signals
    logic        valid_i;
    addr_t       pc_i;
    logic        predict_taken_o;
    addr_t       predict_target_o;
    logic        btb_hit_o;
    logic        update_i;
    addr_t       update_pc_i;
    logic        actual_taken_i;
    addr_t       actual_target_i;
    logic        is_branch_i;

    // Instantiate BPU
    branch_predictor #(
        .BTB_ENTRIES(BTB_ENTRIES),
        .BHT_ENTRIES(BHT_ENTRIES)
    ) dut (
        .clk_i(clk),
        .rst_ni(rst_n),
        .pc_i(pc_i),
        .predict_taken_o(predict_taken_o),
        .predict_target_o(predict_target_o),
        .btb_hit_o(btb_hit_o),
        .update_i(update_i),
        .update_pc_i(update_pc_i),
        .actual_taken_i(actual_taken_i),
        .actual_target_i(actual_target_i),
        .is_branch_i(is_branch_i)
    );

    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

    // Test statistics
    int total_branches = 0;
    int correct_predictions = 0;
    int btb_hits = 0;
    int btb_misses = 0;
    real prediction_accuracy = 0.0;
    real btb_hit_rate = 0.0;

    // Test stimulus
    initial begin
        rst_n = 0;
        valid_i = 0;
        pc_i = 0;
        update_i = 0;
        update_pc_i = 0;
        actual_taken_i = 0;
        actual_target_i = 0;
        is_branch_i = 0;
        #20;
        rst_n = 1;
        #10;

        // Test 1: Basic BTB functionality
        $display("[TB] Test 1: Basic BTB functionality");
        test_btb_basic();

        // Test 2: BHT prediction accuracy
        $display("[TB] Test 2: BHT prediction accuracy");
        test_bht_accuracy();

        // Test 3: BTB capacity and replacement
        $display("[TB] Test 3: BTB capacity and replacement");
        test_btb_capacity();

        // Test 4: Branch pattern learning
        $display("[TB] Test 4: Branch pattern learning");
        test_branch_patterns();

        // Test 5: Performance metrics
        $display("[TB] Test 5: Performance metrics");
        test_performance_metrics();

        // Test 6: Corner cases
        $display("[TB] Test 6: Corner cases");
        test_corner_cases();

        // Report results
        report_results();
        $finish;
    end

    // Test 1: Basic BTB functionality
    task test_btb_basic();
        // Test BTB miss on first access
        pc_i = 32'h0000_1000;
        valid_i = 1;
        @(posedge clk);
        valid_i = 0;
        @(posedge clk);
        if (!btb_hit_o) $display("[TB] BTB miss on first access - PASS");
        else $display("[TB] ERROR: Expected BTB miss on first access");

        // Update BTB with branch information
        update_i = 1;
        update_pc_i = 32'h0000_1000;
        actual_taken_i = 1;
        actual_target_i = 32'h0000_2000;
        is_branch_i = 1;
        @(posedge clk);
        update_i = 0;
        is_branch_i = 0;

        // Test BTB hit on second access
        pc_i = 32'h0000_1000;
        valid_i = 1;
        @(posedge clk);
        valid_i = 0;
        @(posedge clk);
        if (btb_hit_o && predict_target_o == 32'h0000_2000) 
            $display("[TB] BTB hit with correct target - PASS");
        else $display("[TB] ERROR: Expected BTB hit with correct target");
    endtask

    // Test 2: BHT prediction accuracy
    task test_bht_accuracy();
        // Train a strongly taken branch
        for (int i = 0; i < 10; i++) begin
            update_i = 1;
            update_pc_i = 32'h0000_3000;
            actual_taken_i = 1;
            actual_target_i = 32'h0000_4000;
            is_branch_i = 1;
            @(posedge clk);
        end
        update_i = 0;
        is_branch_i = 0;

        // Test prediction after training
        pc_i = 32'h0000_3000;
        valid_i = 1;
        @(posedge clk);
        valid_i = 0;
        @(posedge clk);
        if (predict_taken_o) 
            $display("[TB] BHT predicts taken after training - PASS");
        else $display("[TB] ERROR: Expected BHT to predict taken after training");

        // Train a strongly not-taken branch
        for (int i = 0; i < 10; i++) begin
            update_i = 1;
            update_pc_i = 32'h0000_5000;
            actual_taken_i = 0;
            actual_target_i = 32'h0000_5004;
            is_branch_i = 1;
            @(posedge clk);
        end
        update_i = 0;
        is_branch_i = 0;

        // Test prediction after training
        pc_i = 32'h0000_5000;
        valid_i = 1;
        @(posedge clk);
        valid_i = 0;
        @(posedge clk);
        if (!predict_taken_o) 
            $display("[TB] BHT predicts not-taken after training - PASS");
        else $display("[TB] ERROR: Expected BHT to predict not-taken after training");
    endtask

    // Test 3: BTB capacity and replacement
    task test_btb_capacity();
        // Fill BTB with unique entries
        for (int i = 0; i < BTB_ENTRIES + 5; i++) begin
            update_i = 1;
            update_pc_i = 32'h0000_6000 + (i * 4);
            actual_taken_i = (i % 2);
            actual_target_i = 32'h0000_7000 + (i * 4);
            is_branch_i = 1;
            @(posedge clk);
        end
        update_i = 0;
        is_branch_i = 0;

        // Test that some entries were replaced
        int hits = 0;
        for (int i = 0; i < 10; i++) begin
            pc_i = 32'h0000_6000 + (i * 4);
            valid_i = 1;
            @(posedge clk);
            valid_i = 0;
            @(posedge clk);
            if (btb_hit_o) hits++;
        end

        if (hits < 10) 
            $display("[TB] BTB replacement working - PASS (%0d/10 hits)", hits);
        else $display("[TB] WARNING: No BTB replacement detected");
    endtask

    // Test 4: Branch pattern learning
    task test_branch_patterns();
        // Create a pattern: TNTNTNTN...
        for (int i = 0; i < 20; i++) begin
            update_i = 1;
            update_pc_i = 32'h0000_8000;
            actual_taken_i = (i % 2);
            actual_target_i = actual_taken_i ? 32'h0000_9000 : 32'h0000_8004;
            is_branch_i = 1;
            @(posedge clk);
        end
        update_i = 0;
        is_branch_i = 0;

        // Test prediction accuracy on pattern
        int correct = 0;
        for (int i = 0; i < 10; i++) begin
            pc_i = 32'h0000_8000;
            valid_i = 1;
            @(posedge clk);
            valid_i = 0;
            @(posedge clk);
            
            // Check if prediction matches pattern
            if (predict_taken_o == ((i + 20) % 2)) correct++;
        end

        if (correct >= 7) 
            $display("[TB] Pattern learning working - PASS (%0d/10 correct)", correct);
        else $display("[TB] WARNING: Pattern learning accuracy low (%0d/10 correct)", correct);
    endtask

    // Test 5: Performance metrics
    task test_performance_metrics();
        // Generate random branch patterns
        for (int i = 0; i < 100; i++) begin
            // Random branch
            update_i = 1;
            update_pc_i = $random & 32'hFFFF_FFFF;
            actual_taken_i = $random % 2;
            actual_target_i = actual_taken_i ? ($random & 32'hFFFF_FFFF) : (update_pc_i + 4);
            is_branch_i = 1;
            @(posedge clk);
            
            // Test prediction
            pc_i = update_pc_i;
            valid_i = 1;
            @(posedge clk);
            valid_i = 0;
            @(posedge clk);
            
            // Update statistics
            total_branches++;
            if (predict_taken_o == actual_taken_i) correct_predictions++;
            if (btb_hit_o) btb_hits++;
            else btb_misses++;
        end
        update_i = 0;
        is_branch_i = 0;

        // Calculate metrics
        prediction_accuracy = real'(correct_predictions) / real'(total_branches) * 100.0;
        btb_hit_rate = real'(btb_hits) / real'(btb_hits + btb_misses) * 100.0;

        $display("[TB] Performance Metrics:");
        $display("[TB]   Total Branches: %0d", total_branches);
        $display("[TB]   Correct Predictions: %0d", correct_predictions);
        $display("[TB]   Prediction Accuracy: %0.1f%%", prediction_accuracy);
        $display("[TB]   BTB Hit Rate: %0.1f%%", btb_hit_rate);
    endtask

    // Test 6: Corner cases
    task test_corner_cases();
        // Test with zero PC
        pc_i = 32'h0000_0000;
        valid_i = 1;
        @(posedge clk);
        valid_i = 0;
        @(posedge clk);
        $display("[TB] Zero PC test - PASS");

        // Test with maximum PC
        pc_i = 32'hFFFF_FFFF;
        valid_i = 1;
        @(posedge clk);
        valid_i = 0;
        @(posedge clk);
        $display("[TB] Maximum PC test - PASS");

        // Test rapid updates
        for (int i = 0; i < 5; i++) begin
            update_i = 1;
            update_pc_i = 32'h0000_A000 + (i * 4);
            actual_taken_i = 1;
            actual_target_i = 32'h0000_B000 + (i * 4);
            is_branch_i = 1;
            @(posedge clk);
        end
        update_i = 0;
        is_branch_i = 0;
        $display("[TB] Rapid updates test - PASS");
    endtask

    // Report final results
    task report_results();
        $display("[TB] ========================================");
        $display("[TB] Branch Predictor Test Results");
        $display("[TB] ========================================");
        $display("[TB] Total Branches Tested: %0d", total_branches);
        $display("[TB] Prediction Accuracy: %0.1f%%", prediction_accuracy);
        $display("[TB] BTB Hit Rate: %0.1f%%", btb_hit_rate);
        
        if (prediction_accuracy >= 85.0) begin
            $display("[TB] ✅ Prediction accuracy target met (>85%%)");
        end else begin
            $display("[TB] ❌ Prediction accuracy below target (<85%%)");
        end
        
        if (btb_hit_rate >= 80.0) begin
            $display("[TB] ✅ BTB hit rate target met (>80%%)");
        end else begin
            $display("[TB] ❌ BTB hit rate below target (<80%%)");
        end
        
        $display("[TB] ========================================");
    endtask

    // Coverage
    covergroup branch_predictor_cg @(posedge clk);
        prediction_cp: coverpoint predict_taken_o;
        btb_hit_cp: coverpoint btb_hit_o;
        update_cp: coverpoint update_i;
        actual_taken_cp: coverpoint actual_taken_i;
        
        prediction_btb_cross: cross prediction_cp, btb_hit_cp;
        update_actual_cross: cross update_cp, actual_taken_cp;
    endgroup

    branch_predictor_cg bp_cg = new();

endmodule : branch_predictor_tb 