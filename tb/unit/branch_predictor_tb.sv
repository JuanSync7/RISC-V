//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V
//
// File: branch_predictor_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: branch_predictor_tb
// AUTHOR: DesignAI (<author_email@company.com>)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Testbench for the Branch Predictor module, including BTB, BHT, and RAS.
// PRIMARY_PURPOSE: To verify the functional correctness of the Branch Predictor module's prediction logic and update mechanisms.
// ROLE_IN_SYSTEM: Unit test for the Branch Predictor, ensuring its standalone functionality before integration into the core pipeline.
// PROBLEM_SOLVED: Ensures accurate branch prediction, correct handling of JAL/JALR instructions, and proper update of prediction tables.
// MODULE_TYPE: Testbench_Component
// TARGET_TECHNOLOGY_PREF: N/A (Simulation only)
// RELATED_SPECIFICATION: RISC-V Privileged Architecture Specification (Branch Prediction aspects)
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module branch_predictor_tb;

    import riscv_core_pkg::*;
    import riscv_config_pkg::*;
    import riscv_bp_types_pkg::*;

    // AI_TAG: FEATURE - Testing of BTB (Branch Target Buffer) functionality.
    // AI_TAG: FEATURE - Testing of BHT (Branch History Table) functionality.
    // AI_TAG: FEATURE - Testing of RAS (Return Address Stack) push and pop operations.
    // AI_TAG: FEATURE - Verification of branch prediction accuracy.
    // AI_TAG: FEATURE - Handling of JAL and JALR instructions.

    // Clock and Reset
    logic clk;  // AI_TAG: PORT_DESC - Testbench clock.
                // AI_TAG: PORT_CLK_DOMAIN - clk
    logic rst_n; // AI_TAG: PORT_DESC - Active-low asynchronous reset.
                 // AI_TAG: PORT_CLK_DOMAIN - clk (async assert)
                 // AI_TAG: PORT_TIMING - Asynchronous

    // Branch Predictor Inputs
    addr_t pc_i; // AI_TAG: PORT_DESC - Program Counter input to the branch predictor.
                 // AI_TAG: PORT_CLK_DOMAIN - clk
    branch_update_t bp_update_i; // AI_TAG: PORT_DESC - Branch update information from the execute stage.
                                 // AI_TAG: PORT_CLK_DOMAIN - clk

    // Branch Predictor Outputs
    logic predict_taken_o; // AI_TAG: PORT_DESC - Predicted taken status.
                           // AI_TAG: PORT_CLK_DOMAIN - clk
                           // AI_TAG: PORT_DEFAULT_STATE - 1'b0
    addr_t predict_target_o; // AI_TAG: PORT_DESC - Predicted branch target address.
                             // AI_TAG: PORT_CLK_DOMAIN - clk
                             // AI_TAG: PORT_DEFAULT_STATE - '0
    logic btb_hit_o; // AI_TAG: PORT_DESC - Indicates a BTB hit.
                     // AI_TAG: PORT_CLK_DOMAIN - clk
                     // AI_TAG: PORT_DEFAULT_STATE - 1'b0
    addr_t ras_predict_target_o; // AI_TAG: PORT_DESC - Predicted return address from RAS.
                                 // AI_TAG: PORT_CLK_DOMAIN - clk
                                 // AI_TAG: PORT_DEFAULT_STATE - '0

    // Instantiate the Branch Predictor Unit (BPU)
    branch_predictor #(
        .BTB_ENTRIES(DEFAULT_BTB_ENTRIES), // AI_TAG: PARAM_DESC - Number of entries in the Branch Target Buffer.
                                           // AI_TAG: PARAM_USAGE - Configures the size of the BTB.
                                           // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2.
        .BHT_ENTRIES(DEFAULT_BHT_ENTRIES), // AI_TAG: PARAM_DESC - Number of entries in the Branch History Table.
                                           // AI_TAG: PARAM_USAGE - Configures the size of the BHT.
                                           // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2.
        .RAS_ENTRIES(DEFAULT_RAS_ENTRIES)  // AI_TAG: PARAM_DESC - Number of entries in the Return Address Stack.
                                           // AI_TAG: PARAM_USAGE - Configures the depth of the RAS.
                                           // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2.
    ) uut ( // AI_TAG: IF_TYPE - Branch Predictor Unit Instance
            // AI_TAG: IF_DESC - Instance of the Branch Predictor Unit under test.
            // AI_TAG: IF_CLOCKING - clk
            // AI_TAG: IF_RESET - rst_n
        .clk_i(clk),
        .rst_ni(rst_n),
        .pc_i(pc_i),
        .predict_taken_o(predict_taken_o),
        .predict_target_o(predict_target_o),
        .btb_hit_o(btb_hit_o),
        .ras_predict_target_o(ras_predict_target_o),
        .update_i(bp_update_i.update_valid),
        .update_pc_i(bp_update_i.update_pc),
        .actual_taken_i(bp_update_i.actual_taken),
        .actual_target_i(bp_update_i.actual_target),
        .is_branch_i(bp_update_i.is_branch),
        .is_jal_i(bp_update_i.is_jal),
        .jal_target_i(bp_update_i.jal_target),
        .is_jalr_i(bp_update_i.is_jalr)
    );

    // Clock Generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period (100MHz)
    end

    // Test Stimulus
    initial begin
        $display("\n--------------------------------------------------");
        $display("Starting Branch Predictor Testbench");
        $display("--------------------------------------------------");

        // Initialize signals
        rst_n = 0;
        pc_i = '0;
        bp_update_i = '0;

        // AI_TAG: SCENARIO_START - Initial Reset and Initialization
        // Apply reset and initialize testbench variables.
        // AI_TAG: SCENARIO_END
        #10; // Wait for a bit
        rst_n = 1; // Release reset
        $display("Reset released.");

        // --- Test Scenario 1: Basic Branch Prediction (Not Taken) ---
        // AI_TAG: SCENARIO_START - Basic Branch Prediction (Not Taken)
        // Test a simple branch that is predicted not taken and then updated as not taken.
        // AI_TAG: SCENARIO_END
        $display("\n--- Test Scenario 1: Basic Branch Prediction (Not Taken) ---");
        pc_i = 32'h0000_1000; // Instruction at 0x1000
        #10; // Prediction cycle
        $display("PC: %h, Predicted Taken: %b, Predicted Target: %h, BTB Hit: %b, RAS Target: %h",
                 pc_i, predict_taken_o, predict_target_o, btb_hit_o, ras_predict_target_o);
        // Simulate actual outcome: Not Taken
        bp_update_i.update_valid = 1;
        bp_update_i.update_pc = 32'h0000_1000;
        bp_update_i.actual_taken = 0;
        bp_update_i.actual_target = 32'h0000_1004; // PC + 4
        bp_update_i.is_branch = 1;
        bp_update_i.is_jal = 0;
        bp_update_i.is_jalr = 0;
        #10; // Update cycle
        bp_update_i = '0; // Clear update

        // --- Test Scenario 2: Basic Branch Prediction (Taken) ---
        // AI_TAG: SCENARIO_START - Basic Branch Prediction (Taken)
        // Test a simple branch that is predicted taken and then updated as taken.
        // AI_TAG: SCENARIO_END
        $display("\n--- Test Scenario 2: Basic Branch Prediction (Taken) ---");
        pc_i = 32'h0000_1008; // Instruction at 0x1008
        #10; // Prediction cycle
        $display("PC: %h, Predicted Taken: %b, Predicted Target: %h, BTB Hit: %b, RAS Target: %h",
                 pc_i, predict_taken_o, predict_target_o, btb_hit_o, ras_predict_target_o);
        // Simulate actual outcome: Taken to 0x1020
        bp_update_i.update_valid = 1;
        bp_update_i.update_pc = 32'h0000_1008;
        bp_update_i.actual_taken = 1;
        bp_update_i.actual_target = 32'h0000_1020;
        bp_update_i.is_branch = 1;
        bp_update_i.is_jal = 0;
        bp_update_i.is_jalr = 0;
        #10; // Update cycle
        bp_update_i = '0; // Clear update

        // --- Test Scenario 3: JAL (Push to RAS) ---
        // AI_TAG: SCENARIO_START - JAL (Push to RAS)
        // Test JAL instruction, which should push the return address onto the RAS.
        // AI_TAG: SCENARIO_END
        $display("\n--- Test Scenario 3: JAL (Push to RAS) ---");
        pc_i = 32'h0000_2000; // JAL instruction
        #10; // Prediction cycle (should predict PC+4, as JAL is not in BTB initially)
        $display("PC: %h, Predicted Taken: %b, Predicted Target: %h, BTB Hit: %b, RAS Target: %h",
                 pc_i, predict_taken_o, predict_target_o, btb_hit_o, ras_predict_target_o);
        // Simulate actual outcome: JAL taken, return address 0x2004
        bp_update_i.update_valid = 1;
        bp_update_i.update_pc = 32'h0000_2000;
        bp_update_i.actual_taken = 1;
        bp_update_i.actual_target = 32'h0000_2050; // JAL target
        bp_update_i.is_branch = 1;
        bp_update_i.is_jal = 1;
        bp_update_i.jal_target = 32'h0000_2004; // Return address (PC+4)
        bp_update_i.is_jalr = 0;
        #10; // Update cycle
        bp_update_i = '0; // Clear update

        // --- Test Scenario 4: JALR (Pop from RAS) ---
        // AI_TAG: SCENARIO_START - JALR (Pop from RAS)
        // Test JALR instruction, which should pop the return address from the RAS.
        // AI_TAG: SCENARIO_END
        $display("\n--- Test Scenario 4: JALR (Pop from RAS) ---");
        pc_i = 32'h0000_204C; // JALR instruction (just before 0x2050)
        #10; // Prediction cycle (should predict RAS target)
        $display("PC: %h, Predicted Taken: %b, Predicted Target: %h, BTB Hit: %b, RAS Target: %h",
                 pc_i, predict_taken_o, predict_target_o, btb_hit_o, ras_predict_target_o);
        // Simulate actual outcome: JALR taken to 0x2004 (popped from RAS)
        bp_update_i.update_valid = 1;
        bp_update_i.update_pc = 32'h0000_204C;
        bp_update_i.actual_taken = 1;
        bp_update_i.actual_target = 32'h0000_2004; // Actual target from RAS
        bp_update_i.is_branch = 1;
        bp_update_i.is_jal = 0;
        bp_update_i.is_jalr = 1;
        #10; // Update cycle
        bp_update_i = '0; // Clear update

        // --- Test Scenario 5: Nested JAL/JALR ---
        // AI_TAG: SCENARIO_START - Nested JAL/JALR
        // Test nested JAL calls and subsequent JALR returns to verify RAS depth and LIFO behavior.
        // AI_TAG: SCENARIO_END
        $display("\n--- Test Scenario 5: Nested JAL/JALR ---");
        // JAL 1
        pc_i = 32'h0000_3000;
        #10;
        bp_update_i.update_valid = 1; bp_update_i.update_pc = 32'h0000_3000; bp_update_i.actual_taken = 1; bp_update_i.actual_target = 32'h0000_3100; bp_update_i.is_branch = 1; bp_update_i.is_jal = 1; bp_update_i.jal_target = 32'h0000_3004; bp_update_i.is_jalr = 0;
        #10; bp_update_i = '0;

        // JAL 2
        pc_i = 32'h0000_3100;
        #10;
        bp_update_i.update_valid = 1; bp_update_i.update_pc = 32'h0000_3100; bp_update_i.actual_taken = 1; bp_update_i.actual_target = 32'h0000_3200; bp_update_i.is_branch = 1; bp_update_i.is_jal = 1; bp_update_i.jal_target = 32'h0000_3104; bp_update_i.is_jalr = 0;
        #10; bp_update_i = '0;

        // JALR 2 (pop 3104)
        pc_i = 32'h0000_31FC; // Predicts 0x3104
        #10;
        $display("PC: %h, Predicted Target (from RAS): %h", pc_i, ras_predict_target_o);
        bp_update_i.update_valid = 1; bp_update_i.update_pc = 32'h0000_31FC; bp_update_i.actual_taken = 1; bp_update_i.actual_target = 32'h0000_3104; bp_update_i.is_branch = 1; bp_update_i.is_jal = 0; bp_update_i.is_jalr = 1;
        #10; bp_update_i = '0;

        // JALR 1 (pop 3004)
        pc_i = 32'h0000_30FC; // Predicts 0x3004
        #10;
        $display("PC: %h, Predicted Target (from RAS): %h", pc_i, ras_predict_target_o);
        bp_update_i.update_valid = 1; bp_update_i.update_pc = 32'h0000_30FC; bp_update_i.actual_taken = 1; bp_update_i.actual_target = 32'h0000_3004; bp_update_i.is_branch = 1; bp_update_i.is_jal = 0; bp_update_i.is_jalr = 1;
        #10; bp_update_i = '0;

        $display("\n--------------------------------------------------");
        $display("Branch Predictor Testbench Finished");
        $display("--------------------------------------------------");
        $finish;
    end

endmodule : branch_predictor_tb
//=============================================================================
// Dependencies: branch_predictor.sv, riscv_core_pkg.sv, riscv_config_pkg.sv, riscv_bp_types_pkg.sv
//
// Instantiated In:
//   - N/A (Top-level testbench)
//
// Performance:
//   - Critical Path: N/A
//   - Max Frequency: N/A (Simulation only)
//   - Area: N/A (Simulation only)
//
// Verification Coverage:
//   - Code Coverage: To be determined by simulation tool
//   - Functional Coverage: To be determined by simulation tool
//   - Branch Coverage: To be determined by simulation tool
//
// Synthesis:
//   - Target Technology: N/A
//   - Synthesis Tool: N/A
//   - Clock Domains: 1
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: branch_predictor_tb.sv
//   - Test Vectors: 5 directed test cases
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | DesignAI           | Initial creation of Branch Predictor testbench.
//=============================================================================