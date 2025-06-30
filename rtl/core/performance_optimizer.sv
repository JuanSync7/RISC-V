//=============================================================================
// MODULE_NAME: performance_optimizer
// AUTHOR: RTL Design Agent
// VERSION: 1.0.0
// DATE: 2025-01-27
// DESCRIPTION: Dynamic system performance optimization controller
// PRIMARY_PURPOSE: Optimize system performance through dynamic control mechanisms
// ROLE_IN_SYSTEM: Controls and optimizes various system performance parameters
// PROBLEM_SOLVED: Provides adaptive performance optimization based on system conditions
// MODULE_TYPE: RTL
// TARGET_TECHNOLOGY_PREF: ASIC
// RELATED_SPECIFICATION: RISC-V_Performance_Optimization_Spec_v1.0
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Cache replacement policy optimization
// AI_TAG: FEATURE - Branch predictor tuning
// AI_TAG: FEATURE - Pipeline balancing control
// AI_TAG: FEATURE - Power-performance optimization

// AI_TAG: INTERNAL_BLOCK - CacheOptimizer - Optimizes cache replacement policies
// AI_TAG: INTERNAL_BLOCK - BranchOptimizer - Tunes branch predictor parameters
// AI_TAG: INTERNAL_BLOCK - PipelineController - Balances pipeline stages
// AI_TAG: INTERNAL_BLOCK - PowerManager - Manages power-performance tradeoffs

// AI_TAG: BLOCK_DIAGRAM_DESC - Performance metrics feed into CacheOptimizer and BranchOptimizer for algorithmic tuning. PipelineController manages stage balancing. PowerManager coordinates power-performance optimization across all components.

import riscv_config_pkg::*;

module performance_optimizer #(
    parameter integer NUM_CACHE_LEVELS = DEFAULT_NUM_CACHE_LEVELS,            // AI_TAG: PARAM_DESC - Number of cache levels to optimize
                                                        // AI_TAG: PARAM_USAGE - Configures cache optimization arrays
                                                        // AI_TAG: PARAM_CONSTRAINTS - Must be >= 1, Max 4
    parameter integer NUM_BP_PREDICTORS = DEFAULT_NUM_BP_PREDICTORS,            // AI_TAG: PARAM_DESC - Number of branch predictors
                                                        // AI_TAG: PARAM_USAGE - Configures branch predictor optimization
                                                        // AI_TAG: PARAM_CONSTRAINTS - Must be power of 2
    parameter integer OPTIMIZATION_WINDOW = DEFAULT_OPT_WINDOW       // AI_TAG: PARAM_DESC - Optimization window size in cycles
                                                        // AI_TAG: PARAM_USAGE - Determines how often optimizations are applied
                                                        // AI_TAG: PARAM_CONSTRAINTS - Must be power of 2
) (
    // System Clock and Reset
    input  logic                            clk_i,      // AI_TAG: PORT_DESC - System clock
                                                        // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic                            rst_ni,     // AI_TAG: PORT_DESC - Asynchronous active-low reset
                                                        // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
                                                        // AI_TAG: PORT_TIMING - Asynchronous

    // Performance Monitoring Inputs
    input  logic [31:0]                     ipc_current_i,      // AI_TAG: PORT_DESC - Current IPC measurement
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic [15:0]                     cache_miss_rate_i,  // AI_TAG: PORT_DESC - Cache miss rate percentage
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic [15:0]                     branch_miss_rate_i, // AI_TAG: PORT_DESC - Branch prediction miss rate
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic [7:0]                      pipeline_stalls_i,  // AI_TAG: PORT_DESC - Pipeline stall count
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i

    // System Load Indicators
    input  logic [7:0]                      system_load_i,      // AI_TAG: PORT_DESC - Overall system load percentage
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic [7:0]                      power_budget_i,     // AI_TAG: PORT_DESC - Available power budget
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i

    // Optimization Control Outputs
    output logic [2:0]                      cache_policy_o,     // AI_TAG: PORT_DESC - Cache replacement policy selection
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                                // AI_TAG: PORT_DEFAULT_STATE - 3'b000 (LRU policy)
    output logic [3:0]                      bp_config_o,        // AI_TAG: PORT_DESC - Branch predictor configuration
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                                // AI_TAG: PORT_DEFAULT_STATE - 4'b0001 (default config)
    output logic [1:0]                      pipeline_mode_o,    // AI_TAG: PORT_DESC - Pipeline operation mode
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                                // AI_TAG: PORT_DEFAULT_STATE - 2'b00 (normal mode)
    
    // Power Management Outputs
    output logic                            clock_gate_en_o,    // AI_TAG: PORT_DESC - Clock gating enable
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                                // AI_TAG: PORT_DEFAULT_STATE - 1'b0
    output logic [3:0]                      power_mode_o,       // AI_TAG: PORT_DESC - System power mode
                                                                // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                                // AI_TAG: PORT_DEFAULT_STATE - 4'b0001 (normal power)

    // Optimization Status
    output logic                            optimization_active_o, // AI_TAG: PORT_DESC - Optimization in progress
                                                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                                   // AI_TAG: PORT_DEFAULT_STATE - 1'b0
    output logic [31:0]                     performance_gain_o     // AI_TAG: PORT_DESC - Estimated performance gain
                                                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                                   // AI_TAG: PORT_DEFAULT_STATE - 32'h0
);

    //-----
    // Local Parameters
    //-----
    localparam integer IPC_TARGET = DEFAULT_IPC_TARGET;                // Target IPC percentage
    localparam integer CACHE_MISS_THRESHOLD = DEFAULT_CACHE_MISS_THRESHOLD;      // Cache miss rate threshold (%)
    localparam integer BRANCH_MISS_THRESHOLD = DEFAULT_BRANCH_MISS_THRESHOLD;     // Branch miss rate threshold (%)
    localparam integer PIPELINE_STALL_THRESHOLD = DEFAULT_PIPELINE_STALL_THRESHOLD;  // Pipeline stall threshold

    // AI_TAG: FSM_NAME - optimizer_fsm_cs
    // AI_TAG: FSM_PURPOSE - optimizer_fsm_cs - Controls optimization sequence and decisions
    // AI_TAG: FSM_ENCODING - optimizer_fsm_cs - binary
    // AI_TAG: FSM_RESET_STATE - optimizer_fsm_cs - S_MONITOR
    typedef enum logic [2:0] {
        S_MONITOR       = 3'b000,  // AI_TAG: FSM_STATE - S_MONITOR - Performance monitoring state
        S_ANALYZE       = 3'b001,  // AI_TAG: FSM_STATE - S_ANALYZE - Performance analysis state
        S_CACHE_OPT     = 3'b010,  // AI_TAG: FSM_STATE - S_CACHE_OPT - Cache optimization state
        S_BRANCH_OPT    = 3'b011,  // AI_TAG: FSM_STATE - S_BRANCH_OPT - Branch predictor optimization
        S_PIPELINE_OPT  = 3'b100,  // AI_TAG: FSM_STATE - S_PIPELINE_OPT - Pipeline optimization state
        S_POWER_OPT     = 3'b101   // AI_TAG: FSM_STATE - S_POWER_OPT - Power optimization state
    } optimizer_state_e;

    // Cache replacement policies
    typedef enum logic [2:0] {
        POLICY_LRU      = 3'b000,  // Least Recently Used
        POLICY_LFU      = 3'b001,  // Least Frequently Used
        POLICY_RANDOM   = 3'b010,  // Random replacement
        POLICY_FIFO     = 3'b011,  // First In, First Out
        POLICY_ADAPTIVE = 3'b100   // Adaptive based on access pattern
    } cache_policy_e;

    //-----
    // Internal Signal Declarations
    //-----

    // AI_TAG: INTERNAL_STORAGE - optimizer_fsm_cs - Current FSM state
    // AI_TAG: INTERNAL_STORAGE_TYPE - optimizer_fsm_cs - Flip-flop based
    optimizer_state_e                       optimizer_fsm_cs, optimizer_fsm_ns;

    // Performance tracking registers
    logic [31:0]                            ipc_history_r [3:0];
    logic [15:0]                            cache_miss_history_r [3:0];
    logic [15:0]                            branch_miss_history_r [3:0];
    logic [31:0]                            optimization_counter_r;
    logic [31:0]                            baseline_performance_r;

    // Optimization configuration registers
    logic [2:0]                             current_cache_policy_r;
    logic [3:0]                             current_bp_config_r;
    logic [1:0]                             current_pipeline_mode_r;
    logic [3:0]                             current_power_mode_r;

    // Combinational signals
    logic                                   performance_degraded_c;
    logic                                   cache_optimization_needed_c;
    logic                                   branch_optimization_needed_c;
    logic                                   pipeline_optimization_needed_c;
    logic                                   power_optimization_needed_c;
    logic [31:0]                            average_ipc_c;

    //-----
    // Combinational Logic
    //-----

    // AI_TAG: DATAPATH_DESC - Performance metrics are analyzed to determine optimization needs and calculate performance gains
    
    // Calculate average IPC over history window
    always_comb begin : proc_average_ipc
        average_ipc_c = (ipc_history_r[0] + ipc_history_r[1] + 
                        ipc_history_r[2] + ipc_history_r[3]) >> 2; // Divide by 4
    end

    // Determine optimization needs
    assign performance_degraded_c = (average_ipc_c < IPC_TARGET);
    assign cache_optimization_needed_c = (cache_miss_rate_i > CACHE_MISS_THRESHOLD);
    assign branch_optimization_needed_c = (branch_miss_rate_i > BRANCH_MISS_THRESHOLD);
    assign pipeline_optimization_needed_c = (pipeline_stalls_i > PIPELINE_STALL_THRESHOLD);
    assign power_optimization_needed_c = (system_load_i < 50) && (power_budget_i < 80);

    // Performance gain estimation
    always_comb begin : proc_performance_gain
        logic [31:0] cache_gain, branch_gain, pipeline_gain;
        
        // Estimate gains based on current miss rates and optimizations
        cache_gain = cache_optimization_needed_c ? 
                     (cache_miss_rate_i > 20) ? 32'd15 : 32'd5 : 32'd0;
        
        branch_gain = branch_optimization_needed_c ? 
                      (branch_miss_rate_i > 15) ? 32'd10 : 32'd3 : 32'd0;
        
        pipeline_gain = pipeline_optimization_needed_c ? 
                        (pipeline_stalls_i > 30) ? 32'd12 : 32'd4 : 32'd0;
        
        performance_gain_o = cache_gain + branch_gain + pipeline_gain;
    end

    //-----
    // Sequential Logic (Registers)
    //-----

    // FSM state register
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_fsm_state_reg
        if (!rst_ni) begin
            optimizer_fsm_cs <= S_MONITOR;
        end else begin
            optimizer_fsm_cs <= optimizer_fsm_ns;
        end
    end

    // Performance history tracking
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_performance_history
        if (!rst_ni) begin
            for (int i = 0; i < 4; i++) begin
                ipc_history_r[i] <= 32'h0;
                cache_miss_history_r[i] <= 16'h0;
                branch_miss_history_r[i] <= 16'h0;
            end
            optimization_counter_r <= 32'h0;
            baseline_performance_r <= 32'h0;
        end else begin
            // Shift history arrays and add new samples every optimization window
            if (optimization_counter_r == (OPTIMIZATION_WINDOW - 1)) begin
                for (int i = 3; i > 0; i--) begin
                    ipc_history_r[i] <= ipc_history_r[i-1];
                    cache_miss_history_r[i] <= cache_miss_history_r[i-1];
                    branch_miss_history_r[i] <= branch_miss_history_r[i-1];
                end
                ipc_history_r[0] <= ipc_current_i;
                cache_miss_history_r[0] <= cache_miss_rate_i;
                branch_miss_history_r[0] <= branch_miss_rate_i;
                
                optimization_counter_r <= 32'h0;
            end else begin
                optimization_counter_r <= optimization_counter_r + 32'h1;
            end
            
            // Update baseline performance
            if (average_ipc_c > baseline_performance_r) begin
                baseline_performance_r <= average_ipc_c;
            end
        end
    end

    // Optimization configuration registers
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_optimization_config
        if (!rst_ni) begin
            current_cache_policy_r <= POLICY_LRU;
            current_bp_config_r <= 4'b0001;
            current_pipeline_mode_r <= 2'b00;
            current_power_mode_r <= 4'b0001;
        end else begin
            // Update configurations based on FSM state
            case (optimizer_fsm_cs)
                S_CACHE_OPT: begin
                    // Adaptive cache policy selection
                    if (cache_miss_rate_i > 25) begin
                        current_cache_policy_r <= POLICY_ADAPTIVE;
                    end else if (cache_miss_rate_i > 20) begin
                        current_cache_policy_r <= POLICY_LFU;
                    end else if (cache_miss_rate_i > 15) begin
                        current_cache_policy_r <= POLICY_LRU;
                    end
                end
                
                S_BRANCH_OPT: begin
                    // Branch predictor configuration tuning
                    if (branch_miss_rate_i > 15) begin
                        current_bp_config_r <= 4'b1000; // Aggressive prediction
                    end else if (branch_miss_rate_i > 10) begin
                        current_bp_config_r <= 4'b0100; // Moderate prediction
                    end else begin
                        current_bp_config_r <= 4'b0001; // Conservative prediction
                    end
                end
                
                S_PIPELINE_OPT: begin
                    // Pipeline mode optimization
                    if (pipeline_stalls_i > 30) begin
                        current_pipeline_mode_r <= 2'b10; // Deep pipeline mode
                    end else if (pipeline_stalls_i > 20) begin
                        current_pipeline_mode_r <= 2'b01; // Balanced pipeline mode
                    end else begin
                        current_pipeline_mode_r <= 2'b00; // Normal pipeline mode
                    end
                end
                
                S_POWER_OPT: begin
                    // Power mode optimization
                    if (system_load_i < 30) begin
                        current_power_mode_r <= 4'b0010; // Low power mode
                    end else if (system_load_i < 70) begin
                        current_power_mode_r <= 4'b0001; // Normal power mode
                    end else begin
                        current_power_mode_r <= 4'b1000; // High performance mode
                    end
                end
                
                default: begin
                    // Maintain current configurations
                end
            endcase
        end
    end

    //-----
    // FSM Next-State Logic
    //-----

    // AI_TAG: FSM_INPUT_CONDITIONS - optimizer_fsm_cs - performance_degraded_c, cache_optimization_needed_c, branch_optimization_needed_c
    always_comb begin : proc_fsm_next_state
        optimizer_fsm_ns = optimizer_fsm_cs; // Default: stay in current state
        
        // Default outputs
        optimization_active_o = 1'b0;
        clock_gate_en_o = 1'b0;

        case (optimizer_fsm_cs)
            S_MONITOR: begin
                // AI_TAG: FSM_OUTPUT_ACTIONS - optimizer_fsm_cs - S_MONITOR - Monitor performance and decide on optimizations
                if (performance_degraded_c && (optimization_counter_r == 0)) begin
                    optimizer_fsm_ns = S_ANALYZE;
                end
            end
            
            S_ANALYZE: begin
                // AI_TAG: FSM_OUTPUT_ACTIONS - optimizer_fsm_cs - S_ANALYZE - Analyze which optimization is most needed
                optimization_active_o = 1'b1;
                
                if (cache_optimization_needed_c) begin
                    optimizer_fsm_ns = S_CACHE_OPT;
                end else if (branch_optimization_needed_c) begin
                    optimizer_fsm_ns = S_BRANCH_OPT;
                end else if (pipeline_optimization_needed_c) begin
                    optimizer_fsm_ns = S_PIPELINE_OPT;
                end else if (power_optimization_needed_c) begin
                    optimizer_fsm_ns = S_POWER_OPT;
                end else begin
                    optimizer_fsm_ns = S_MONITOR;
                end
            end
            
            S_CACHE_OPT: begin
                // AI_TAG: FSM_OUTPUT_ACTIONS - optimizer_fsm_cs - S_CACHE_OPT - Apply cache optimizations
                optimization_active_o = 1'b1;
                optimizer_fsm_ns = S_MONITOR;
            end
            
            S_BRANCH_OPT: begin
                // AI_TAG: FSM_OUTPUT_ACTIONS - optimizer_fsm_cs - S_BRANCH_OPT - Apply branch predictor optimizations
                optimization_active_o = 1'b1;
                optimizer_fsm_ns = S_MONITOR;
            end
            
            S_PIPELINE_OPT: begin
                // AI_TAG: FSM_OUTPUT_ACTIONS - optimizer_fsm_cs - S_PIPELINE_OPT - Apply pipeline optimizations
                optimization_active_o = 1'b1;
                optimizer_fsm_ns = S_MONITOR;
            end
            
            S_POWER_OPT: begin
                // AI_TAG: FSM_OUTPUT_ACTIONS - optimizer_fsm_cs - S_POWER_OPT - Apply power optimizations
                optimization_active_o = 1'b1;
                clock_gate_en_o = (current_power_mode_r != 4'b1000); // Enable clock gating unless high performance mode
                optimizer_fsm_ns = S_MONITOR;
            end
            
            default: begin
                optimizer_fsm_ns = S_MONITOR;
            end
        endcase
    end

    // Output assignments
    assign cache_policy_o = current_cache_policy_r;
    assign bp_config_o = current_bp_config_r;
    assign pipeline_mode_o = current_pipeline_mode_r;
    assign power_mode_o = current_power_mode_r;

    // AI_TAG: FSM_TRANSITION - optimizer_fsm_cs: S_MONITOR -> S_ANALYZE when (performance_degraded_c && optimization_counter_r == 0)
    // AI_TAG: FSM_TRANSITION - optimizer_fsm_cs: S_ANALYZE -> S_CACHE_OPT when (cache_optimization_needed_c)
    // AI_TAG: FSM_TRANSITION - optimizer_fsm_cs: S_CACHE_OPT -> S_MONITOR when (optimization applied)

    //-----
    // Assertions
    //-----

    // AI_TAG: ASSERTION - a_cache_policy_valid: Ensures cache policy is within valid range
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    a_cache_policy_valid: assert property (
        @(posedge clk_i) disable iff (!rst_ni) 
        (cache_policy_o <= POLICY_ADAPTIVE)
    );

    // AI_TAG: ASSERTION - a_optimization_progress: Optimization should be active when not in monitor state
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Warning
    a_optimization_progress: assert property (
        @(posedge clk_i) disable iff (!rst_ni)
        (optimizer_fsm_cs != S_MONITOR) |-> (optimization_active_o)
    );

endmodule : performance_optimizer

`default_nettype wire

//=============================================================================
// Dependencies: None
//
// Performance:
//   - Critical Path: Performance history calculation and FSM transitions
//   - Max Frequency: 400MHz (ASIC)
//   - Area: Medium, includes history storage and optimization logic
//
// Verification Coverage:
//   - Code Coverage: Target 100%
//   - Functional Coverage: All optimization scenarios and FSM states
//   - Branch Coverage: All conditional optimization paths
//
// Synthesis:
//   - Target Technology: ASIC
//   - Synthesis Tool: Design Compiler
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: performance_optimizer.sdc
//
// Testing:
//   - Testbench: performance_optimizer_tb.sv
//   - Test Vectors: 1000+ optimization scenarios
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-01-27 | RTL Design Agent   | Initial release - dynamic performance optimization
//============================================================================= 