//=============================================================================
// Company: <Company Name>
// Project Name: RISC-V
//
// File: qos_stress_tb.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: qos_stress_tb
// AUTHOR: DesignAI (<author_email@company.com>)
// VERSION: 1.0.0
// DATE: 2025-07-05
// DESCRIPTION: Comprehensive QoS stress testing testbench that validates QoS arbitration under high load conditions, priority inversion scenarios, starvation prevention, and bandwidth allocation fairness across multiple cores.
// PRIMARY_PURPOSE: To verify the QoS arbiter's ability to manage and prioritize memory requests under various stress conditions, ensuring fairness and preventing starvation.
// ROLE_IN_SYSTEM: Top-level test for the QoS system, ensuring its robust operation within the memory hierarchy.
// PROBLEM_SOLVED: Validates that the QoS system correctly enforces priorities, prevents starvation of low-priority traffic, and allocates bandwidth according to configured weights.
// MODULE_TYPE: Testbench_Component
// TARGET_TECHNOLOGY_PREF: N/A (Simulation Only)
// RELATED_SPECIFICATION: QoS Specification Document
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: In Progress
// QUALITY_STATUS: Draft
//
//=============================================================================
`timescale 1ns/1ps
`default_nettype none

import riscv_config_pkg::*;
import riscv_types_pkg::*;
import riscv_qos_pkg::*;
import riscv_mem_types_pkg::*;

// AI_TAG: FEATURE - Tests QoS arbitration under high load conditions
// AI_TAG: FEATURE - Validates priority enforcement and starvation prevention
// AI_TAG: FEATURE - Tests bandwidth allocation and fairness mechanisms
// AI_TAG: FEATURE - Stress tests with bursty and sustained traffic patterns

module qos_stress_tb;

    // Testbench Parameters
    localparam integer CLK_PERIOD = 10; // AI_TAG: PARAM_DESC - Clock period for the testbench.
                                        // AI_TAG: PARAM_USAGE - Defines the simulation clock frequency.
                                        // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.
    localparam integer NUM_CORES = 8;   // AI_TAG: PARAM_DESC - Number of simulated cores/initiators for stress testing.
                                        // AI_TAG: PARAM_USAGE - Scales the traffic generation and QoS complexity.
                                        // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.
    localparam integer NUM_PRIORITIES = 4; // AI_TAG: PARAM_DESC - Number of QoS priority levels.
                                          // AI_TAG: PARAM_USAGE - Defines the granularity of QoS prioritization.
                                          // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.
    localparam integer MAX_TEST_CYCLES = 100000; // AI_TAG: PARAM_DESC - Maximum simulation cycles for the test.
                                                // AI_TAG: PARAM_USAGE - Prevents infinite simulation loops.
                                                // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.
    localparam integer STRESS_DURATION = 50000; // AI_TAG: PARAM_DESC - Duration of stress test phases in cycles.
                                                // AI_TAG: PARAM_USAGE - Controls the length of traffic generation.
                                                // AI_TAG: PARAM_CONSTRAINTS - Must be a positive integer.
    
    // QoS Parameters
    localparam integer HIGH_PRIORITY = 3;
    localparam integer MED_PRIORITY = 2;
    localparam integer LOW_PRIORITY = 1;
    localparam integer BACKGROUND_PRIORITY = 0;
    
    // Clock and Reset
    logic clk_i; // AI_TAG: PORT_DESC - Testbench clock.
                 // AI_TAG: PORT_CLK_DOMAIN - clk_i
    logic rst_ni; // AI_TAG: PORT_DESC - Active-low asynchronous reset.
                  // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
                  // AI_TAG: PORT_TIMING - Asynchronous
    
    // QoS Interface Array
    qos_arbiter_if qos_if [NUM_CORES] (.clk_i(clk_i), .rst_ni(rst_ni)); // AI_TAG: IF_TYPE - QoS Arbiter Interface Array
                                                                       // AI_TAG: IF_DESC - Array of interfaces connecting to the QoS arbiter, one per core.
                                                                       // AI_TAG: IF_CLOCKING - clk_i
                                                                       // AI_TAG: IF_RESET - rst_ni
    
    // Memory Interface
    memory_req_rsp_if mem_if (.clk_i(clk_i), .rst_ni(rst_ni)); // AI_TAG: IF_TYPE - Memory Request/Response Interface
                                                              // AI_TAG: IF_DESC - Interface to the simulated memory model.
                                                              // AI_TAG: IF_CLOCKING - clk_i
                                                              // AI_TAG: IF_RESET - rst_ni
    
    // Performance Monitoring
    logic [31:0] qos_violations; // AI_TAG: PORT_DESC - Counter for detected QoS violations.
                                 // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                 // AI_TAG: PORT_DEFAULT_STATE - '0
    logic [31:0] total_transactions; // AI_TAG: PORT_DESC - Total number of transactions processed.
                                     // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                     // AI_TAG: PORT_DEFAULT_STATE - '0
    logic [NUM_CORES-1:0] starvation_flags; // AI_TAG: PORT_DESC - Flags indicating if a core is experiencing starvation.
                                            // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                            // AI_TAG: PORT_DEFAULT_STATE - '0
    logic [31:0] bandwidth_utilization; // AI_TAG: PORT_DESC - Overall memory bandwidth utilization percentage.
                                        // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                        // AI_TAG: PORT_DEFAULT_STATE - '0
    
    // Test State
    typedef enum logic [3:0] {
        TEST_INIT,
        TEST_BASIC_PRIORITY,
        TEST_STARVATION_PREVENTION,
        TEST_BANDWIDTH_ALLOCATION,
        TEST_BURST_HANDLING,
        TEST_PRIORITY_INVERSION,
        TEST_FAIRNESS_ENFORCEMENT,
        TEST_OVERSUBSCRIPTION,
        TEST_DYNAMIC_PRIORITY,
        TEST_CLEANUP
    } test_state_e;
    
    test_state_e current_test;
    integer test_cycle_count;
    integer test_pass_count = 0;
    integer test_fail_count = 0;
    integer error_count = 0;
    
    // Traffic Generation
    typedef struct packed {
        logic [31:0] addr;
        logic [31:0] data;
        logic [3:0] strb;
        logic write;
        logic [7:0] id;
        logic [3:0] priority;
        logic [15:0] burst_length;
        integer issue_time;
        integer completion_time;
    } qos_transaction_t;
    
    qos_transaction_t transaction_queue [$]; // AI_TAG: INTERNAL_STORAGE - transaction_queue - Queue of all transactions generated.
                                             // AI_TAG: INTERNAL_STORAGE_TYPE - Queue
                                             // AI_TAG: INTERNAL_STORAGE_ACCESS - Read/write by traffic generators and monitors.
    qos_transaction_t pending_transactions [NUM_CORES][$]; // AI_TAG: INTERNAL_STORAGE - pending_transactions - Per-core queues of transactions awaiting completion.
                                                          // AI_TAG: INTERNAL_STORAGE_TYPE - Array of Queues
                                                          // AI_TAG: INTERNAL_STORAGE_ACCESS - Read/write by traffic generators and monitors.
    
    // Performance Tracking
    integer transactions_per_priority [NUM_PRIORITIES]; // AI_TAG: INTERNAL_STORAGE - transactions_per_priority - Counts transactions per QoS priority level.
                                                        // AI_TAG: INTERNAL_STORAGE_TYPE - Array
                                                        // AI_TAG: INTERNAL_STORAGE_ACCESS - Updated by monitors.
    integer latency_per_priority [NUM_PRIORITIES]; // AI_TAG: INTERNAL_STORAGE - latency_per_priority - Accumulates latency per QoS priority level.
                                                   // AI_TAG: INTERNAL_STORAGE_TYPE - Array
                                                   // AI_TAG: INTERNAL_STORAGE_ACCESS - Updated by monitors.
    integer bandwidth_per_core [NUM_CORES]; // AI_TAG: INTERNAL_STORAGE - bandwidth_per_core - Tracks bandwidth consumed by each core.
                                            // AI_TAG: INTERNAL_STORAGE_TYPE - Array
                                            // AI_TAG: INTERNAL_STORAGE_ACCESS - Updated by monitors.
    integer starvation_cycles [NUM_CORES]; // AI_TAG: INTERNAL_STORAGE - starvation_cycles - Tracks cycles a core has been waiting for access.
                                           // AI_TAG: INTERNAL_STORAGE_TYPE - Array
                                           // AI_TAG: INTERNAL_STORAGE_ACCESS - Updated by monitors.
    
    //=========================================================================
    // QoS Constants and Configuration
    //=========================================================================
    parameter integer QOS_WEIGHT_BASE = 32'h1000;
    parameter integer QOS_STARVATION_TIMEOUT_REG = 32'h1100;
    parameter integer QOS_CONTROL_REG = 32'h1104;
    parameter integer QOS_ENABLE_BIT = 1;
    
    //=========================================================================
    // QoS Test Variables and Data Structures
    //=========================================================================
    integer starvation_threshold = 1000; // AI_TAG: INTERNAL_STORAGE - starvation_threshold - Maximum cycles a core can wait before being considered starved.
                                         // AI_TAG: INTERNAL_STORAGE_TYPE - Integer
                                         // AI_TAG: INTERNAL_STORAGE_ACCESS - Read by starvation monitor.
    integer served_transactions_count = 0;
    integer priority_starvation_cycles[16]; // AI_TAG: INTERNAL_STORAGE - priority_starvation_cycles - Per-priority starvation tracking.
                                            // AI_TAG: INTERNAL_STORAGE_TYPE - Array
                                            // AI_TAG: INTERNAL_STORAGE_ACCESS - Updated by monitors.
    real core_bandwidth_weight[NUM_CORES]; // AI_TAG: INTERNAL_STORAGE - core_bandwidth_weight - Configured bandwidth weights for each core.
                                          // AI_TAG: INTERNAL_STORAGE_TYPE - Array
                                          // AI_TAG: INTERNAL_STORAGE_ACCESS - Configured by testbench.
    integer core_transaction_count[NUM_CORES]; // AI_TAG: INTERNAL_STORAGE - core_transaction_count - Counts transactions per core.
                                               // AI_TAG: INTERNAL_STORAGE_TYPE - Array
                                               // AI_TAG: INTERNAL_STORAGE_ACCESS - Updated by monitors.
    
    // Transaction queues and logs
    qos_transaction_t served_transactions[$]; // AI_TAG: INTERNAL_STORAGE - served_transactions - Log of all transactions served by the arbiter.
                                              // AI_TAG: INTERNAL_STORAGE_TYPE - Queue
                                              // AI_TAG: INTERNAL_STORAGE_ACCESS - Updated by monitors.
    
    //=========================================================================
    // DUT Instantiation
    //=========================================================================
    qos_arbiter #(
        .NUM_CORES(NUM_CORES),
        .NUM_PRIORITIES(NUM_PRIORITIES),
        .ENABLE_STARVATION_PREVENTION(1),
        .STARVATION_THRESHOLD(1000),
        .ENABLE_BANDWIDTH_ALLOCATION(1),
        .ENABLE_DYNAMIC_PRIORITY(1)
    ) dut ( // AI_TAG: IF_TYPE - QoS Arbiter Instance
            // AI_TAG: IF_DESC - Instance of the QoS Arbiter under test.
            // AI_TAG: IF_CLOCKING - clk_i
            // AI_TAG: IF_RESET - rst_ni
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // QoS interfaces from cores
        .qos_if(qos_if),
        
        // Memory interface
        .mem_if(mem_if.master),
        
        // Performance monitoring
        .qos_violations_o(qos_violations),
        .total_transactions_o(total_transactions),
        .starvation_flags_o(starvation_flags),
        .bandwidth_utilization_o(bandwidth_utilization)
    );
    
    // Memory Model
    memory_model #(
        .ACCESS_LATENCY(20),
        .BANDWIDTH_LIMIT(4), // Artificially limit bandwidth for stress testing
        .RANDOM_DELAYS(1)
    ) u_memory_model ( // AI_TAG: IF_TYPE - Memory Model Instance
                       // AI_TAG: IF_DESC - Behavioral memory model to simulate memory responses.
                       // AI_TAG: IF_CLOCKING - clk_i
                       // AI_TAG: IF_RESET - rst_ni
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .mem_if(mem_if.slave)
    );
    
    //=========================================================================
    // Clock and Reset Generation
    //=========================================================================
    initial begin
        clk_i = 1'b0;
        forever #(CLK_PERIOD/2) clk_i = ~clk_i;
    end
    
    initial begin
        rst_ni = 1'b0;
        repeat(10) @(posedge clk_i);
        rst_ni = 1'b1;
        $display("[%0t] Reset released", $time);
    end
    
    //=========================================================================
    // Main Test Sequence
    //=========================================================================
    initial begin
        initialize_testbench();
        wait(rst_ni);
        repeat(5) @(posedge clk_i);
        
        $display("\n=================================================================");
        $display("  QoS Stress Testing and Validation Suite");
        $display("=================================================================\n");
        
        // Execute comprehensive QoS test suite
        run_test(TEST_INIT, "Initialization and Basic Setup");
        run_test(TEST_BASIC_PRIORITY, "Basic Priority Enforcement");
        run_test(TEST_STARVATION_PREVENTION, "Starvation Prevention");
        run_test(TEST_BANDWIDTH_ALLOCATION, "Bandwidth Allocation");
        run_test(TEST_BURST_HANDLING, "Burst Traffic Handling");
        run_test(TEST_PRIORITY_INVERSION, "Priority Inversion Prevention");
        run_test(TEST_FAIRNESS_ENFORCEMENT, "Fairness Enforcement");
        run_test(TEST_OVERSUBSCRIPTION, "Oversubscription Handling");
        run_test(TEST_DYNAMIC_PRIORITY, "Dynamic Priority Adjustment");
        run_test(TEST_CLEANUP, "Cleanup and Final Validation");
        
        report_final_results();
        $finish;
    end
    
    //=========================================================================
    // Test Execution Framework
    //=========================================================================
    
    task initialize_testbench();
        current_test = TEST_INIT;
        test_cycle_count = 0;
        
        // Initialize all QoS interfaces
        for (int i = 0; i < NUM_CORES; i++) begin
            qos_if[i].req_valid = 1'b0;
            qos_if[i].req = '0;
            qos_if[i].rsp_ready = 1'b1;
        end
        
        // Clear performance counters
        for (int i = 0; i < NUM_PRIORITIES; i++) begin
            transactions_per_priority[i] = 0;
            latency_per_priority[i] = 0;
        end
        
        for (int i = 0; i < NUM_CORES; i++) begin
            bandwidth_per_core[i] = 0;
            starvation_cycles[i] = 0;
        end
    endtask
    
    task run_test(test_state_e test_phase, string test_name);
        $display("[%0t] Starting %s...", $time, test_name);
        current_test = test_phase;
        test_cycle_count = 0;
        
        case (test_phase)
            TEST_INIT: test_initialization();
            TEST_BASIC_PRIORITY: test_basic_priority_enforcement();
            TEST_STARVATION_PREVENTION: test_starvation_prevention();
            TEST_BANDWIDTH_ALLOCATION: test_bandwidth_allocation();
            TEST_BURST_HANDLING: test_burst_handling();
            TEST_PRIORITY_INVERSION: test_priority_inversion_prevention();
            TEST_FAIRNESS_ENFORCEMENT: test_fairness_enforcement();
            TEST_OVERSUBSCRIPTION: test_oversubscription_handling();
            TEST_DYNAMIC_PRIORITY: test_dynamic_priority_adjustment();
            TEST_CLEANUP: test_cleanup_validation();
        endcase
        
        $display("[%0t] Completed %s", $time, test_name);
        repeat(10) @(posedge clk_i);
    endtask
    
    //=========================================================================
    // Individual Test Implementations
    //=========================================================================
    
    task test_initialization();
        $display("  - Verifying QoS arbiter initialization");
        
        // Check that all interfaces are ready
        repeat(100) @(posedge clk_i);
        
        if (qos_violations == 0 && total_transactions == 0) begin
            $display("  ✅ QoS arbiter initialized correctly");
            test_pass_count++;
        end else begin
            $error("  ❌ QoS arbiter initialization failed");
            test_fail_count++;
        end
    endtask
    
    task test_basic_priority_enforcement();
        $display("  - Testing basic priority enforcement");
        
        // Generate transactions with different priorities
        fork
            // High priority traffic from core 0
            generate_priority_traffic(0, HIGH_PRIORITY, 50, 100);
            
            // Low priority traffic from core 1
            generate_priority_traffic(1, LOW_PRIORITY, 100, 200);
            
            // Monitor transaction ordering
            monitor_priority_enforcement();
        join
        
        // Verify high priority transactions completed first
        if (verify_priority_ordering()) begin
            $display("  ✅ Basic priority enforcement test PASSED");
            test_pass_count++;
        end else begin
            $error("  ❌ Basic priority enforcement test FAILED");
            test_fail_count++;
        end
    endtask
    
    task test_starvation_prevention();
        $display("  - Testing starvation prevention mechanism");
        
        // Generate heavy high-priority load
        fork
            // Continuous high priority from multiple cores
            generate_continuous_traffic(0, HIGH_PRIORITY, STRESS_DURATION/4);
            generate_continuous_traffic(1, HIGH_PRIORITY, STRESS_DURATION/4);
            generate_continuous_traffic(2, HIGH_PRIORITY, STRESS_DURATION/4);
            
            // Single low priority core
            generate_continuous_traffic(3, LOW_PRIORITY, STRESS_DURATION/2);
            
            // Monitor for starvation
            monitor_starvation_prevention();
        join
        
        if (verify_no_starvation()) begin
            $display("  ✅ Starvation prevention test PASSED");
            test_pass_count++;
        end else begin
            $error("  ❌ Starvation prevention test FAILED");
            test_fail_count++;
        end
    endtask
    
    task test_bandwidth_allocation();
        $display("  - Testing bandwidth allocation fairness");
        
        // Configure bandwidth weights for each core
        configure_bandwidth_weights();
        
        // Generate equal load from all cores
        fork
            for (int i = 0; i < NUM_CORES; i++) begin
                automatic int core_id = i;
                generate_bandwidth_test_traffic(core_id, MED_PRIORITY, STRESS_DURATION/4);
            end
        join_none
        
        monitor_bandwidth_allocation();
        
        wait_for_test_completion(STRESS_DURATION/2);
        
        if (verify_bandwidth_fairness()) begin
            $display("  ✅ Bandwidth allocation test PASSED");
            test_pass_count++;
        end else begin
            $error("  ❌ Bandwidth allocation test FAILED");
            test_fail_count++;
        end
    endtask
    
    task test_burst_handling();
        $display("  - Testing burst traffic handling");
        
        // Generate bursty traffic patterns
        fork
            // Core 0: Short intense bursts
            generate_burst_traffic(0, HIGH_PRIORITY, 10, 500, 1000);
            
            // Core 1: Long sustained bursts  
            generate_burst_traffic(1, MED_PRIORITY, 100, 100, 2000);
            
            // Core 2: Random bursts
            generate_random_burst_traffic(2, LOW_PRIORITY, STRESS_DURATION/4);
            
            // Background traffic
            generate_background_traffic();
            
            // Monitor burst handling
            monitor_burst_performance();
        join
        
        if (verify_burst_handling()) begin
            $display("  ✅ Burst traffic handling test PASSED");
            test_pass_count++;
        end else begin
            $error("  ❌ Burst traffic handling test FAILED");
            test_fail_count++;
        end
    endtask
    
    task test_priority_inversion_prevention();
        $display("  - Testing priority inversion prevention");
        
        // Create priority inversion scenario
        fork
            // High priority blocked by low priority holding resource
            create_priority_inversion_scenario();
            
            // Monitor for priority boosting
            monitor_priority_inversion();
        join
        
        if (verify_priority_inversion_handled()) begin
            $display("  ✅ Priority inversion prevention test PASSED");
            test_pass_count++;
        end else begin
            $error("  ❌ Priority inversion prevention test FAILED");
            test_fail_count++;
        end
    endtask
    
    task test_fairness_enforcement();
        $display("  - Testing fairness enforcement within priority levels");
        
        // Multiple cores at same priority level
        fork
            for (int i = 0; i < 4; i++) begin
                automatic int core_id = i;
                generate_fairness_test_traffic(core_id, MED_PRIORITY, STRESS_DURATION/3);
            end
        join_none
        
        monitor_fairness_metrics();
        wait_for_test_completion(STRESS_DURATION/2);
        
        if (verify_fairness_within_priority()) begin
            $display("  ✅ Fairness enforcement test PASSED");
            test_pass_count++;
        end else begin
            $error("  ❌ Fairness enforcement test FAILED");
            test_fail_count++;
        end
    endtask
    
    task test_oversubscription_handling();
        $display("  - Testing oversubscription handling");
        
        // Generate more traffic than system can handle
        fork
            for (int i = 0; i < NUM_CORES; i++) begin
                automatic int core_id = i;
                generate_oversubscription_traffic(core_id, 
                    (i % NUM_PRIORITIES), STRESS_DURATION/2);
            end
        join_none
        
        monitor_oversubscription_behavior();
        wait_for_test_completion(STRESS_DURATION);
        
        if (verify_graceful_degradation()) begin
            $display("  ✅ Oversubscription handling test PASSED");
            test_pass_count++;
        end else begin
            $error("  ❌ Oversubscription handling test FAILED");
            test_fail_count++;
        end
    endtask
    
    task test_dynamic_priority_adjustment();
        $display("  - Testing dynamic priority adjustment");
        
        // Generate traffic and dynamically change priorities
        fork
            generate_dynamic_priority_traffic();
            monitor_dynamic_adjustment();
        join
        
        if (verify_dynamic_priority_response()) begin
            $display("  ✅ Dynamic priority adjustment test PASSED");
            test_pass_count++;
        end else begin
            $error("  ❌ Dynamic priority adjustment test FAILED");
            test_fail_count++;
        end
    endtask
    
    task test_cleanup_validation();
        $display("  - Testing cleanup and final validation");
        
        // Drain all pending transactions
        drain_all_queues();
        
        // Verify system state
        repeat(100) @(posedge clk_i);
        
        if (verify_clean_shutdown()) begin
            $display("  ✅ Cleanup validation test PASSED");
            test_pass_count++;
        end else begin
            $error("  ❌ Cleanup validation test FAILED");
            test_fail_count++;
        end
    endtask
    
    //=========================================================================
    // Traffic Generation Tasks
    //=========================================================================
    
    task generate_priority_traffic(int core_id, int priority, int count, int interval);
        for (int i = 0; i < count; i++) begin
            qos_transaction_t trans;
            trans.addr = 32'h1000_0000 + (core_id * 32'h100_0000) + (i * 4);
            trans.data = $random();
            trans.strb = 4'b1111;
            trans.write = (i % 3) == 0;
            trans.id = 8'h10 + core_id;
            trans.priority = priority;
            trans.burst_length = 1;
            trans.issue_time = $time;
            
            send_qos_transaction(core_id, trans);
            
            repeat(interval) @(posedge clk_i);
        end
    endtask
    
    task generate_continuous_traffic(int core_id, int priority, int duration);
        integer cycle_count = 0;
        
        while (cycle_count < duration) begin
            qos_transaction_t trans;
            trans.addr = 32'h2000_0000 + (core_id * 32'h100_0000) + (cycle_count * 4);
            trans.data = $random();
            trans.strb = 4'b1111;
            trans.write = (cycle_count % 4) == 0;
            trans.id = 8'h20 + core_id;
            trans.priority = priority;
            trans.burst_length = 1;
            trans.issue_time = $time;
            
            if (qos_if[core_id].req_ready) begin
                send_qos_transaction(core_id, trans);
            end
            
            @(posedge clk_i);
            cycle_count++;
        end
    endtask
    
    task generate_burst_traffic(int core_id, int priority, int burst_size, 
                               int burst_interval, int duration);
        integer cycle_count = 0;
        
        while (cycle_count < duration) begin
            // Generate burst
            for (int i = 0; i < burst_size; i++) begin
                qos_transaction_t trans;
                trans.addr = 32'h3000_0000 + (core_id * 32'h100_0000) + 
                           (cycle_count * burst_size + i) * 4;
                trans.data = $random();
                trans.strb = 4'b1111;
                trans.write = (i % 2) == 0;
                trans.id = 8'h30 + core_id;
                trans.priority = priority;
                trans.burst_length = burst_size;
                trans.issue_time = $time;
                
                send_qos_transaction(core_id, trans);
                @(posedge clk_i);
            end
            
            // Wait for burst interval
            repeat(burst_interval) @(posedge clk_i);
            cycle_count += burst_size + burst_interval;
        end
    endtask
    
    //=========================================================================
    // Helper Tasks and Functions
    //=========================================================================
    
    task send_qos_transaction(int core_id, qos_transaction_t trans);
        @(posedge clk_i);
        qos_if[core_id].req_valid = 1'b1;
        qos_if[core_id].req.addr = trans.addr;
        qos_if[core_id].req.data = trans.data;
        qos_if[core_id].req.strb = trans.strb;
        qos_if[core_id].req.write = trans.write;
        qos_if[core_id].req.id = trans.id;
        qos_if[core_id].req.priority = trans.priority;
        
        pending_transactions[core_id].push_back(trans);
        
        wait(qos_if[core_id].req_ready);
        @(posedge clk_i);
        qos_if[core_id].req_valid = 1'b0;
    endtask
    
    task configure_bandwidth_weights();
        // Configure bandwidth allocation weights for different priority levels
        $display("    - Configuring bandwidth weights");
        
        // Set up QoS arbiter weights (higher priority gets more bandwidth)
        for (int prio = 0; prio < 16; prio++) begin
            // Calculate weight: higher priority = higher weight
            integer weight = (16 - prio) * 4; // Priority 15 gets weight 64, priority 0 gets weight 4
            
            // Write to QoS configuration register (via CSR interface)
            write_qos_config_register(QOS_WEIGHT_BASE + prio, weight);
        end
        
        // Configure anti-starvation timeouts
        write_qos_config_register(QOS_STARVATION_TIMEOUT_REG, 1000); // 1000 cycles max starvation
        
        // Enable QoS enforcement
        write_qos_config_register(QOS_CONTROL_REG, QOS_ENABLE_BIT);
        
        repeat(10) @(posedge clk_i); // Allow configuration to take effect
    endtask
    
    task monitor_priority_enforcement();
        // Monitor transaction ordering by priority
        fork
            forever begin
                wait(mem_if.req_valid && mem_if.req_ready);
                
                // Record transaction details
                qos_transaction_t current_trans;
                current_trans.addr = mem_if.req.addr;
                current_trans.data = mem_if.req.data;
                current_trans.priority = mem_if.req.qos.priority;
                current_trans.id = mem_if.req.id;
                current_trans.issue_time = $time;
                current_trans.strb = mem_if.req.strb;
                current_trans.write = mem_if.req.write;
                current_trans.burst_length = 1; // Single beat transaction
                
                // Check priority ordering
                if (served_transactions.size() > 0) begin
                    qos_transaction_t last_trans = served_transactions[$];
                    
                    // Verify higher priority was served first (within starvation window)
                    if (current_trans.priority < last_trans.priority && 
                        (current_trans.issue_time - last_trans.issue_time) < starvation_threshold) begin
                        $error("[%0t] Priority violation: Lower priority %0d served before higher priority %0d", 
                               $time, last_trans.priority, current_trans.priority);
                        qos_violations++;
                    end
                end
                
                served_transactions.push_back(current_trans);
                total_transactions++;
                
                // Track per-core statistics
                core_transaction_count[get_core_from_id(current_trans.id)]++;
                
                @(posedge clk_i);
            end
        join_none
    endtask
    
    function bit verify_priority_ordering();
        // Verify that higher priority transactions were served first
        bit ordering_correct = 1'b1;
        integer violations = 0;
        
        for (int i = 1; i < served_transactions.size(); i++) begin
            qos_transaction_t current = served_transactions[i];
            qos_transaction_t previous = served_transactions[i-1];
            
            // Check if lower priority was served while higher priority was waiting
            if (current.priority > previous.priority) begin
                // Look for any pending higher priority transactions
                for (int j = 0; j < NUM_CORES; j++) begin
                    for (int k = 0; k < pending_transactions[j].size(); k++) begin
                        qos_transaction_t pending = pending_transactions[j][k];
                        if (pending.priority < current.priority && 
                            pending.issue_time < current.issue_time &&
                            (current.issue_time - pending.issue_time) < starvation_threshold) begin
                            violations++;
                            ordering_correct = 1'b0;
                            $display("Priority ordering violation found");
                            break;
                        end
                    end
                    if (!ordering_correct) break;
                end
            end
        end
        
        $display("    Priority ordering violations: %0d", violations);
        return ordering_correct;
    end function
    
    function bit verify_no_starvation();
        // Check that no core was starved for excessive time
        bit no_starvation = 1'b1;
        
        for (int i = 0; i < NUM_CORES; i++) begin
            if (starvation_cycles[i] > starvation_threshold) begin
                $error("Core %0d starved for %0d cycles (threshold: %0d)", 
                       i, starvation_cycles[i], starvation_threshold);
                no_starvation = 1'b0;
            end
        end
        
        // Check for priority-level starvation
        for (int prio = 0; prio < 16; prio++) begin
            if (priority_starvation_cycles[prio] > starvation_threshold) begin
                $error("Priority level %0d starved for %0d cycles", 
                       prio, priority_starvation_cycles[prio]);
                no_starvation = 1'b0;
            end
        end
        
        return no_starvation;
    end function
    
    function bit verify_bandwidth_fairness();
        // Verify bandwidth was allocated fairly according to weights
        bit fairness_achieved = 1'b1;
        real total_weight = 0;
        real expected_bandwidth[NUM_CORES];
        real actual_bandwidth[NUM_CORES];
        
        // Calculate total weight
        for (int i = 0; i < NUM_CORES; i++) begin
            total_weight += core_bandwidth_weight[i];
        end
        
        // Calculate expected vs actual bandwidth
        for (int i = 0; i < NUM_CORES; i++) begin
            expected_bandwidth[i] = (core_bandwidth_weight[i] / total_weight) * 100.0;
            actual_bandwidth[i] = (real'(core_transaction_count[i]) / real'(total_transactions)) * 100.0;
            
            // Allow 10% tolerance for fairness
            real deviation = (actual_bandwidth[i] - expected_bandwidth[i]);
            if (deviation < 0) deviation = -deviation;
            
            if (deviation > 10.0) begin
                $error("Bandwidth fairness violation for core %0d: expected %.1f%%, got %.1f%%", 
                       i, expected_bandwidth[i], actual_bandwidth[i]);
                fairness_achieved = 1'b0;
            end
            
            $display("    Core %0d: Expected %.1f%% bandwidth, actual %.1f%%", 
                     i, expected_bandwidth[i], actual_bandwidth[i]);
        end
        
        return fairness_achieved;
    end function
    
    // Additional helper functions...
    task wait_for_test_completion(int cycles);
        repeat(cycles) @(posedge clk_i);
    endtask
    
    task drain_all_queues();
        // Wait for all pending transactions to complete
        while (|pending_transactions) begin
            @(posedge clk_i);
        end
    endtask
    
    function bit verify_clean_shutdown();
        return (qos_violations == 0) && (transaction_queue.size() == 0);
    end function
    
    task report_final_results();
        $display("\n=================================================================");
        $display("  QoS STRESS TEST RESULTS");
        $display("=================================================================");
        $display("  Tests Passed: %0d", test_pass_count);
        $display("  Tests Failed: %0d", test_fail_count);
        $display("  Total QoS Violations: %0d", qos_violations);
        $display("  Total Transactions: %0d", total_transactions);
        $display("  Bandwidth Utilization: %0d%%", bandwidth_utilization);
        
        if (test_fail_count == 0 && error_count == 0) begin
            $display("  RESULT: ALL QoS TESTS PASSED ✅");
        end else begin
            $display("  RESULT: SOME QoS TESTS FAILED ❌");
        end
        $display("=================================================================\n");
    endtask
    
    // Timeout protection
    initial begin
        #(MAX_TEST_CYCLES * CLK_PERIOD);
        $error("QoS testbench timeout");
        $finish;
    end

    //=========================================================================
    // QoS Helper Functions
    //=========================================================================
    function integer get_core_from_id(logic [7:0] transaction_id);
        // Extract core ID from transaction ID (assumes lower 2 bits encode core)
        return transaction_id[1:0];
    end function
    
    task write_qos_config_register(logic [31:0] addr, logic [31:0] data);
        // Write to QoS configuration register via CSR interface
        // This would typically use a configuration bus or CSR interface
        // For now, simulate the write with a display
        $display("    Writing QoS config: addr=0x%h, data=0x%h", addr, data);
        
        // In a real implementation, this would be:
        // csr_if.write(addr, data);
        // or similar CSR write mechanism
        
        @(posedge clk_i);
    endtask
    
    // Initialize QoS tracking structures
    initial begin
        // Initialize starvation cycle counters
        for (int i = 0; i < 16; i++) begin
            priority_starvation_cycles[i] = 0;
        end
        
        // Initialize core bandwidth weights (equal by default)
        for (int i = 0; i < NUM_CORES; i++) begin
            core_bandwidth_weight[i] = 25.0; // 25% each for 4 cores
            core_transaction_count[i] = 0;
        end
        
        // Initialize starvation cycle tracking
        for (int i = 0; i < NUM_CORES; i++) begin
            starvation_cycles[i] = 0;
        end
    end
    
    // Monitor starvation cycles
    always @(posedge clk_i) begin
        if (rst_ni) begin
            // Track core starvation
            for (int i = 0; i < NUM_CORES; i++) begin
                if (qos_if[i].req_valid && !qos_if[i].req_ready) begin
                    starvation_cycles[i]++;
                end else if (qos_if[i].req_valid && qos_if[i].req_ready) begin
                    starvation_cycles[i] = 0; // Reset on successful transaction
                end
            end
            
            // Track priority-level starvation
            for (int i = 0; i < NUM_CORES; i++) begin
                if (qos_if[i].req_valid && !qos_if[i].req_ready) begin
                    integer prio = qos_if[i].req.priority;
                    priority_starvation_cycles[prio]++;
                end
            end
        end
    end

endmodule : qos_stress_tb
//=============================================================================
// Dependencies: qos_arbiter.sv, memory_model.sv, riscv_config_pkg.sv, riscv_types_pkg.sv, riscv_qos_pkg.sv, riscv_mem_types_pkg.sv
//
// Instantiated In:
//   - N/A (Top-level testbench)
//
// Performance:
//   - Critical Path: N/A
//   - Max Frequency: N/A (Simulation Only)
//   - Area: N/A (Simulation Only)
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
//   - Testbench: qos_stress_tb.sv
//   - Test Vectors: Multiple directed and constrained-random test scenarios
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-05 | DesignAI           | Initial creation of QoS Stress testbench.
//=============================================================================