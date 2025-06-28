//===========================================================================
// File: test_env.sv
// Description: Comprehensive test environment manager for RISC-V processor verification
// Author: RISC-V Team
// Date: 2024
// Version: 1.0
//===========================================================================

package test_env;

    import test_utils::*;
    import test_data::*;
    import scoreboard::*;
    import monitor::*;
    import driver::*;
    import checker::*;
    import coverage::*;
    import verification_plan::*;

    //===========================================================================
    // Test Environment Configuration
    //===========================================================================
    
    // Test environment modes
    typedef enum {
        TEST_ENV_DISABLED,
        TEST_ENV_BASIC,
        TEST_ENV_FULL,
        TEST_ENV_STRESS
    } test_env_mode_t;
    
    // Test environment statistics
    typedef struct packed {
        integer total_tests;
        integer passed_tests;
        integer failed_tests;
        integer skipped_tests;
        real pass_rate;
        time start_time;
        time end_time;
        checker_stats_t checker_stats;
        monitor_stats_t monitor_stats;
        driver_stats_t driver_stats;
        scoreboard_stats_t scoreboard_stats;
    } test_env_stats_t;
    
    //===========================================================================
    // Test Environment Class
    //===========================================================================
    
    class TestEnvironment;
        // Configuration
        test_env_mode_t mode;
        test_env_stats_t stats;
        
        // Verification components
        Scoreboard scoreboard;
        Monitor monitor;
        Driver driver;
        ProtocolChecker checker;
        
        // Coverage instances
        coverage::alu_cg alu_coverage;
        coverage::memory_cg memory_coverage;
        coverage::regfile_cg regfile_coverage;
        coverage::pipeline_cg pipeline_coverage;
        coverage::exception_cg exception_coverage;
        coverage::csr_op_cg csr_coverage;
        coverage::hazard_cg hazard_coverage;
        coverage::branch_prediction_cg branch_coverage;
        coverage::performance_cg performance_coverage;
        coverage::cache_cg cache_coverage;
        coverage::axi4_cg axi4_coverage;
        
        // Test management
        test_scenario_t current_test;
        bit test_running;
        integer test_timeout;
        
        // Constructor
        function new(test_env_mode_t initial_mode = TEST_ENV_BASIC);
            mode = initial_mode;
            stats.total_tests = 0;
            stats.passed_tests = 0;
            stats.failed_tests = 0;
            stats.skipped_tests = 0;
            stats.pass_rate = 0.0;
            stats.start_time = $time;
            test_running = 1'b0;
            test_timeout = 10000; // Default timeout in cycles
            
            // Initialize verification components
            initialize_components();
        endfunction
        
        //===========================================================================
        // Component Initialization
        //===========================================================================
        
        // Initialize all verification components
        function void initialize_components();
            // Initialize scoreboard
            scoreboard = new(SCOREBOARD_ENABLED);
            
            // Initialize monitor
            monitor = new(MONITOR_PASSIVE, scoreboard);
            
            // Initialize driver
            driver = new(DRIVER_BASIC, scoreboard, monitor);
            
            // Initialize checker
            checker = new(CHECKER_BASIC);
            
            // Initialize coverage groups
            initialize_coverage();
            
            $display("[%0t] [TEST_ENV] Components initialized in mode %s", 
                     $time, get_mode_string());
        endfunction
        
        // Initialize coverage groups
        function void initialize_coverage();
            if (mode == TEST_ENV_DISABLED) return;
            
            // Initialize coverage groups based on mode
            if (mode == TEST_ENV_BASIC || mode == TEST_ENV_FULL || mode == TEST_ENV_STRESS) begin
                alu_coverage = new();
                memory_coverage = new();
                regfile_coverage = new();
                pipeline_coverage = new();
                exception_coverage = new();
            end
            
            if (mode == TEST_ENV_FULL || mode == TEST_ENV_STRESS) begin
                csr_coverage = new();
                hazard_coverage = new();
                branch_coverage = new();
                performance_coverage = new();
                cache_coverage = new();
                axi4_coverage = new();
            end
            
            $display("[%0t] [TEST_ENV] Coverage groups initialized", $time);
        endfunction
        
        //===========================================================================
        // Test Execution Management
        //===========================================================================
        
        // Run a single test
        function bit run_test(test_scenario_t test);
            if (mode == TEST_ENV_DISABLED) return 1'b0;
            
            current_test = test;
            test_running = 1'b1;
            stats.total_tests++;
            
            $display("[%0t] [TEST_ENV] Starting test: %s", $time, test.test_name);
            $display("[%0t] [TEST_ENV] Description: %s", $time, test.description);
            $display("[%0t] [TEST_ENV] Timeout: %0d cycles", $time, test.timeout_cycles);
            
            // Reset all components
            reset_components();
            
            // Configure components based on test
            configure_components(test);
            
            // Run the test
            bit test_passed = execute_test(test);
            
            // Collect results
            collect_test_results(test, test_passed);
            
            test_running = 1'b0;
            
            return test_passed;
        endfunction
        
        // Execute a test scenario
        function bit execute_test(test_scenario_t test);
            integer cycle_count = 0;
            bit test_passed = 1'b1;
            
            // Start performance monitoring
            start_performance_monitoring();
            
            // Run driver
            fork
                driver.run();
            join_none
            
            // Monitor test execution
            while (cycle_count < test.timeout_cycles && !driver.is_complete()) begin
                @(posedge clk);
                cycle_count++;
                
                // Update performance statistics
                update_performance_stats(1'b1, 1'b0, 1'b0, 1'b0, 1'b0);
                
                // Check for timeout
                if (cycle_count >= test.timeout_cycles) begin
                    $display("[%0t] [TEST_ENV] Test timeout after %0d cycles", $time, cycle_count);
                    test_passed = 1'b0;
                    break;
                end
            end
            
            // Wait for driver to complete
            wait (driver.is_complete());
            
            // Stop performance monitoring
            print_performance_report();
            
            return test_passed;
        endfunction
        
        // Configure components for a specific test
        function void configure_components(test_scenario_t test);
            case (test.category)
                FUNCTIONAL_TEST: begin
                    driver.set_mode(DRIVER_BASIC);
                    monitor.set_mode(MONITOR_PASSIVE);
                    checker.set_mode(CHECKER_BASIC);
                end
                PERFORMANCE_TEST: begin
                    driver.set_mode(DRIVER_ADVANCED);
                    monitor.set_mode(MONITOR_ACTIVE);
                    checker.set_mode(CHECKER_BASIC);
                end
                STRESS_TEST: begin
                    driver.set_mode(DRIVER_STRESS);
                    monitor.set_mode(MONITOR_ACTIVE);
                    checker.set_mode(CHECKER_STRICT);
                end
                CORNER_CASE_TEST: begin
                    driver.set_mode(DRIVER_ADVANCED);
                    monitor.set_mode(MONITOR_ACTIVE);
                    checker.set_mode(CHECKER_STRICT);
                end
                default: begin
                    driver.set_mode(DRIVER_BASIC);
                    monitor.set_mode(MONITOR_PASSIVE);
                    checker.set_mode(CHECKER_BASIC);
                end
            endcase
        endfunction
        
        // Collect test results
        function void collect_test_results(test_scenario_t test, bit test_passed);
            if (test_passed) begin
                stats.passed_tests++;
                $display("[%0t] [TEST_ENV] Test PASSED: %s", $time, test.test_name);
            end else begin
                stats.failed_tests++;
                $display("[%0t] [TEST_ENV] Test FAILED: %s", $time, test.test_name);
            end
            
            // Print component reports
            if (mode == TEST_ENV_FULL || mode == TEST_ENV_STRESS) begin
                scoreboard.print_scoreboard_report();
                monitor.print_monitor_report();
                driver.print_driver_report();
                checker.print_checker_report();
            end
        endfunction
        
        //===========================================================================
        // Test Suite Management
        //===========================================================================
        
        // Run test suite by category
        function void run_test_suite(test_category_t category);
            if (mode == TEST_ENV_DISABLED) return;
            
            test_scenario_t tests[];
            tests = verification_plan::get_tests_by_category(category);
            
            $display("[%0t] [TEST_ENV] Running test suite for category: %s", 
                     $time, get_category_string(category));
            $display("[%0t] [TEST_ENV] Number of tests: %0d", $time, tests.size());
            
            for (int i = 0; i < tests.size(); i++) begin
                bit test_passed = run_test(tests[i]);
                
                // Check if we should continue based on test priority
                if (tests[i].priority == CRITICAL && !test_passed) begin
                    $display("[%0t] [TEST_ENV] Critical test failed, stopping test suite", $time);
                    break;
                end
            end
            
            $display("[%0t] [TEST_ENV] Test suite completed for category: %s", 
                     $time, get_category_string(category));
        endfunction
        
        // Run test suite by priority
        function void run_test_suite_by_priority(test_priority_t priority);
            if (mode == TEST_ENV_DISABLED) return;
            
            test_scenario_t tests[];
            tests = verification_plan::get_tests_by_priority(priority);
            
            $display("[%0t] [TEST_ENV] Running test suite for priority: %s", 
                     $time, get_priority_string(priority));
            $display("[%0t] [TEST_ENV] Number of tests: %0d", $time, tests.size());
            
            for (int i = 0; i < tests.size(); i++) begin
                bit test_passed = run_test(tests[i]);
                
                // For critical tests, stop on first failure
                if (priority == CRITICAL && !test_passed) begin
                    $display("[%0t] [TEST_ENV] Critical test failed, stopping test suite", $time);
                    break;
                end
            end
            
            $display("[%0t] [TEST_ENV] Test suite completed for priority: %s", 
                     $time, get_priority_string(priority));
        endfunction
        
        // Run regression test suite
        function void run_regression_suite();
            if (mode == TEST_ENV_DISABLED) return;
            
            $display("[%0t] [TEST_ENV] Starting regression test suite", $time);
            
            // Run tests by priority (critical first)
            run_test_suite_by_priority(CRITICAL);
            run_test_suite_by_priority(HIGH);
            run_test_suite_by_priority(MEDIUM);
            run_test_suite_by_priority(LOW);
            
            $display("[%0t] [TEST_ENV] Regression test suite completed", $time);
        endfunction
        
        //===========================================================================
        // Coverage Management
        //===========================================================================
        
        // Sample all coverage
        function void sample_coverage();
            if (mode == TEST_ENV_DISABLED) return;
            
            // Sample basic coverage
            if (alu_coverage != null) alu_coverage.sample();
            if (memory_coverage != null) memory_coverage.sample();
            if (regfile_coverage != null) regfile_coverage.sample();
            if (pipeline_coverage != null) pipeline_coverage.sample();
            if (exception_coverage != null) exception_coverage.sample();
            
            // Sample advanced coverage
            if (csr_coverage != null) csr_coverage.sample();
            if (hazard_coverage != null) hazard_coverage.sample();
            if (branch_coverage != null) branch_coverage.sample();
            if (performance_coverage != null) performance_coverage.sample();
            if (cache_coverage != null) cache_coverage.sample();
            if (axi4_coverage != null) axi4_coverage.sample();
        endfunction
        
        // Check coverage goals
        function bit check_coverage_goals();
            if (mode == TEST_ENV_DISABLED) return 1'b1;
            
            bit all_goals_met = verification_plan::check_coverage_goals();
            
            if (all_goals_met) begin
                $display("[%0t] [TEST_ENV] All coverage goals met", $time);
            end else begin
                $display("[%0t] [TEST_ENV] Some coverage goals not met", $time);
            end
            
            return all_goals_met;
        endfunction
        
        //===========================================================================
        // Component Management
        //===========================================================================
        
        // Reset all components
        function void reset_components();
            if (scoreboard != null) scoreboard.reset();
            if (monitor != null) monitor.reset();
            if (driver != null) driver.reset();
            if (checker != null) checker.reset();
        endfunction
        
        // Get component statistics
        function void get_component_stats();
            if (checker != null) stats.checker_stats = checker.get_stats();
            if (monitor != null) stats.monitor_stats = monitor.get_stats();
            if (driver != null) stats.driver_stats = driver.get_stats();
            if (scoreboard != null) stats.scoreboard_stats = scoreboard.get_stats();
        endfunction
        
        //===========================================================================
        // Utility Methods
        //===========================================================================
        
        // Get mode string
        function string get_mode_string();
            case (mode)
                TEST_ENV_DISABLED: return "DISABLED";
                TEST_ENV_BASIC: return "BASIC";
                TEST_ENV_FULL: return "FULL";
                TEST_ENV_STRESS: return "STRESS";
                default: return "UNKNOWN";
            endcase
        endfunction
        
        // Get category string
        function string get_category_string(test_category_t category);
            case (category)
                FUNCTIONAL_TEST: return "FUNCTIONAL";
                PERFORMANCE_TEST: return "PERFORMANCE";
                STRESS_TEST: return "STRESS";
                CORNER_CASE_TEST: return "CORNER_CASE";
                REGRESSION_TEST: return "REGRESSION";
                INTEGRATION_TEST: return "INTEGRATION";
                SYSTEM_TEST: return "SYSTEM";
                default: return "UNKNOWN";
            endcase
        endfunction
        
        // Get priority string
        function string get_priority_string(test_priority_t priority);
            case (priority)
                CRITICAL: return "CRITICAL";
                HIGH: return "HIGH";
                MEDIUM: return "MEDIUM";
                LOW: return "LOW";
                default: return "UNKNOWN";
            endcase
        endfunction
        
        // Calculate final statistics
        function void calculate_final_stats();
            stats.end_time = $time;
            if (stats.total_tests > 0) begin
                stats.pass_rate = real'(stats.passed_tests) / real'(stats.total_tests) * 100.0;
            end
            get_component_stats();
        endfunction
        
        // Print test environment report
        function void print_test_env_report();
            calculate_final_stats();
            $display("=== TEST ENVIRONMENT REPORT ===");
            $display("Mode: %s", get_mode_string());
            $display("Total Tests: %0d", stats.total_tests);
            $display("Passed: %0d", stats.passed_tests);
            $display("Failed: %0d", stats.failed_tests);
            $display("Skipped: %0d", stats.skipped_tests);
            $display("Pass Rate: %0.2f%%", stats.pass_rate);
            $display("Simulation Time: %0t", stats.end_time - stats.start_time);
            $display("===============================");
        endfunction
        
        // Set test environment mode
        function void set_mode(test_env_mode_t new_mode);
            mode = new_mode;
            initialize_components();
        endfunction
        
        // Set test timeout
        function void set_test_timeout(integer timeout);
            test_timeout = timeout;
        endfunction
        
        // Check if test is running
        function bit is_test_running();
            return test_running;
        endfunction
        
    endclass

endpackage : test_env 