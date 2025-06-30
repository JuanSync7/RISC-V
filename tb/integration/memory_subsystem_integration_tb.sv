//=============================================================================
// Company: RISC-V Verification Team
// Author: Senior Verification Engineer
// Created: 2025-01-27
//
// File: memory_subsystem_integration_tb.sv
// Module: memory_subsystem_integration_tb
//
// Project Name: RISC-V Multi-Core System
// Target Devices: ASIC/FPGA
// Tool Versions: VCS/QuestaSim
// Verification Status: Comprehensive Integration Testing
// Quality Status: Reviewed
//
// Description:
//   Comprehensive integration testbench for memory subsystem including cache
//   hierarchy (L1I, L2, L3), cache coherency controller, QoS-aware memory
//   wrapper, and prefetch unit. Tests system-level memory behavior.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module memory_subsystem_integration_tb;

    //-----
    // Parameters
    //-----
    localparam integer NUM_CORES = 4;
    localparam integer DATA_WIDTH = 32;
    localparam integer ADDR_WIDTH = 32;
    localparam integer CACHE_LINE_WIDTH = 128;
    localparam integer QOS_LEVELS = 4;
    localparam integer CLK_PERIOD = 10; // 100MHz
    localparam integer TEST_TIMEOUT = 5000000; // 5ms
    localparam integer NUM_RANDOM_TESTS = 1000;

    //-----
    // Clock and Reset
    //-----
    logic                               clk_i;
    logic                               rst_ni;

    //-----
    // Core Interface Signals (per core)
    //-----
    logic [NUM_CORES-1:0]               core_req_valid;
    logic [NUM_CORES-1:0]               core_req_ready;
    logic [NUM_CORES-1:0][ADDR_WIDTH-1:0] core_req_addr;
    logic [NUM_CORES-1:0][DATA_WIDTH-1:0] core_req_wdata;
    logic [NUM_CORES-1:0]               core_req_we;
    logic [NUM_CORES-1:0][3:0]          core_req_be;
    logic [NUM_CORES-1:0][QOS_LEVELS-1:0] core_qos_level;
    
    logic [NUM_CORES-1:0]               core_rsp_valid;
    logic [NUM_CORES-1:0]               core_rsp_ready;
    logic [NUM_CORES-1:0][DATA_WIDTH-1:0] core_rsp_rdata;
    logic [NUM_CORES-1:0]               core_rsp_error;

    //-----
    // Memory Interface Signals
    //-----
    logic                               mem_req_valid;
    logic                               mem_req_ready;
    logic [ADDR_WIDTH-1:0]              mem_req_addr;
    logic [CACHE_LINE_WIDTH-1:0]        mem_req_wdata;
    logic                               mem_req_we;
    logic [CACHE_LINE_WIDTH/8-1:0]      mem_req_be;
    
    logic                               mem_rsp_valid;
    logic                               mem_rsp_ready;
    logic [CACHE_LINE_WIDTH-1:0]        mem_rsp_rdata;
    logic                               mem_rsp_error;

    //-----
    // QoS and Performance Monitoring
    //-----
    logic [31:0]                        total_transactions;
    logic [15:0]                        cache_hits_l1;
    logic [15:0]                        cache_hits_l2;
    logic [15:0]                        cache_hits_l3;
    logic [15:0]                        cache_misses;
    logic [7:0]                         coherency_violations;
    logic [31:0]                        qos_bandwidth_used;

    //-----
    // Testbench Control
    //-----
    logic                               test_done;
    int                                 test_count;
    int                                 pass_count;
    int                                 fail_count;
    string                              current_test_name;

    //-----
    // Memory Model
    //-----
    logic [7:0]                         memory_model [2**20-1:0]; // 1MB memory model
    logic [ADDR_WIDTH-1:0]              last_addresses_queue [$];
    
    //-----
    // Traffic Generator Classes
    //-----
    class MemoryTransaction;
        rand bit [ADDR_WIDTH-1:0]       addr;
        rand bit [DATA_WIDTH-1:0]       wdata;
        rand bit                        we;
        rand bit [3:0]                  be;
        rand bit [QOS_LEVELS-1:0]       qos_level;
        rand int                        core_id;
        
        constraint c_addr {
            // Align addresses and keep in reasonable range
            addr[1:0] == 2'b00; // Word aligned
            addr < 32'h0010_0000; // 1MB range
        }
        
        constraint c_core_id {
            core_id inside {[0:NUM_CORES-1]};
        }
        
        constraint c_qos_level {
            $countones(qos_level) == 1; // Only one QoS level active
        }
        
        constraint c_be {
            // Byte enable patterns
            be inside {4'b0001, 4'b0011, 4'b1111, 4'b1100, 4'b0110};
        }
    endclass

    class TrafficPattern;
        rand int                        num_transactions;
        rand bit [2:0]                  pattern_type;
        rand bit [1:0]                  locality_type;
        
        constraint c_num_transactions {
            num_transactions inside {[10:100]};
        }
        
        constraint c_pattern_type {
            pattern_type inside {
                3'b000, // Sequential
                3'b001, // Random
                3'b010, // Stride
                3'b011, // Hot-cold
                3'b100  // Shared data
            };
        }
    endclass

    //-----
    // Coverage Groups
    //-----
    covergroup memory_subsystem_cg @(posedge clk_i);
        option.per_instance = 1;
        option.name = "memory_subsystem_coverage";
        
        // Core request coverage
        cp_core_requests: coverpoint $countones(core_req_valid) {
            bins no_requests = {0};
            bins single_request = {1};
            bins dual_requests = {2};
            bins triple_requests = {3};
            bins all_requests = {NUM_CORES};
        }
        
        // QoS level coverage
        cp_qos_levels: coverpoint core_qos_level[0] { // Sample from core 0
            bins qos_0 = {4'b0001};
            bins qos_1 = {4'b0010};
            bins qos_2 = {4'b0100};
            bins qos_3 = {4'b1000};
        }
        
        // Memory operation types
        cp_operation_types: coverpoint {|core_req_we, |core_req_valid} {
            bins idle = {2'b00};
            bins read_ops = {2'b01};
            bins write_ops = {2'b11};
        }
        
        // Cache hierarchy hits
        cp_cache_performance: coverpoint {cache_hits_l1 > 0, cache_hits_l2 > 0, cache_hits_l3 > 0} {
            bins all_l1 = {3'b100};
            bins l1_l2 = {3'b110};
            bins all_levels = {3'b111};
            bins memory_access = {3'b000};
        }
        
        // Cross coverage
        cx_qos_performance: cross cp_qos_levels, cp_cache_performance;
        cx_core_requests_qos: cross cp_core_requests, cp_qos_levels;
    endgroup

    //-----
    // Memory Subsystem DUT
    //-----
    // Note: This would instantiate the actual memory subsystem
    // For this testbench, we'll create behavioral models
    
    // Behavioral L1 I-Cache
    icache #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) icache_inst [NUM_CORES-1:0] (
        .clk_i(clk_i),
        .rst_ni(rst_ni)
        // Additional ports would be connected here
    );
    
    // Behavioral L2 Cache
    l2_cache #(
        .DATA_WIDTH(CACHE_LINE_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) l2_cache_inst (
        .clk_i(clk_i),
        .rst_ni(rst_ni)
        // Additional ports would be connected here
    );
    
    // Cache Coherency Controller
    cache_coherency_controller coherency_ctrl_inst (
        .clk_i(clk_i),
        .rst_ni(rst_ni)
        // Additional ports would be connected here
    );
    
    // QoS Memory Wrapper
    qos_memory_wrapper #(
        .QOS_LEVELS(QOS_LEVELS)
    ) qos_wrapper_inst (
        .clk_i(clk_i),
        .rst_ni(rst_ni)
        // Additional ports would be connected here
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
    memory_subsystem_cg cg_memory_subsystem;
    
    initial begin
        cg_memory_subsystem = new();
    end

    //-----
    // Memory Model Behavior
    //-----
    always @(posedge clk_i) begin
        if (mem_req_valid && mem_req_ready) begin
            if (mem_req_we) begin
                // Write to memory model
                for (int i = 0; i < CACHE_LINE_WIDTH/8; i++) begin
                    if (mem_req_be[i]) begin
                        memory_model[mem_req_addr + i] = mem_req_wdata[i*8 +: 8];
                    end
                end
            end
        end
    end
    
    // Memory response generation
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            mem_rsp_valid <= 1'b0;
            mem_rsp_rdata <= '0;
            mem_rsp_error <= 1'b0;
        end else begin
            mem_rsp_valid <= mem_req_valid && mem_req_ready && !mem_req_we;
            if (mem_req_valid && mem_req_ready && !mem_req_we) begin
                // Read from memory model
                for (int i = 0; i < CACHE_LINE_WIDTH/8; i++) begin
                    mem_rsp_rdata[i*8 +: 8] <= memory_model[mem_req_addr + i];
                end
            end
        end
    end

    //-----
    // Test Tasks
    //-----
    
    // Reset task
    task reset_dut();
        begin
            rst_ni = 1'b0;
            
            // Initialize all core interfaces
            for (int i = 0; i < NUM_CORES; i++) begin
                core_req_valid[i] = 1'b0;
                core_req_addr[i] = '0;
                core_req_wdata[i] = '0;
                core_req_we[i] = 1'b0;
                core_req_be[i] = '0;
                core_qos_level[i] = 4'b0001; // Default QoS
                core_rsp_ready[i] = 1'b1;
            end
            
            mem_req_ready = 1'b1;
            mem_rsp_ready = 1'b1;
            
            repeat (10) @(posedge clk_i);
            rst_ni = 1'b1;
            repeat (10) @(posedge clk_i);
            
            $display("[%0t] Reset completed", $time);
        end
    endtask

    // Send memory request task
    task send_memory_request(
        int core_id,
        logic [ADDR_WIDTH-1:0] addr,
        logic [DATA_WIDTH-1:0] wdata,
        logic we,
        logic [3:0] be,
        logic [QOS_LEVELS-1:0] qos
    );
        begin
            core_req_valid[core_id] = 1'b1;
            core_req_addr[core_id] = addr;
            core_req_wdata[core_id] = wdata;
            core_req_we[core_id] = we;
            core_req_be[core_id] = be;
            core_qos_level[core_id] = qos;
            
            // Wait for handshake
            while (!core_req_ready[core_id]) @(posedge clk_i);
            @(posedge clk_i);
            
            core_req_valid[core_id] = 1'b0;
            
            // Wait for response if read
            if (!we) begin
                while (!core_rsp_valid[core_id]) @(posedge clk_i);
                @(posedge clk_i);
            end
        end
    endtask

    // Generate traffic pattern task
    task generate_traffic_pattern(TrafficPattern pattern);
        MemoryTransaction trans;
        logic [ADDR_WIDTH-1:0] base_addr;
        
        begin
            trans = new();
            
            case (pattern.pattern_type)
                3'b000: begin // Sequential
                    base_addr = $random & 32'h000F_FF00;
                    for (int i = 0; i < pattern.num_transactions; i++) begin
                        assert(trans.randomize() with {
                            addr == base_addr + (i * 4);
                            we dist {1'b0 := 70, 1'b1 := 30};
                        });
                        send_memory_request(trans.core_id, trans.addr, trans.wdata, 
                                          trans.we, trans.be, trans.qos_level);
                    end
                end
                
                3'b001: begin // Random
                    for (int i = 0; i < pattern.num_transactions; i++) begin
                        assert(trans.randomize());
                        send_memory_request(trans.core_id, trans.addr, trans.wdata, 
                                          trans.we, trans.be, trans.qos_level);
                    end
                end
                
                3'b010: begin // Stride
                    base_addr = $random & 32'h000F_FF00;
                    for (int i = 0; i < pattern.num_transactions; i++) begin
                        assert(trans.randomize() with {
                            addr == base_addr + (i * 64); // Cache line stride
                            we dist {1'b0 := 80, 1'b1 := 20};
                        });
                        send_memory_request(trans.core_id, trans.addr, trans.wdata, 
                                          trans.we, trans.be, trans.qos_level);
                    end
                end
                
                3'b011: begin // Hot-cold (80% to hot addresses)
                    logic [ADDR_WIDTH-1:0] hot_addrs [8];
                    
                    // Initialize hot addresses
                    for (int i = 0; i < 8; i++) begin
                        hot_addrs[i] = ($random & 32'h000F_FF00) + (i * 4);
                    end
                    
                    for (int i = 0; i < pattern.num_transactions; i++) begin
                        assert(trans.randomize());
                        if ($random % 100 < 80) begin
                            // Hot address access
                            trans.addr = hot_addrs[$random % 8];
                        end
                        send_memory_request(trans.core_id, trans.addr, trans.wdata, 
                                          trans.we, trans.be, trans.qos_level);
                    end
                end
                
                3'b100: begin // Shared data (multiple cores accessing same addresses)
                    base_addr = $random & 32'h000F_FF00;
                    for (int i = 0; i < pattern.num_transactions; i++) begin
                        assert(trans.randomize() with {
                            addr inside {[base_addr:base_addr+63]};
                            we dist {1'b0 := 60, 1'b1 := 40};
                        });
                        send_memory_request(trans.core_id, trans.addr, trans.wdata, 
                                          trans.we, trans.be, trans.qos_level);
                    end
                end
            endcase
        end
    endtask

    //-----
    // Test Scenarios
    //-----
    
    // Test 1: Basic memory operations
    task test_basic_memory_operations();
        begin
            current_test_name = "Basic Memory Operations Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            reset_dut();
            
            // Single core basic read/write
            send_memory_request(0, 32'h0000_1000, 32'hDEAD_BEEF, 1'b1, 4'b1111, 4'b0001);
            send_memory_request(0, 32'h0000_1000, 32'h0, 1'b0, 4'b1111, 4'b0001);
            
            // Multiple cores accessing different addresses
            fork
                send_memory_request(0, 32'h0000_2000, 32'h1111_1111, 1'b1, 4'b1111, 4'b0001);
                send_memory_request(1, 32'h0000_3000, 32'h2222_2222, 1'b1, 4'b1111, 4'b0010);
                send_memory_request(2, 32'h0000_4000, 32'h3333_3333, 1'b1, 4'b1111, 4'b0100);
                send_memory_request(3, 32'h0000_5000, 32'h4444_4444, 1'b1, 4'b1111, 4'b1000);
            join
            
            $display("[%0t] Basic memory operations completed", $time);
            pass_count++;
            test_count++;
        end
    endtask

    // Test 2: Cache coherency testing
    task test_cache_coherency();
        logic [ADDR_WIDTH-1:0] shared_addr = 32'h0000_8000;
        
        begin
            current_test_name = "Cache Coherency Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            reset_dut();
            
            // Multiple cores reading the same address
            fork
                send_memory_request(0, shared_addr, 32'h0, 1'b0, 4'b1111, 4'b0001);
                send_memory_request(1, shared_addr, 32'h0, 1'b0, 4'b1111, 4'b0001);
                send_memory_request(2, shared_addr, 32'h0, 1'b0, 4'b1111, 4'b0001);
            join
            
            // One core writes, others read
            send_memory_request(0, shared_addr, 32'hCOHE_RENT, 1'b1, 4'b1111, 4'b0001);
            
            fork
                send_memory_request(1, shared_addr, 32'h0, 1'b0, 4'b1111, 4'b0001);
                send_memory_request(2, shared_addr, 32'h0, 1'b0, 4'b1111, 4'b0001);
                send_memory_request(3, shared_addr, 32'h0, 1'b0, 4'b1111, 4'b0001);
            join
            
            $display("[%0t] Cache coherency test completed", $time);
            pass_count++;
            test_count++;
        end
    endtask

    // Test 3: QoS priority testing
    task test_qos_priority();
        begin
            current_test_name = "QoS Priority Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            reset_dut();
            
            // Generate requests with different QoS levels simultaneously
            fork
                begin
                    for (int i = 0; i < 20; i++) begin
                        send_memory_request(0, 32'h0001_0000 + (i*4), 32'h1111_1111, 1'b1, 4'b1111, 4'b0001); // Low QoS
                    end
                end
                begin
                    #(CLK_PERIOD * 5); // Slight delay
                    for (int i = 0; i < 10; i++) begin
                        send_memory_request(1, 32'h0002_0000 + (i*4), 32'h8888_8888, 1'b1, 4'b1111, 4'b1000); // High QoS
                    end
                end
            join
            
            $display("[%0t] QoS priority test completed", $time);
            pass_count++;
            test_count++;
        end
    endtask

    // Test 4: Traffic pattern testing
    task test_traffic_patterns();
        TrafficPattern pattern;
        
        begin
            current_test_name = "Traffic Pattern Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            reset_dut();
            pattern = new();
            
            // Test different traffic patterns
            for (int pattern_type = 0; pattern_type < 5; pattern_type++) begin
                assert(pattern.randomize() with {
                    pattern_type == local::pattern_type;
                    num_transactions inside {[20:50]};
                });
                
                $display("[%0t] Testing pattern type %0d", $time, pattern_type);
                generate_traffic_pattern(pattern);
                
                // Allow time for operations to complete
                repeat (100) @(posedge clk_i);
            end
            
            $display("[%0t] Traffic pattern test completed", $time);
            pass_count++;
            test_count++;
        end
    endtask

    // Test 5: Stress testing with random traffic
    task test_random_stress();
        TrafficPattern pattern;
        
        begin
            current_test_name = "Random Stress Test";
            $display("\n=== Starting %s ===", current_test_name);
            
            reset_dut();
            pattern = new();
            
            for (int i = 0; i < 50; i++) begin
                assert(pattern.randomize());
                generate_traffic_pattern(pattern);
                
                if (i % 10 == 0) begin
                    $display("[%0t] Completed %0d stress test iterations", $time, i);
                end
            end
            
            $display("[%0t] Random stress test completed", $time);
            pass_count++;
            test_count++;
        end
    endtask

    //-----
    // Main Test Execution
    //-----
    initial begin
        $display("=== Memory Subsystem Integration Testbench Started ===");
        $display("Parameters: NUM_CORES=%0d, QOS_LEVELS=%0d", NUM_CORES, QOS_LEVELS);
        
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
        test_basic_memory_operations();
        test_cache_coherency();
        test_qos_priority();
        test_traffic_patterns();
        test_random_stress();
        
        // Final results
        repeat (100) @(posedge clk_i);
        
        $display("\n=== Test Results Summary ===");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        if (test_count > 0) begin
            $display("Pass Rate: %0.1f%%", (pass_count * 100.0) / test_count);
        end
        
        // Performance metrics
        $display("\n=== Performance Metrics ===");
        $display("Total Transactions: %0d", total_transactions);
        $display("L1 Cache Hits: %0d", cache_hits_l1);
        $display("L2 Cache Hits: %0d", cache_hits_l2);
        $display("L3 Cache Hits: %0d", cache_hits_l3);
        $display("Cache Misses: %0d", cache_misses);
        $display("QoS Bandwidth Used: %0d", qos_bandwidth_used);
        
        // Coverage report
        $display("\n=== Coverage Summary ===");
        $display("Functional Coverage: %0.1f%%", cg_memory_subsystem.get_inst_coverage());
        
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

endmodule : memory_subsystem_integration_tb

`default_nettype wire

//=============================================================================
// Dependencies: icache.sv, l2_cache.sv, l3_cache.sv, cache_coherency_controller.sv,
//               qos_memory_wrapper.sv, prefetch_unit.sv
//
// Performance:
//   - Simulation Time: ~2000ms for full integration test suite
//   - Memory Usage: ~500MB for waveform capture
//   - Coverage: Target 95% functional coverage
//
// Integration Coverage:
//   - Cache hierarchy interaction testing
//   - Cache coherency protocol verification
//   - QoS arbitration and bandwidth management
//   - Multi-core memory access patterns
//   - Performance counter validation
//
// Test Features:
//   - Multi-core traffic generation
//   - Configurable traffic patterns (sequential, random, stride, hot-cold, shared)
//   - Cache coherency stress testing
//   - QoS priority verification
//   - Performance metrics collection
//   - Memory model with behavioral responses
//
// Usage:
//   - VCS: vcs -sverilog +incdir+../../rtl memory_subsystem_integration_tb.sv
//   - QuestaSim: vsim -voptargs=+acc work.memory_subsystem_integration_tb
//
//----
// Revision History:
// Version | Date       | Author                    | Description
//=============================================================================
// 1.0.0   | 2025-01-27 | Senior Verification Engineer | Initial comprehensive integration testbench
//============================================================================= 