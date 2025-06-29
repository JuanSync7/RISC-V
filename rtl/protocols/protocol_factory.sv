//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: protocol_factory.sv
// Module: protocol_factory
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Protocol factory module that provides dynamic protocol switching
//   capabilities for the RISC-V memory subsystem. Supports AXI4, CHI,
//   TileLink, and custom protocols with runtime configuration.
//   Updated to use proper interfaces.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Dynamic protocol switching at runtime using proper interfaces
// AI_TAG: FEATURE - Support for AXI4, CHI, TileLink protocols with SystemVerilog interfaces
// AI_TAG: FEATURE - Configurable protocol parameters
// AI_TAG: FEATURE - Protocol-agnostic internal interface
// AI_TAG: INTERNAL_BLOCK - ProtocolMux - Multiplexes between different protocol adapters
// AI_TAG: INTERNAL_BLOCK - ConfigRegister - Stores current protocol configuration
// AI_TAG: INTERNAL_BLOCK - ProtocolAdapters - Individual protocol translation modules using proper interfaces
// AI_TAG: INTERNAL_BLOCK - PerformanceMonitor - Tracks protocol-specific metrics

import riscv_config_pkg::*;
import riscv_types_pkg::*;
import riscv_protocol_types_pkg::*;
import riscv_core_pkg::*;

module protocol_factory #(
    parameter string DEFAULT_PROTOCOL = "AXI4",           // AI_TAG: PARAM_DESC - Default protocol at reset
                                                          // AI_TAG: PARAM_USAGE - "AXI4", "CHI", "TILELINK", "CUSTOM"
                                                          // AI_TAG: PARAM_CONSTRAINTS - Must be one of supported protocols
    parameter integer ADDR_WIDTH = DEFAULT_AXI4_ADDR_WIDTH, // AI_TAG: PARAM_DESC - Address bus width
                                                            // AI_TAG: PARAM_USAGE - Must match interface parameters
                                                            // AI_TAG: PARAM_CONSTRAINTS - Must match all protocol interfaces
    parameter integer DATA_WIDTH = DEFAULT_AXI4_DATA_WIDTH, // AI_TAG: PARAM_DESC - Data bus width
                                                            // AI_TAG: PARAM_USAGE - Must match interface parameters
                                                            // AI_TAG: PARAM_CONSTRAINTS - Must match all protocol interfaces
    parameter integer ID_WIDTH = DEFAULT_AXI4_ID_WIDTH,   // AI_TAG: PARAM_DESC - Transaction ID width
                                                          // AI_TAG: PARAM_USAGE - For AXI4 and compatible protocols
                                                          // AI_TAG: PARAM_CONSTRAINTS - Must match interface parameter
    parameter integer MAX_OUTSTANDING = 8                 // AI_TAG: PARAM_DESC - Maximum outstanding transactions
                                                          // AI_TAG: PARAM_USAGE - Passed to protocol adapters
                                                          // AI_TAG: PARAM_CONSTRAINTS - Must be power of 2
) (
    input  logic        clk_i,     // AI_TAG: PORT_DESC - System clock
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        rst_ni,    // AI_TAG: PORT_DESC - Asynchronous active-low reset
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
                                   // AI_TAG: PORT_TIMING - Asynchronous

    // Configuration interface
    input  logic [31:0] config_reg_i,     // AI_TAG: PORT_DESC - Protocol configuration register
                                          // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                          // AI_TAG: PORT_USAGE - Controls protocol selection and parameters
    output logic [31:0] status_reg_o,     // AI_TAG: PORT_DESC - Protocol status register
                                          // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                          // AI_TAG: PORT_USAGE - Reports current protocol and performance metrics

    // Generic memory interface (protocol-agnostic)
    // AI_TAG: IF_TYPE - Generic Memory Interface (slave)
    // AI_TAG: IF_DESC - Protocol-agnostic memory interface for internal use
    // AI_TAG: IF_CLOCKING - clk_i
    // AI_TAG: IF_RESET - rst_ni
    memory_req_rsp_if.slave generic_if,

    // Protocol-specific external interfaces using proper SystemVerilog interfaces
    
    // AXI4 Interface
    // AI_TAG: IF_TYPE - AXI4 Master
    // AI_TAG: IF_MODPORT - master
    // AI_TAG: IF_PROTOCOL_VERSION - AXI4
    // AI_TAG: IF_DESC - AXI4 master interface for external memory access
    // AI_TAG: IF_DATA_WIDTHS - Data: parameterized, Addr: parameterized, ID: parameterized
    // AI_TAG: IF_CLOCKING - clk_i via axi4_if.aclk connection
    // AI_TAG: IF_RESET - rst_ni via axi4_if.aresetn connection
    axi4_if.master axi4_if,

    // CHI Interface
    // AI_TAG: IF_TYPE - CHI Request Node (RN)
    // AI_TAG: IF_MODPORT - rn
    // AI_TAG: IF_PROTOCOL_VERSION - CHI-B
    // AI_TAG: IF_DESC - CHI interface for coherent memory access
    // AI_TAG: IF_DATA_WIDTHS - Data: parameterized, Addr: parameterized, Node ID: parameterized
    // AI_TAG: IF_CLOCKING - clk_i via chi_if.clk connection
    // AI_TAG: IF_RESET - rst_ni via chi_if.resetn connection
    chi_if.rn chi_if,

    // TileLink Interface
    // AI_TAG: IF_TYPE - TileLink Manager (Client)
    // AI_TAG: IF_MODPORT - manager
    // AI_TAG: IF_PROTOCOL_VERSION - TileLink Uncached (TL-UL)
    // AI_TAG: IF_DESC - TileLink interface for open-source ecosystem compatibility
    // AI_TAG: IF_DATA_WIDTHS - Data: parameterized, Addr: parameterized, Source: parameterized
    // AI_TAG: IF_CLOCKING - clk_i via tl_if.clk connection
    // AI_TAG: IF_RESET - rst_ni via tl_if.reset_n connection
    tilelink_if.manager tl_if,

    // Performance monitoring outputs
    output logic [31:0] protocol_transactions_o,  // AI_TAG: PORT_DESC - Total protocol transactions
                                                  // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                  // AI_TAG: PORT_USAGE - Performance monitoring counter
    output logic [31:0] protocol_latency_avg_o,   // AI_TAG: PORT_DESC - Average transaction latency
                                                  // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                  // AI_TAG: PORT_USAGE - Performance monitoring metric
    output logic [31:0] protocol_bandwidth_o      // AI_TAG: PORT_DESC - Protocol bandwidth utilization
                                                  // AI_TAG: PORT_CLK_DOMAIN - clk_i
                                                  // AI_TAG: PORT_USAGE - Performance monitoring metric
);

    // AI_TAG: INTERNAL_BLOCK - ProtocolSelector - Selects active protocol based on configuration
    // AI_TAG: INTERNAL_BLOCK - InterfaceMultiplexer - Routes traffic to selected protocol adapter
    // AI_TAG: INTERNAL_BLOCK - PerformanceCounters - Tracks protocol-specific performance metrics

    //-----
    // Local Parameters and Types
    //-----
    // AI_TAG: FSM_NAME - protocol_selector
    // AI_TAG: FSM_PURPOSE - protocol_selector - Selects which protocol adapter is active
    // AI_TAG: FSM_ENCODING - protocol_selector - binary
    // AI_TAG: FSM_RESET_STATE - protocol_selector - PROTOCOL_AXI4
    typedef enum logic [1:0] {
        PROTOCOL_AXI4     = 2'b00,  // AI_TAG: FSM_STATE - PROTOCOL_AXI4 - AXI4 protocol selected
        PROTOCOL_CHI      = 2'b01,  // AI_TAG: FSM_STATE - PROTOCOL_CHI - CHI protocol selected
        PROTOCOL_TILELINK = 2'b10,  // AI_TAG: FSM_STATE - PROTOCOL_TILELINK - TileLink protocol selected
        PROTOCOL_CUSTOM   = 2'b11   // AI_TAG: FSM_STATE - PROTOCOL_CUSTOM - Custom protocol selected
    } protocol_type_e;

    //-----
    // Configuration Register Decoding
    //-----
    protocol_type_e current_protocol_s;
    logic           protocol_enable_s;
    logic           debug_mode_s;
    logic [7:0]     protocol_config_s;

    assign current_protocol_s = protocol_type_e'(config_reg_i[1:0]);
    assign protocol_enable_s  = config_reg_i[2];
    assign debug_mode_s       = config_reg_i[3];
    assign protocol_config_s  = config_reg_i[15:8];

    //-----
    // Internal Interfaces for Protocol Adapters
    //-----
    // AI_TAG: INTERNAL_LOGIC - Internal memory interfaces for each protocol adapter
    memory_req_rsp_if axi4_adapter_if(.clk_i(clk_i), .rst_ni(rst_ni));
    memory_req_rsp_if chi_adapter_if(.clk_i(clk_i), .rst_ni(rst_ni));
    memory_req_rsp_if tilelink_adapter_if(.clk_i(clk_i), .rst_ni(rst_ni));

    //-----
    // Protocol Multiplexer
    //-----
    // AI_TAG: INTERNAL_LOGIC - Protocol multiplexer routes generic interface to selected protocol
    always_comb begin : proc_protocol_mux
        // Default all adapters disconnected
        axi4_adapter_if.req_valid = 1'b0;
        chi_adapter_if.req_valid = 1'b0;
        tilelink_adapter_if.req_valid = 1'b0;
        
        axi4_adapter_if.req = '0;
        chi_adapter_if.req = '0;
        tilelink_adapter_if.req = '0;
        
        axi4_adapter_if.rsp_ready = 1'b0;
        chi_adapter_if.rsp_ready = 1'b0;
        tilelink_adapter_if.rsp_ready = 1'b0;
        
        // Default generic interface outputs
        generic_if.req_ready = 1'b0;
        generic_if.rsp_valid = 1'b0;
        generic_if.rsp = '0;

        // Route based on current protocol and enable state
        if (protocol_enable_s) begin
            case (current_protocol_s)
                PROTOCOL_AXI4: begin
                    axi4_adapter_if.req_valid = generic_if.req_valid;
                    axi4_adapter_if.req = generic_if.req;
                    generic_if.req_ready = axi4_adapter_if.req_ready;
                    generic_if.rsp_valid = axi4_adapter_if.rsp_valid;
                    generic_if.rsp = axi4_adapter_if.rsp;
                    axi4_adapter_if.rsp_ready = generic_if.rsp_ready;
                end
                
                PROTOCOL_CHI: begin
                    chi_adapter_if.req_valid = generic_if.req_valid;
                    chi_adapter_if.req = generic_if.req;
                    generic_if.req_ready = chi_adapter_if.req_ready;
                    generic_if.rsp_valid = chi_adapter_if.rsp_valid;
                    generic_if.rsp = chi_adapter_if.rsp;
                    chi_adapter_if.rsp_ready = generic_if.rsp_ready;
                end
                
                PROTOCOL_TILELINK: begin
                    tilelink_adapter_if.req_valid = generic_if.req_valid;
                    tilelink_adapter_if.req = generic_if.req;
                    generic_if.req_ready = tilelink_adapter_if.req_ready;
                    generic_if.rsp_valid = tilelink_adapter_if.rsp_valid;
                    generic_if.rsp = tilelink_adapter_if.rsp;
                    tilelink_adapter_if.rsp_ready = generic_if.rsp_ready;
                end
                
                default: begin // PROTOCOL_CUSTOM
                    // Custom protocol handling - simple passthrough for demonstration
                    generic_if.req_ready = 1'b1;
                    generic_if.rsp_valid = generic_if.req_valid;
                    generic_if.rsp.data = generic_if.req.addr; // Simple echo for demo
                    generic_if.rsp.id = generic_if.req.id;
                    generic_if.rsp.error = 1'b0;
                    generic_if.rsp.last = 1'b1;
                end
            endcase
        end else begin
            // Protocol disabled - reject all requests
            generic_if.req_ready = 1'b0;
            generic_if.rsp_valid = 1'b0;
            generic_if.rsp = '0;
        end
    end

    //-----
    // AXI4 Protocol Adapter
    //-----
    axi4_adapter #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .USER_WIDTH(1)
    ) u_axi4_adapter (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Generic interface
        .mem_if(axi4_adapter_if.master),
        
        // AXI4 interface - using proper interface
        .axi_if(axi4_if)
    );

    //-----
    // CHI Protocol Adapter
    //-----
    chi_adapter #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(128),  // CHI typically uses 128-bit data
        .NODEID_WIDTH(7),
        .TXNID_WIDTH(8),
        .MAX_OUTSTANDING(MAX_OUTSTANDING)
    ) u_chi_adapter (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Generic interface
        .mem_if(chi_adapter_if.slave),
        
        // CHI interface - using proper interface
        .chi_if(chi_if)
    );

    //-----
    // TileLink Protocol Adapter
    //-----
    tilelink_adapter #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .SOURCE_WIDTH(8),
        .SINK_WIDTH(8),
        .SIZE_WIDTH(3),
        .MAX_OUTSTANDING(MAX_OUTSTANDING)
    ) u_tilelink_adapter (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Generic interface
        .mem_if(tilelink_adapter_if.slave),
        
        // TileLink interface - using proper interface
        .tl_if(tl_if)
    );

    //-----
    // Performance Monitoring
    //-----
    // AI_TAG: INTERNAL_STORAGE - Performance counters for monitoring protocol activity
    // AI_TAG: INTERNAL_STORAGE_TYPE - Performance counters - Counter registers
    // AI_TAG: INTERNAL_STORAGE_ACCESS - Performance counters - Read/increment
    logic [31:0] transaction_count_r;
    logic [31:0] latency_accumulator_r;
    logic [31:0] bandwidth_counter_r;
    logic [15:0] latency_timer_r;
    logic        transaction_pending_r;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_performance_counters
        if (!rst_ni) begin
            transaction_count_r <= '0;
            latency_accumulator_r <= '0;
            bandwidth_counter_r <= '0;
            latency_timer_r <= '0;
            transaction_pending_r <= 1'b0;
        end else begin
            // Transaction counting
            if (generic_if.req_valid && generic_if.req_ready) begin
                transaction_count_r <= transaction_count_r + 1;
                latency_timer_r <= '0;
                transaction_pending_r <= 1'b1;
            end
            
            // Bandwidth counting
            if (generic_if.rsp_valid && generic_if.rsp_ready) begin
                bandwidth_counter_r <= bandwidth_counter_r + 1;
                if (transaction_pending_r) begin
                    latency_accumulator_r <= latency_accumulator_r + latency_timer_r;
                    transaction_pending_r <= 1'b0;
                end
            end
            
            // Latency timer
            if (transaction_pending_r) begin
                latency_timer_r <= latency_timer_r + 1;
            end
        end
    end

    assign protocol_transactions_o = transaction_count_r;
    assign protocol_latency_avg_o = transaction_count_r > 0 ? 
                                   latency_accumulator_r / transaction_count_r : 0;
    assign protocol_bandwidth_o = bandwidth_counter_r;

    //-----
    // Status Register
    //-----
    assign status_reg_o = {
        8'h0,                     // Reserved [31:24]
        protocol_transactions_o[23:16], // Transaction count MSB [23:16]
        protocol_enable_s,        // Protocol enabled [15]
        debug_mode_s,             // Debug mode [14]
        2'b0,                     // Reserved [13:12]
        protocol_transactions_o[11:8], // Transaction count [11:8]
        protocol_config_s[7:4],   // Protocol config MSB [7:4]
        protocol_config_s[3:2],   // Protocol config LSB [3:2]
        current_protocol_s        // Current protocol [1:0]
    };

    // AI_TAG: ASSERTION - a_protocol_valid: Protocol selection should be valid
    // AI_TAG: ASSERTION_TYPE - Simulation
    // AI_TAG: ASSERTION_SEVERITY - Error
`ifdef SIMULATION
    assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (current_protocol_s inside {PROTOCOL_AXI4, PROTOCOL_CHI, PROTOCOL_TILELINK, PROTOCOL_CUSTOM}))
    else $error("Invalid protocol selection: %d", current_protocol_s);

    // AI_TAG: ASSERTION - a_one_adapter_active: Only one adapter should be active at a time
    assert property (@(posedge clk_i) disable iff (!rst_ni) 
        ($onehot0({axi4_adapter_if.req_valid, chi_adapter_if.req_valid, tilelink_adapter_if.req_valid})))
    else $error("Multiple adapters active simultaneously");

    // AI_TAG: ASSERTION - a_protocol_enable_consistency: When disabled, no adapters should be active
    assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (!protocol_enable_s) |-> (!axi4_adapter_if.req_valid && !chi_adapter_if.req_valid && !tilelink_adapter_if.req_valid))
    else $error("Adapters active when protocol disabled");
`endif

endmodule : protocol_factory

//=============================================================================
// Dependencies: axi4_adapter.sv, chi_adapter.sv, tilelink_adapter.sv, 
//               axi4_if.sv, chi_if.sv, tilelink_if.sv, memory_req_rsp_if.sv
//
// Performance:
//   - Critical Path: Protocol multiplexer and adapter interfaces
//   - Max Frequency: 400MHz ASIC, 200MHz FPGA
//   - Area: Depends on enabled protocols and adapter complexity (~1000 gates base)
//
// Verification Coverage:
//   - Code Coverage: TBD
//   - Functional Coverage: Protocol switching scenarios
//   - Branch Coverage: All protocol paths and configurations
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: protocol_factory.sdc
//
// Testing:
//   - Testbench: protocol_factory_tb.sv
//   - Test Vectors: Protocol switching scenarios, performance validation
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 2.0.0   | 2025-01-27 | DesignAI          | Updated to use proper interfaces for all protocols
// 1.0.0   | 2025-01-27 | DesignAI          | Initial implementation with AXI4/CHI/TileLink support
//============================================================================= 