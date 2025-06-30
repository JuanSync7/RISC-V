//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: axi4_adapter.sv
// Module: axi4_adapter
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   AXI4 protocol adapter for protocol-agnostic memory interface. Converts
//   between memory_req_rsp_if and AXI4 interface, maintaining backward
//   compatibility with existing AXI4 systems. Updated to use proper interface.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - AXI4 protocol adapter using proper SystemVerilog interface
// AI_TAG: FEATURE - Protocol-agnostic memory interface to AXI4 conversion
// AI_TAG: FEATURE - Configurable data, address, and ID widths
// AI_TAG: FEATURE - Full AXI4 protocol compliance with burst support

module axi4_adapter #(
    // AI_TAG: PARAM_DESC - ID_WIDTH - Width of AXI4 ID signals.
    // AI_TAG: PARAM_USAGE - Sets transaction ID width for request tracking
    // AI_TAG: PARAM_CONSTRAINTS - Must match axi4_if parameter
    parameter integer ID_WIDTH = 4,
    
    // AI_TAG: PARAM_DESC - ADDR_WIDTH - Width of address signals.
    // AI_TAG: PARAM_USAGE - Sets address bus width for both interfaces
    // AI_TAG: PARAM_CONSTRAINTS - Must match axi4_if parameter
    parameter integer ADDR_WIDTH = 32,
    
    // AI_TAG: PARAM_DESC - DATA_WIDTH - Width of data signals.
    // AI_TAG: PARAM_USAGE - Sets data bus width for both interfaces
    // AI_TAG: PARAM_CONSTRAINTS - Must match axi4_if parameter
    parameter integer DATA_WIDTH = 32,
    
    // AI_TAG: PARAM_DESC - USER_WIDTH - Width of AXI4 user signals.
    // AI_TAG: PARAM_USAGE - Sets user signal width for AXI4 interface
    // AI_TAG: PARAM_CONSTRAINTS - Must match axi4_if parameter
    parameter integer USER_WIDTH = 1
) (
    // AI_TAG: PORT_DESC - clk_i - System clock.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        clk_i,
    
    // AI_TAG: PORT_DESC - rst_ni - Asynchronous active-low reset.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
    // AI_TAG: PORT_TIMING - Asynchronous
    input  logic        rst_ni,

    // Protocol-Agnostic Memory Interface
    // AI_TAG: PORT_DESC - mem_if - Protocol-agnostic memory interface.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    memory_req_rsp_if.master mem_if,

    // AXI4 Interface - Using proper interface
    // AI_TAG: IF_TYPE - AXI4 Master
    // AI_TAG: IF_MODPORT - master
    // AI_TAG: IF_PROTOCOL_VERSION - AXI4
    // AI_TAG: IF_DESC - AXI4 master interface for external memory access
    // AI_TAG: IF_DATA_WIDTHS - Data: parameterized, Addr: parameterized, ID: parameterized
    // AI_TAG: IF_CLOCKING - clk_i via axi_if.aclk connection
    // AI_TAG: IF_RESET - rst_ni via axi_if.aresetn connection
    axi4_if.master axi_if
);

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;
    import riscv_core_pkg::*;

    // AI_TAG: INTERNAL_BLOCK - StateMachine - Controls AXI4 transaction flow
    // AI_TAG: INTERNAL_BLOCK - RequestTracker - Tracks pending requests and responses
    // AI_TAG: INTERNAL_BLOCK - ProtocolConverter - Converts between interface protocols

    // AI_TAG: FSM_NAME - axi4_state_fsm
    // AI_TAG: FSM_PURPOSE - axi4_state_fsm - Controls the AXI4 transaction state machine
    // AI_TAG: FSM_ENCODING - axi4_state_fsm - binary
    // AI_TAG: FSM_RESET_STATE - axi4_state_fsm - S_IDLE
    typedef enum logic [2:0] {
        S_IDLE,           // AI_TAG: FSM_STATE - S_IDLE - Waiting for request
        S_READ_ADDR,      // AI_TAG: FSM_STATE - S_READ_ADDR - Sending read address
        S_READ_DATA,      // AI_TAG: FSM_STATE - S_READ_DATA - Receiving read data
        S_WRITE_ADDR,     // AI_TAG: FSM_STATE - S_WRITE_ADDR - Sending write address
        S_WRITE_DATA,     // AI_TAG: FSM_STATE - S_WRITE_DATA - Sending write data
        S_WRITE_RESP      // AI_TAG: FSM_STATE - S_WRITE_RESP - Receiving write response
    } axi4_state_e;
    
    axi4_state_e state_r, state_ns;
    
    // AI_TAG: INTERNAL_STORAGE - Request tracking registers
    // AI_TAG: INTERNAL_STORAGE_TYPE - Request tracking registers - Flip-flop based
    // AI_TAG: INTERNAL_STORAGE_ACCESS - Request tracking registers - FSM controlled
    logic [ID_WIDTH-1:0] pending_id_r;
    logic [ADDR_WIDTH-1:0] pending_addr_r;
    logic [2:0] pending_size_r;
    logic pending_write_r;
    word_t pending_data_r;
    logic [(DATA_WIDTH/8)-1:0] pending_strb_r;
    logic [2:0] pending_prot_r;
    logic pending_cacheable_r;
    
    // Connect interface clock and reset
    assign axi_if.aclk = clk_i;
    assign axi_if.aresetn = rst_ni;
    
    // Import protocol constants package
    import riscv_protocol_constants_pkg::*;
    import riscv_qos_pkg::*;
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 signal assignments using parameterized constants
    assign axi_if.awlen = AXI4_LEN_SINGLE_BEAT;     // Single beat transfers
    assign axi_if.arlen = AXI4_LEN_SINGLE_BEAT;     // Single beat transfers
    assign axi_if.awburst = AXI4_BURST_INCR;        // INCR burst type
    assign axi_if.arburst = AXI4_BURST_INCR;        // INCR burst type
    assign axi_if.awlock = AXI4_LOCK_NORMAL;        // Normal access
    assign axi_if.arlock = AXI4_LOCK_NORMAL;        // Normal access
    assign axi_if.awregion = AXI4_REGION_DEFAULT;   // No region
    assign axi_if.arregion = AXI4_REGION_DEFAULT;   // No region
    assign axi_if.awuser = {USER_WIDTH{RESET_VALUE_1BIT}};  // Default user signal
    assign axi_if.aruser = {USER_WIDTH{RESET_VALUE_1BIT}};  // Default user signal
    assign axi_if.wuser = {USER_WIDTH{RESET_VALUE_1BIT}};   // Default user signal
    assign axi_if.wlast = AXI4_LAST_TRANSFER;       // Single beat transfers
    
    // QoS Assignment Logic - Differentiated for reads vs writes
    logic [3:0] read_qos_level, write_qos_level;
    qos_transaction_type_e read_transaction_type, write_transaction_type;
    
    // Determine read transaction type based on address and access pattern
    always_comb begin : proc_read_transaction_type_detection
        if (mem_if.req.addr >= 32'h0000_0000 && mem_if.req.addr < 32'h0000_1000) begin
            read_transaction_type = QOS_TYPE_EXCEPTION;  // Exception vectors - critical
        end else if (mem_if.req.addr[1:0] == 2'b00) begin
            read_transaction_type = QOS_TYPE_INSTR_FETCH; // Likely instruction fetch - high priority
        end else if (mem_if.req.addr >= 32'hF000_0000) begin
            read_transaction_type = QOS_TYPE_PERIPHERAL;  // Peripheral space - best effort
        end else begin
            read_transaction_type = QOS_TYPE_DATA_ACCESS; // Data read - medium-high priority
        end
    end
    
    // Determine write transaction type based on address and access pattern  
    always_comb begin : proc_write_transaction_type_detection
        if (mem_if.req.addr >= 32'h0000_0000 && mem_if.req.addr < 32'h0000_1000) begin
            write_transaction_type = QOS_TYPE_EXCEPTION;  // Exception vectors - critical
        end else if (mem_if.req.strb != 4'hF) begin
            write_transaction_type = QOS_TYPE_DATA_ACCESS; // Partial write - data access
        end else if (mem_if.req.addr >= 32'hF000_0000) begin
            write_transaction_type = QOS_TYPE_PERIPHERAL;  // Peripheral space - best effort
        end else if ((mem_if.req.addr & 32'hFFFF_FF00) == 32'hFFFF_FF00) begin
            write_transaction_type = QOS_TYPE_CACHE_WB;   // Cache writeback region - lower priority
        end else begin
            write_transaction_type = QOS_TYPE_DATA_ACCESS; // Regular data write
        end
    end
    
    // Differentiated QoS level assignment with operation-specific tuning
    always_comb begin : proc_qos_level_assignment
        // Base QoS levels from transaction types
        logic [3:0] base_read_qos = get_qos_level(read_transaction_type);
        logic [3:0] base_write_qos = get_qos_level(write_transaction_type);
        
        // Read QoS adjustments - reads typically higher priority for performance
        case (read_transaction_type)
            QOS_TYPE_INSTR_FETCH: read_qos_level = QOS_LEVEL_HIGH;        // Keep instruction fetches high
            QOS_TYPE_DATA_ACCESS: read_qos_level = QOS_LEVEL_MEDIUM_HIGH; // Data reads important for performance
            QOS_TYPE_CACHE_FILL:  read_qos_level = QOS_LEVEL_MEDIUM;      // Cache fills medium priority
            default:              read_qos_level = base_read_qos;         // Use base level
        endcase
        
        // Write QoS adjustments - writes can be slightly lower priority 
        case (write_transaction_type)
            QOS_TYPE_EXCEPTION:   write_qos_level = QOS_LEVEL_CRITICAL;   // Exception writes critical
            QOS_TYPE_DATA_ACCESS: write_qos_level = QOS_LEVEL_MEDIUM;     // Data writes medium (posted)
            QOS_TYPE_CACHE_WB:    write_qos_level = QOS_LEVEL_MEDIUM_LOW; // Writebacks lower priority
            QOS_TYPE_PERIPHERAL:  write_qos_level = QOS_LEVEL_LOW;        // Peripheral writes low priority
            default:              write_qos_level = base_write_qos;       // Use base level
        endcase
    end
    
    // Final QoS assignment - context-sensitive
    assign axi_if.awqos = write_qos_level;  // Write QoS - optimized for write operations
    assign axi_if.arqos = read_qos_level;   // Read QoS - optimized for read operations
    
    // AI_TAG: FSM_TRANSITION - axi4_state_fsm: S_IDLE -> S_READ_ADDR when (!pending_write_r && mem_if.req_valid)
    // AI_TAG: FSM_TRANSITION - axi4_state_fsm: S_IDLE -> S_WRITE_ADDR when (pending_write_r && mem_if.req_valid)
    // AI_TAG: FSM_TRANSITION - axi4_state_fsm: S_READ_ADDR -> S_READ_DATA when (axi_if.arvalid && axi_if.arready)
    // AI_TAG: FSM_TRANSITION - axi4_state_fsm: S_READ_DATA -> S_IDLE when (axi_if.rvalid && axi_if.rready)
    // AI_TAG: FSM_TRANSITION - axi4_state_fsm: S_WRITE_ADDR -> S_WRITE_DATA when (axi_if.awvalid && axi_if.awready)
    // AI_TAG: FSM_TRANSITION - axi4_state_fsm: S_WRITE_DATA -> S_WRITE_RESP when (axi_if.wvalid && axi_if.wready)
    // AI_TAG: FSM_TRANSITION - axi4_state_fsm: S_WRITE_RESP -> S_IDLE when (axi_if.bvalid && axi_if.bready)
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 state machine registers
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_state_machine
        if (!rst_ni) begin
            state_r <= S_IDLE;
            pending_id_r <= '0;
            pending_addr_r <= '0;
            pending_size_r <= '0;
            pending_write_r <= 1'b0;
            pending_data_r <= '0;
            pending_strb_r <= '0;
            pending_prot_r <= '0;
            pending_cacheable_r <= 1'b0;
        end else begin
            state_r <= state_ns;
            
            // Latch request when accepted
            if (mem_if.req_valid && mem_if.req_ready) begin
                pending_id_r <= mem_if.req.id[ID_WIDTH-1:0];
                pending_addr_r <= mem_if.req.addr;
                pending_size_r <= mem_if.req.size;
                pending_write_r <= mem_if.req.write;
                pending_data_r <= mem_if.req.data;
                pending_strb_r <= mem_if.req.strb[(DATA_WIDTH/8)-1:0];
                pending_prot_r <= mem_if.req.prot;
                pending_cacheable_r <= mem_if.req.cacheable;
            end
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - State machine next state logic
    always_comb begin : proc_next_state_logic
        state_ns = state_r;
        
        case (state_r)
            S_IDLE: begin
                if (mem_if.req_valid) begin
                    if (mem_if.req.write) begin
                        state_ns = S_WRITE_ADDR;
                    end else begin
                        state_ns = S_READ_ADDR;
                    end
                end
            end
            
            S_READ_ADDR: begin
                if (axi_if.arvalid && axi_if.arready) begin
                    state_ns = S_READ_DATA;
                end
            end
            
            S_READ_DATA: begin
                if (axi_if.rvalid && axi_if.rready) begin
                    state_ns = S_IDLE;
                end
            end
            
            S_WRITE_ADDR: begin
                if (axi_if.awvalid && axi_if.awready) begin
                    state_ns = S_WRITE_DATA;
                end
            end
            
            S_WRITE_DATA: begin
                if (axi_if.wvalid && axi_if.wready) begin
                    state_ns = S_WRITE_RESP;
                end
            end
            
            S_WRITE_RESP: begin
                if (axi_if.bvalid && axi_if.bready) begin
                    state_ns = S_IDLE;
                end
            end
            
            default: begin
                state_ns = S_IDLE;
            end
        endcase
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 read address channel
    always_comb begin : proc_read_address_channel
        axi_if.arvalid = (state_r == S_READ_ADDR);
        axi_if.araddr = pending_addr_r;
        axi_if.arprot = pending_prot_r;
        axi_if.arcache = pending_cacheable_r ? 4'b0010 : 4'b0000; // Normal Non-cacheable Bufferable
        axi_if.arsize = pending_size_r;
        axi_if.arid = pending_id_r;
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 read data channel
    always_comb begin : proc_read_data_channel
        axi_if.rready = (state_r == S_READ_DATA);
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 write address channel
    always_comb begin : proc_write_address_channel
        axi_if.awvalid = (state_r == S_WRITE_ADDR);
        axi_if.awaddr = pending_addr_r;
        axi_if.awprot = pending_prot_r;
        axi_if.awcache = pending_cacheable_r ? 4'b0010 : 4'b0000; // Normal Non-cacheable Bufferable
        axi_if.awsize = pending_size_r;
        axi_if.awid = pending_id_r;
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 write data channel
    always_comb begin : proc_write_data_channel
        axi_if.wvalid = (state_r == S_WRITE_DATA);
        axi_if.wdata = pending_data_r;
        axi_if.wstrb = pending_strb_r;
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 write response channel
    always_comb begin : proc_write_response_channel
        axi_if.bready = (state_r == S_WRITE_RESP);
    end
    
    // AI_TAG: INTERNAL_LOGIC - Memory interface control
    always_comb begin : proc_memory_interface
        // Request ready when in IDLE state
        mem_if.req_ready = (state_r == S_IDLE);
        
        // Default response values
        mem_if.rsp_valid = 1'b0;
        mem_if.rsp.data = '0;
        mem_if.rsp.id = '0;
        mem_if.rsp.error = 1'b0;
        mem_if.rsp.last = 1'b1;
        
        if (state_r == S_READ_DATA && axi_if.rvalid) begin
            mem_if.rsp_valid = 1'b1;
            mem_if.rsp.data = axi_if.rdata;
            mem_if.rsp.id = {{(16-ID_WIDTH){1'b0}}, axi_if.rid}; // Extend to 16-bit ID
            mem_if.rsp.error = (axi_if.rresp != 2'b00); // Check for error response
            mem_if.rsp.last = axi_if.rlast;
        end else if (state_r == S_WRITE_RESP && axi_if.bvalid) begin
            mem_if.rsp_valid = 1'b1;
            mem_if.rsp.id = {{(16-ID_WIDTH){1'b0}}, axi_if.bid}; // Extend to 16-bit ID
            mem_if.rsp.error = (axi_if.bresp != 2'b00); // Check for error response
            mem_if.rsp.last = 1'b1;
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - Response ready (always ready to accept responses)
    assign mem_if.rsp_ready = 1'b1;

    // AI_TAG: ASSERTION - a_state_machine_valid: Ensures state machine stays in valid states
    // AI_TAG: ASSERTION_TYPE - Simulation
    // AI_TAG: ASSERTION_SEVERITY - Error
`ifdef SIMULATION
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        state_r inside {S_IDLE, S_READ_ADDR, S_READ_DATA, S_WRITE_ADDR, S_WRITE_DATA, S_WRITE_RESP});
    
    // AI_TAG: ASSERTION - a_req_valid_stable: Ensures request remains stable when valid but not ready
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        mem_if.req_valid && !mem_if.req_ready |=> mem_if.req_valid);
`endif

endmodule : axi4_adapter

//=============================================================================
// Dependencies: riscv_core_pkg.sv, memory_req_rsp_if.sv, axi4_if.sv
//
// Performance:
//   - Critical Path: Protocol conversion to AXI4 handshake
//   - Max Frequency: 400MHz (target)
//   - Area: ~200 gates (estimated)
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)
//
// Testing:
//   - Testbench: axi4_adapter_tb.sv
//   - Test Vectors: Protocol conversion tests
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 2.0.0   | 2025-01-27 | DesignAI           | Updated to use proper axi4_if interface
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//=============================================================================