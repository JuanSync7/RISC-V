//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: inter_core_comm_if.sv
// Module: inter_core_comm_if
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Interface for direct inter-core communication. This interface defines
//   a point-to-point-like network between multiple cores and a central
//   routing/managing entity (the Core Manager). It allows any core to
//   send a message or interrupt signal to any other core in the system.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Provides dedicated send/receive channels for each core.
// AI_TAG: FEATURE - Supports configurable number of cores and message width.
// AI_TAG: FEATURE - Includes ready/valid handshake for all channels for robust flow control.

import riscv_inter_core_types_pkg::*;
import riscv_qos_pkg::*;  // Add QoS package import

interface inter_core_comm_if #(
    parameter integer NUM_CORES     = MAX_CORES,    // AI_TAG: PARAM_DESC - The total number of cores in the system.
                                            // AI_TAG: PARAM_USAGE - Determines the number of communication channels.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be > 1.
    parameter integer MSG_WIDTH     = INTER_CORE_MSG_WIDTH,   // AI_TAG: PARAM_DESC - The bit-width of the message payload.
                                            // AI_TAG: PARAM_USAGE - Defines the width of the send_message and recv_message signals.
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be > 0.
    parameter integer CORE_ID_WIDTH = $clog2(NUM_CORES) // AI_TAG: PARAM_DESC - The bit-width required to address any core.
                                                        // AI_TAG: PARAM_USAGE - Automatically calculated from NUM_CORES.
                                                        // AI_TAG: PARAM_CONSTRAINTS - N/A
) (
    input logic clk_i,   // AI_TAG: PORT_DESC - Main system clock for the interface.
                         // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input logic rst_ni   // AI_TAG: PORT_DESC - Asynchronous, active-low reset.
                         // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
);

    //---------------------------------------------------------------------------
    // Communication Signals from Core to Manager
    //---------------------------------------------------------------------------
    logic [NUM_CORES-1:0]                       send_valid_w;     // AI_TAG: PORT_DESC - Core 'i' asserts to indicate a valid message to send.
    logic [NUM_CORES-1:0] [CORE_ID_WIDTH-1:0]   send_dest_id_w;   // AI_TAG: PORT_DESC - The target core ID for the message from core 'i'.
    logic [NUM_CORES-1:0] [MSG_WIDTH-1:0]       send_message_w;   // AI_TAG: PORT_DESC - The message payload from core 'i'.
    logic [NUM_CORES-1:0]                       send_ready_w;     // AI_TAG: PORT_DESC - Manager asserts to indicate it's ready for a message from core 'i'.

    //---------------------------------------------------------------------------
    // Communication Signals from Manager to Core
    //---------------------------------------------------------------------------
    logic [NUM_CORES-1:0]                       recv_valid_w;     // AI_TAG: PORT_DESC - Manager asserts to indicate a valid message for core 'i'.
    logic [NUM_CORES-1:0] [CORE_ID_WIDTH-1:0]   recv_source_id_w; // AI_TAG: PORT_DESC - The source core ID of the message for core 'i'.
    logic [NUM_CORES-1:0] [MSG_WIDTH-1:0]       recv_message_w;   // AI_TAG: PORT_DESC - The message payload for core 'i'.
    logic [NUM_CORES-1:0]                       recv_ready_w;     // AI_TAG: PORT_DESC - Core 'i' asserts to indicate it's ready for a message from the manager.

    //---------------------------------------------------------------------------
    // Modports
    //---------------------------------------------------------------------------

    // Modport for a single core instance. A core 'i' connects to this modport.
    // Example Usage in core 'i': inter_core_comm_if.core[i] core_comm_if;
    modport core (
        output send_valid_w,
        output send_dest_id_w,
        output send_message_w,
        input  send_ready_w,

        input  recv_valid_w,
        input  recv_source_id_w,
        input  recv_message_w,
        output recv_ready_w
    );

    // Modport for the central communication manager/router.
    // It sees all channels from all cores.
    modport manager (
        input  send_valid_w,
        input  send_dest_id_w,
        input  send_message_w,
        output send_ready_w,

        output recv_valid_w,
        output recv_source_id_w,
        output recv_message_w,
        input  recv_ready_w
    );

    // Original communication signals
    logic [NUM_CORES-1:0][NUM_CORES-1:0] msg_valid;
    logic [NUM_CORES-1:0][NUM_CORES-1:0] msg_ready;
    inter_core_msg_t [NUM_CORES-1:0][NUM_CORES-1:0] msg_data;

    // --- QoS-Enhanced Communication Signals ---
    qos_config_t [NUM_CORES-1:0][NUM_CORES-1:0] msg_qos_config;     // QoS config per message
    logic [NUM_CORES-1:0][NUM_CORES-1:0] urgent_msg;                // Urgent message flag
    logic [NUM_CORES-1:0][NUM_CORES-1:0] guaranteed_delivery;       // Guaranteed delivery flag
    
    // --- QoS Communication Types ---
    typedef enum logic [2:0] {
        INTER_CORE_MSG_CACHE_COHERENCY = 3'b000,
        INTER_CORE_MSG_INTERRUPT = 3'b001,
        INTER_CORE_MSG_DEBUG = 3'b010,
        INTER_CORE_MSG_SYNC = 3'b011,
        INTER_CORE_MSG_DATA = 3'b100,
        INTER_CORE_MSG_BARRIER = 3'b101,
        INTER_CORE_MSG_EXCEPTION = 3'b110,
        INTER_CORE_MSG_PERFORMANCE = 3'b111
    } inter_core_msg_type_e;
    
    inter_core_msg_type_e [NUM_CORES-1:0][NUM_CORES-1:0] msg_type;
    
    // --- QoS Priority Levels for Inter-Core Messages ---
    function automatic qos_level_e get_inter_core_qos_level(
        input inter_core_msg_type_e msg_type
    );
        case (msg_type)
            INTER_CORE_MSG_DEBUG:          return QOS_LEVEL_CRITICAL;
            INTER_CORE_MSG_EXCEPTION:      return QOS_LEVEL_CRITICAL;
            INTER_CORE_MSG_INTERRUPT:      return QOS_LEVEL_HIGH;
            INTER_CORE_MSG_CACHE_COHERENCY: return QOS_LEVEL_HIGH;
            INTER_CORE_MSG_SYNC:           return QOS_LEVEL_MEDIUM_HIGH;
            INTER_CORE_MSG_BARRIER:        return QOS_LEVEL_MEDIUM_HIGH;
            INTER_CORE_MSG_DATA:           return QOS_LEVEL_MEDIUM;
            INTER_CORE_MSG_PERFORMANCE:   return QOS_LEVEL_LOW;
            default:                       return QOS_LEVEL_MEDIUM;
        endcase
    endfunction
    
    // --- QoS Configuration Generation ---
    function automatic qos_config_t generate_inter_core_qos_config(
        input inter_core_msg_type_e msg_type,
        input logic [3:0] src_core_id,
        input logic [3:0] dst_core_id
    );
        qos_config_t qos_config;
        
        qos_config.qos_level = get_inter_core_qos_level(msg_type);
        qos_config.core_id = src_core_id;
        
        case (msg_type)
            INTER_CORE_MSG_DEBUG: begin
                qos_config.transaction_type = QOS_TYPE_DEBUG;
                qos_config.urgent = 1'b1;
                qos_config.guaranteed_bw = 1'b1;
                qos_config.weight = QOS_WEIGHT_CRITICAL;
                qos_config.max_latency_cycles = 16'd5;
                qos_config.preemptable = 1'b0;
                qos_config.real_time = 1'b1;
            end
            
            INTER_CORE_MSG_EXCEPTION: begin
                qos_config.transaction_type = QOS_TYPE_EXCEPTION;
                qos_config.urgent = 1'b1;
                qos_config.guaranteed_bw = 1'b1;
                qos_config.weight = QOS_WEIGHT_CRITICAL;
                qos_config.max_latency_cycles = 16'd10;
                qos_config.preemptable = 1'b0;
                qos_config.real_time = 1'b1;
            end
            
            INTER_CORE_MSG_INTERRUPT: begin
                qos_config.transaction_type = QOS_TYPE_INTERRUPT;
                qos_config.urgent = 1'b1;
                qos_config.guaranteed_bw = 1'b1;
                qos_config.weight = QOS_WEIGHT_HIGH;
                qos_config.max_latency_cycles = 16'd15;
                qos_config.preemptable = 1'b0;
                qos_config.real_time = 1'b1;
            end
            
            INTER_CORE_MSG_CACHE_COHERENCY: begin
                qos_config.transaction_type = QOS_TYPE_CACHE_COHERENCY;
                qos_config.urgent = 1'b1;
                qos_config.guaranteed_bw = 1'b1;
                qos_config.weight = QOS_WEIGHT_HIGH;
                qos_config.max_latency_cycles = 16'd20;
                qos_config.preemptable = 1'b0;
                qos_config.real_time = 1'b0;
            end
            
            INTER_CORE_MSG_SYNC: begin
                qos_config.transaction_type = QOS_TYPE_SYNCHRONIZATION;
                qos_config.urgent = 1'b0;
                qos_config.guaranteed_bw = 1'b1;
                qos_config.weight = QOS_WEIGHT_MEDIUM;
                qos_config.max_latency_cycles = 16'd50;
                qos_config.preemptable = 1'b1;
                qos_config.real_time = 1'b0;
            end
            
            INTER_CORE_MSG_BARRIER: begin
                qos_config.transaction_type = QOS_TYPE_SYNCHRONIZATION;
                qos_config.urgent = 1'b0;
                qos_config.guaranteed_bw = 1'b1;
                qos_config.weight = QOS_WEIGHT_MEDIUM;
                qos_config.max_latency_cycles = 16'd100;
                qos_config.preemptable = 1'b1;
                qos_config.real_time = 1'b0;
            end
            
            INTER_CORE_MSG_DATA: begin
                qos_config.transaction_type = QOS_TYPE_DATA_READ;
                qos_config.urgent = 1'b0;
                qos_config.guaranteed_bw = 1'b0;
                qos_config.weight = QOS_WEIGHT_MEDIUM;
                qos_config.max_latency_cycles = 16'd200;
                qos_config.preemptable = 1'b1;
                qos_config.real_time = 1'b0;
            end
            
            INTER_CORE_MSG_PERFORMANCE: begin
                qos_config.transaction_type = QOS_TYPE_PERFORMANCE_MONITORING;
                qos_config.urgent = 1'b0;
                qos_config.guaranteed_bw = 1'b0;
                qos_config.weight = QOS_WEIGHT_LOW;
                qos_config.max_latency_cycles = 16'd1000;
                qos_config.preemptable = 1'b1;
                qos_config.real_time = 1'b0;
            end
            
            default: begin
                qos_config.transaction_type = QOS_TYPE_DATA_READ;
                qos_config.urgent = 1'b0;
                qos_config.guaranteed_bw = 1'b0;
                qos_config.weight = QOS_WEIGHT_MEDIUM;
                qos_config.max_latency_cycles = 16'd100;
                qos_config.preemptable = 1'b1;
                qos_config.real_time = 1'b0;
            end
        endcase
        
        // Common settings
        qos_config.bandwidth_percent = 8'd10;  // 10% baseline allocation
        qos_config.retry_limit = 3'd2;        // Allow 2 retries
        qos_config.ordered = 1'b1;            // Maintain order for correctness
        
        return qos_config;
    endfunction

    // --- QoS Monitoring Signals ---
    logic [NUM_CORES-1:0][NUM_CORES-1:0] qos_violation;
    logic [NUM_CORES-1:0][NUM_CORES-1:0][31:0] message_latency;
    logic [NUM_CORES-1:0][NUM_CORES-1:0][31:0] message_count;
    logic [NUM_CORES-1:0][NUM_CORES-1:0][31:0] dropped_messages;

    // --- Modports for Core Connection ---
    modport core (
        input  clk_i, rst_ni,
        
        // Original signals
        output msg_valid,
        input  msg_ready,
        output msg_data,
        
        // QoS-enhanced signals
        output msg_qos_config,
        output urgent_msg,
        output guaranteed_delivery,
        output msg_type,
        
        // QoS monitoring
        input  qos_violation,
        input  message_latency,
        input  message_count,
        input  dropped_messages
    );

    // --- Modports for Interconnect/Arbiter ---
    modport interconnect (
        input  clk_i, rst_ni,
        
        // Original signals
        input  msg_valid,
        output msg_ready,
        input  msg_data,
        
        // QoS-enhanced signals
        input  msg_qos_config,
        input  urgent_msg,
        input  guaranteed_delivery,
        input  msg_type,
        
        // QoS monitoring
        output qos_violation,
        output message_latency,
        output message_count,
        output dropped_messages
    );

    // --- QoS Convenience Tasks ---
    task automatic send_qos_message(
        input int src_core,
        input int dst_core,
        input inter_core_msg_t message,
        input inter_core_msg_type_e msg_type_in
    );
        msg_valid[src_core][dst_core] = 1'b1;
        msg_data[src_core][dst_core] = message;
        msg_type[src_core][dst_core] = msg_type_in;
        msg_qos_config[src_core][dst_core] = generate_inter_core_qos_config(
            msg_type_in, src_core[3:0], dst_core[3:0]
        );
        urgent_msg[src_core][dst_core] = (get_inter_core_qos_level(msg_type_in) >= QOS_LEVEL_HIGH);
        guaranteed_delivery[src_core][dst_core] = (get_inter_core_qos_level(msg_type_in) >= QOS_LEVEL_MEDIUM_HIGH);
    endtask
    
    task automatic send_debug_message(
        input int src_core,
        input int dst_core,
        input inter_core_msg_t message
    );
        send_qos_message(src_core, dst_core, message, INTER_CORE_MSG_DEBUG);
    endtask
    
    task automatic send_cache_coherency_message(
        input int src_core,
        input int dst_core,
        input inter_core_msg_t message
    );
        send_qos_message(src_core, dst_core, message, INTER_CORE_MSG_CACHE_COHERENCY);
    endtask
    
    task automatic send_interrupt_message(
        input int src_core,
        input int dst_core,
        input inter_core_msg_t message
    );
        send_qos_message(src_core, dst_core, message, INTER_CORE_MSG_INTERRUPT);
    endtask

    // --- QoS Assertion Checkers ---
    // Check that critical messages are not dropped
    genvar g_src, g_dst;
    generate
        for (g_src = 0; g_src < NUM_CORES; g_src++) begin : gen_qos_assertions_src
            for (g_dst = 0; g_dst < NUM_CORES; g_dst++) begin : gen_qos_assertions_dst
                if (g_src != g_dst) begin : gen_different_cores
                    
                    // Critical messages should not be dropped
                    property p_critical_no_drop;
                        @(posedge clk_i) disable iff (!rst_ni)
                        (msg_valid[g_src][g_dst] && 
                         msg_qos_config[g_src][g_dst].qos_level == QOS_LEVEL_CRITICAL) 
                        |-> ##[1:10] msg_ready[g_src][g_dst];
                    endproperty
                    
                    assert property (p_critical_no_drop) 
                        else $error("Critical inter-core message dropped: Core %0d -> Core %0d", g_src, g_dst);
                    
                    // Debug messages should have lowest latency
                    property p_debug_low_latency;
                        @(posedge clk_i) disable iff (!rst_ni)
                        (msg_valid[g_src][g_dst] && 
                         msg_type[g_src][g_dst] == INTER_CORE_MSG_DEBUG) 
                        |-> ##[1:5] msg_ready[g_src][g_dst];
                    endproperty
                    
                    assert property (p_debug_low_latency) 
                        else $error("Debug message exceeded latency requirement: Core %0d -> Core %0d", g_src, g_dst);
                        
                end
            end
        end
    endgenerate

endinterface : inter_core_comm_if

//=============================================================================
// Dependencies: None
//
// Performance:
//   - Critical Path: N/A (Interface definition only)
//   - Max Frequency: N/A
//   - Area: N/A
//
// Verification Coverage:
//   - Code Coverage: N/A
//   - Functional Coverage: N/A
//   - Branch Coverage: N/A
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: N/A
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: N/A
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.1.0   | 2025-06-28 | DesignAI           | Restructured for clarity, added arrayed modports and full flow control.
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//=============================================================================

`default_nettype wire 