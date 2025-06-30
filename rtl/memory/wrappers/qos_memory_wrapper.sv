//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: qos_memory_wrapper.sv
// Module: qos_memory_wrapper
//
// Project Name: RISC-V RV32IM QoS-Enhanced Memory Wrapper
// Target Devices: ASIC/FPGA
//
// Description:
//   QoS-enhanced memory wrapper that provides QoS-aware routing, priority
//   scheduling, and memory bandwidth management. Integrates with the QoS
//   system to ensure critical memory accesses receive appropriate priority.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module qos_memory_wrapper #(
    parameter integer NUM_PORTS = 4,           // Number of input ports
    parameter integer ADDR_WIDTH = 32,
    parameter integer DATA_WIDTH = 32,
    parameter integer OUTSTANDING_REQS = 16,   // Max outstanding requests
    parameter integer QOS_QUEUE_DEPTH = 8      // QoS queue depth per priority
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    // QoS-enhanced input ports
    memory_req_rsp_if.slave port_if [NUM_PORTS],
    
    // QoS configuration for each port
    input  qos_config_t port_qos_config_i [NUM_PORTS],
    
    // Unified memory interface (to actual memory controller)
    memory_req_rsp_if.master mem_if,
    
    // QoS control interface
    input  logic                        qos_enable_i,
    input  qos_arbiter_policy_e         arbiter_policy_i,
    input  logic [7:0]                  bandwidth_limits_i [NUM_PORTS], // Percentage
    
    // QoS monitoring outputs
    output logic [31:0]                 qos_violations_o,
    output logic [31:0]                 port_requests_o [NUM_PORTS],
    output logic [31:0]                 port_bandwidth_used_o [NUM_PORTS],
    output logic [31:0]                 avg_latency_o [NUM_PORTS],
    
    // Emergency override
    input  logic                        emergency_mode_i,
    input  logic [NUM_PORTS-1:0]        emergency_port_mask_i
);

    //---------------------------------------------------------------------------
    // QoS Request Queue Structure
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic                    valid;
        memory_req_t             req;
        qos_config_t             qos_config;
        logic [$clog2(NUM_PORTS)-1:0] src_port;
        logic [31:0]             timestamp;
        logic [31:0]             deadline;
        logic [15:0]             transaction_id;
    } qos_mem_request_t;

    //---------------------------------------------------------------------------
    // Priority Queue Management
    //---------------------------------------------------------------------------
    // Separate queues for different QoS levels
    qos_mem_request_t priority_queues [16][QOS_QUEUE_DEPTH-1:0]; // 16 QoS levels
    logic [$clog2(QOS_QUEUE_DEPTH)-1:0] queue_head [16];
    logic [$clog2(QOS_QUEUE_DEPTH)-1:0] queue_tail [16];
    logic [QOS_QUEUE_DEPTH-1:0] queue_valid [16];
    logic [15:0] queue_not_empty;

    //---------------------------------------------------------------------------
    // Bandwidth Management
    //---------------------------------------------------------------------------
    logic [31:0] bandwidth_counters [NUM_PORTS];
    logic [31:0] bandwidth_windows [NUM_PORTS];
    logic [31:0] global_cycle_counter;
    logic [NUM_PORTS-1:0] bandwidth_exceeded;
    
    localparam integer BANDWIDTH_WINDOW = 1000; // Cycles for bandwidth measurement

    //---------------------------------------------------------------------------
    // QoS Arbitration Logic
    //---------------------------------------------------------------------------
    logic [3:0] selected_qos_level;
    logic [$clog2(QOS_QUEUE_DEPTH)-1:0] selected_queue_idx;
    logic selected_valid;
    qos_mem_request_t selected_request;

    always_comb begin : proc_qos_arbitration
        selected_valid = 1'b0;
        selected_qos_level = 4'h0;
        selected_queue_idx = 0;
        selected_request = '0;

        case (arbiter_policy_i)
            QOS_ARBITER_STRICT_PRIO: begin
                // Strict priority - highest QoS level first
                for (int qos_lvl = 15; qos_lvl >= 0; qos_lvl--) begin
                    if (queue_not_empty[qos_lvl] && !selected_valid) begin
                        selected_qos_level = qos_lvl[3:0];
                        selected_queue_idx = queue_head[qos_lvl];
                        selected_request = priority_queues[qos_lvl][queue_head[qos_lvl]];
                        selected_valid = 1'b1;
                    end
                end
            end
            
            QOS_ARBITER_WEIGHTED_RR: begin
                // Weighted round-robin with QoS consideration
                logic [31:0] best_score = 0;
                
                for (int qos_lvl = 0; qos_lvl < 16; qos_lvl++) begin
                    if (queue_not_empty[qos_lvl]) begin
                        qos_mem_request_t req = priority_queues[qos_lvl][queue_head[qos_lvl]];
                        logic [31:0] score = calculate_priority_score(
                            req.qos_config.qos_level,
                            global_cycle_counter - req.timestamp,
                            req.qos_config.weight,
                            req.qos_config.urgent
                        );
                        
                        if (score > best_score || !selected_valid) begin
                            best_score = score;
                            selected_qos_level = qos_lvl[3:0];
                            selected_queue_idx = queue_head[qos_lvl];
                            selected_request = req;
                            selected_valid = 1'b1;
                        end
                    end
                end
            end
            
            QOS_ARBITER_FAIR_QUEUING: begin
                // Fair queuing with aging
                logic [31:0] oldest_timestamp = 32'hFFFFFFFF;
                
                for (int qos_lvl = 0; qos_lvl < 16; qos_lvl++) begin
                    if (queue_not_empty[qos_lvl]) begin
                        qos_mem_request_t req = priority_queues[qos_lvl][queue_head[qos_lvl]];
                        
                        if (req.timestamp < oldest_timestamp || !selected_valid) begin
                            oldest_timestamp = req.timestamp;
                            selected_qos_level = qos_lvl[3:0];
                            selected_queue_idx = queue_head[qos_lvl];
                            selected_request = req;
                            selected_valid = 1'b1;
                        end
                    end
                end
            end
            
            default: begin
                // Round-robin fallback
                for (int qos_lvl = 0; qos_lvl < 16; qos_lvl++) begin
                    if (queue_not_empty[qos_lvl] && !selected_valid) begin
                        selected_qos_level = qos_lvl[3:0];
                        selected_queue_idx = queue_head[qos_lvl];
                        selected_request = priority_queues[qos_lvl][queue_head[qos_lvl]];
                        selected_valid = 1'b1;
                    end
                end
            end
        endcase
        
        // Emergency mode override
        if (emergency_mode_i && selected_valid) begin
            logic emergency_port = emergency_port_mask_i[selected_request.src_port];
            if (!emergency_port) begin
                selected_valid = 1'b0; // Block non-emergency ports
            end
        end
    end

    //---------------------------------------------------------------------------
    // Request Enqueueing Logic
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_request_enqueue
        if (!rst_ni) begin
            for (int qos_lvl = 0; qos_lvl < 16; qos_lvl++) begin
                queue_head[qos_lvl] <= 0;
                queue_tail[qos_lvl] <= 0;
                queue_valid[qos_lvl] <= '0;
                queue_not_empty[qos_lvl] <= 1'b0;
            end
            global_cycle_counter <= 0;
        end else begin
            global_cycle_counter <= global_cycle_counter + 1;
            
            // Update queue empty flags
            for (int qos_lvl = 0; qos_lvl < 16; qos_lvl++) begin
                queue_not_empty[qos_lvl] <= |queue_valid[qos_lvl];
            end
            
            // Enqueue new requests from input ports
            for (int port = 0; port < NUM_PORTS; port++) begin
                if (port_if[port].req_valid && port_if[port].req_ready) begin
                    logic [3:0] req_qos_level = port_qos_config_i[port].qos_level;
                    logic [$clog2(QOS_QUEUE_DEPTH)-1:0] tail_idx = queue_tail[req_qos_level];
                    
                    // Check if queue has space
                    if (!queue_valid[req_qos_level][tail_idx]) begin
                        // Enqueue the request
                        priority_queues[req_qos_level][tail_idx] <= '{
                            valid: 1'b1,
                            req: port_if[port].req,
                            qos_config: port_qos_config_i[port],
                            src_port: port,
                            timestamp: global_cycle_counter,
                            deadline: global_cycle_counter + port_qos_config_i[port].max_latency_cycles,
                            transaction_id: port * 1000 + tail_idx // Simple ID generation
                        };
                        
                        queue_valid[req_qos_level][tail_idx] <= 1'b1;
                        queue_tail[req_qos_level] <= (tail_idx + 1) % QOS_QUEUE_DEPTH;
                    end
                end
            end
            
            // Dequeue selected request
            if (selected_valid && mem_if.req_ready) begin
                queue_valid[selected_qos_level][selected_queue_idx] <= 1'b0;
                queue_head[selected_qos_level] <= (selected_queue_idx + 1) % QOS_QUEUE_DEPTH;
            end
        end
    end

    //---------------------------------------------------------------------------
    // Bandwidth Management and Monitoring
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_bandwidth_mgmt
        if (!rst_ni) begin
            for (int port = 0; port < NUM_PORTS; port++) begin
                bandwidth_counters[port] <= 0;
                bandwidth_windows[port] <= 0;
                port_requests_o[port] <= 0;
                port_bandwidth_used_o[port] <= 0;
                avg_latency_o[port] <= 0;
            end
            qos_violations_o <= 0;
        end else begin
            // Update bandwidth windows
            for (int port = 0; port < NUM_PORTS; port++) begin
                bandwidth_windows[port] <= bandwidth_windows[port] + 1;
                
                // Reset bandwidth counters every window
                if (bandwidth_windows[port] >= BANDWIDTH_WINDOW) begin
                    bandwidth_windows[port] <= 0;
                    port_bandwidth_used_o[port] <= bandwidth_counters[port];
                    bandwidth_counters[port] <= 0;
                end
                
                // Count bandwidth usage
                if (selected_valid && selected_request.src_port == port && mem_if.req_ready) begin
                    bandwidth_counters[port] <= bandwidth_counters[port] + 1;
                    port_requests_o[port] <= port_requests_o[port] + 1;
                end
                
                // Check bandwidth limits
                logic [31:0] port_limit = (BANDWIDTH_WINDOW * bandwidth_limits_i[port]) / 100;
                bandwidth_exceeded[port] <= (bandwidth_counters[port] > port_limit);
            end
            
            // Monitor QoS violations (deadline misses)
            if (selected_valid && (global_cycle_counter > selected_request.deadline)) begin
                qos_violations_o <= qos_violations_o + 1;
            end
        end
    end

    //---------------------------------------------------------------------------
    // Input Port Ready Logic
    //---------------------------------------------------------------------------
    always_comb begin : proc_port_ready
        for (int port = 0; port < NUM_PORTS; port++) begin
            logic [3:0] req_qos_level = port_qos_config_i[port].qos_level;
            logic [$clog2(QOS_QUEUE_DEPTH)-1:0] tail_idx = queue_tail[req_qos_level];
            
            // Port ready if:
            // 1. QoS enabled and queue has space, OR
            // 2. QoS disabled and memory ready, AND
            // 3. Bandwidth not exceeded (unless emergency mode)
            port_if[port].req_ready = (qos_enable_i ? !queue_valid[req_qos_level][tail_idx] : mem_if.req_ready) &&
                                      (!bandwidth_exceeded[port] || emergency_mode_i);
        end
    end

    //---------------------------------------------------------------------------
    // Memory Interface Output
    //---------------------------------------------------------------------------
    assign mem_if.req_valid = qos_enable_i ? selected_valid : |{port_if[0].req_valid, port_if[1].req_valid, port_if[2].req_valid, port_if[3].req_valid};
    assign mem_if.req = qos_enable_i ? selected_request.req : port_if[0].req; // Simplified for non-QoS mode

    //---------------------------------------------------------------------------
    // Response Routing with Transaction Tracking
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic                            valid;
        logic [$clog2(NUM_PORTS)-1:0]   src_port;
        logic [15:0]                     transaction_id;
        logic [31:0]                     request_timestamp;
    } outstanding_txn_t;
    
    outstanding_txn_t outstanding_transactions [OUTSTANDING_REQS-1:0];
    logic [$clog2(OUTSTANDING_REQS)-1:0] txn_alloc_ptr, txn_complete_ptr;
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_response_routing
        if (!rst_ni) begin
            for (int i = 0; i < OUTSTANDING_REQS; i++) begin
                outstanding_transactions[i] <= '0;
            end
            txn_alloc_ptr <= 0;
            txn_complete_ptr <= 0;
            
            for (int port = 0; port < NUM_PORTS; port++) begin
                port_if[port].rsp_valid <= 1'b0;
                port_if[port].rsp <= '0;
            end
        end else begin
            // Allocate transaction tracking entry for new requests
            if (selected_valid && mem_if.req_ready && !outstanding_transactions[txn_alloc_ptr].valid) begin
                outstanding_transactions[txn_alloc_ptr] <= '{
                    valid: 1'b1,
                    src_port: selected_request.src_port,
                    transaction_id: selected_request.transaction_id,
                    request_timestamp: selected_request.timestamp
                };
                txn_alloc_ptr <= (txn_alloc_ptr + 1) % OUTSTANDING_REQS;
            end
            
            // Route responses back to originating port
            if (mem_if.rsp_valid) begin
                // Find matching outstanding transaction (simplified - using FIFO order)
                if (outstanding_transactions[txn_complete_ptr].valid) begin
                    logic [$clog2(NUM_PORTS)-1:0] rsp_port = outstanding_transactions[txn_complete_ptr].src_port;
                    
                    port_if[rsp_port].rsp_valid <= 1'b1;
                    port_if[rsp_port].rsp <= mem_if.rsp;
                    
                    // Clear completed transaction
                    outstanding_transactions[txn_complete_ptr].valid <= 1'b0;
                    txn_complete_ptr <= (txn_complete_ptr + 1) % OUTSTANDING_REQS;
                end
            end else begin
                // Clear all response valid signals
                for (int port = 0; port < NUM_PORTS; port++) begin
                    port_if[port].rsp_valid <= 1'b0;
                end
            end
        end
    end

    //---------------------------------------------------------------------------
    // QoS Performance Monitoring
    //---------------------------------------------------------------------------
    logic [31:0] latency_accumulators [NUM_PORTS];
    logic [31:0] latency_counts [NUM_PORTS];
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_latency_monitoring
        if (!rst_ni) begin
            for (int port = 0; port < NUM_PORTS; port++) begin
                latency_accumulators[port] <= 0;
                latency_counts[port] <= 0;
            end
        end else begin
            // Calculate average latency per port
            if (mem_if.rsp_valid && outstanding_transactions[txn_complete_ptr].valid) begin
                logic [$clog2(NUM_PORTS)-1:0] rsp_port = outstanding_transactions[txn_complete_ptr].src_port;
                logic [31:0] latency = global_cycle_counter - outstanding_transactions[txn_complete_ptr].request_timestamp;
                
                latency_accumulators[rsp_port] <= latency_accumulators[rsp_port] + latency;
                latency_counts[rsp_port] <= latency_counts[rsp_port] + 1;
                
                // Update average latency
                if (latency_counts[rsp_port] > 0) begin
                    avg_latency_o[rsp_port] <= latency_accumulators[rsp_port] / latency_counts[rsp_port];
                end
            end
        end
    end

endmodule : qos_memory_wrapper

`default_nettype wire
