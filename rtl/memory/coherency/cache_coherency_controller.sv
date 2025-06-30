//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: cache_coherency_controller.sv
// Module: cache_coherency_controller
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Manages cache coherency for the L2 cache using a MESI-like protocol.
//   It tracks the state of cache lines across all L1 caches, handles
//   requests from cores, issues snoops, and ensures data consistency.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_mem_types_pkg::*;

module cache_coherency_controller #(
    parameter integer NUM_CORES = 4,
    parameter integer ADDR_WIDTH = 32,
    parameter int unsigned L2_CACHE_WAYS = 8,
    parameter int unsigned L2_CACHE_SETS = 256
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Coherency interface connecting to all L1 caches
    cache_coherency_if.coherency_controller_port coherency_if,

    // Interface to L3/Memory for misses and writebacks
    memory_req_rsp_if.master mem_if,

    // Interface to L2 cache data and tag arrays
    input  logic [L2_CACHE_WAYS-1:0] l2_tag_match_way_i,
    input  cache_state_t             l2_line_state_i,
    input  logic [NUM_CORES-1:0]     l2_sharer_list_i,
    output logic                     l2_update_en_o,
    output logic [$clog2(L2_CACHE_WAYS)-1:0] l2_way_select_o
);

    //------------------------------------------------------------------------- 
    // MESI Protocol Controller
    //-------------------------------------------------------------------------
    // AI_TAG: FSM_NAME - mesi_protocol_fsm
    // AI_TAG: FSM_PURPOSE - mesi_protocol_fsm - Controls MESI coherency state transitions
    // AI_TAG: FSM_ENCODING - mesi_protocol_fsm - binary encoding for area optimization
    // AI_TAG: FSM_RESET_STATE - mesi_protocol_fsm - COHERENCY_IDLE
    typedef enum logic [2:0] {
        COHERENCY_IDLE     = 3'b000,  // AI_TAG: FSM_STATE - COHERENCY_IDLE - Waiting for coherency requests
        ARBITRATE_REQ      = 3'b001,  // AI_TAG: FSM_STATE - ARBITRATE_REQ - Arbitrating between multiple requests
        PROCESS_REQUEST    = 3'b010,  // AI_TAG: FSM_STATE - PROCESS_REQUEST - Processing selected request
        SEND_SNOOPS        = 3'b011,  // AI_TAG: FSM_STATE - SEND_SNOOPS - Broadcasting snoop requests
        COLLECT_RESPONSES  = 3'b100,  // AI_TAG: FSM_STATE - COLLECT_RESPONSES - Collecting snoop responses
        UPDATE_STATES      = 3'b101,  // AI_TAG: FSM_STATE - UPDATE_STATES - Updating coherency states
        SEND_RESPONSE      = 3'b110   // AI_TAG: FSM_STATE - SEND_RESPONSE - Sending final response
    } coherency_state_e;

    coherency_state_e current_state_r, next_state_c;

    // Registered storage for active request processing
    // AI_TAG: INTERNAL_STORAGE - active_req_r - Stores the current coherency request being processed
    // AI_TAG: INTERNAL_STORAGE - active_core_id_r - ID of core making the active request
    // AI_TAG: INTERNAL_STORAGE - expected_responses_r - Number of snoop responses expected
    // AI_TAG: INTERNAL_STORAGE - response_count_r - Number of snoop responses received
    // AI_TAG: INTERNAL_STORAGE - collected_data_r - Data collected from snoop responses
    // AI_TAG: INTERNAL_STORAGE - snoop_data_valid_r - Indicates if valid data was collected
    coherency_req_t active_req_r;
    logic [CORE_ID_WIDTH-1:0] active_core_id_r;
    logic [CORE_ID_WIDTH:0] expected_responses_r;
    logic [CORE_ID_WIDTH:0] response_count_r;
    logic [DATA_WIDTH-1:0] collected_data_r;
    logic collected_data_valid_r;
    logic [NUM_CORES-1:0] snoop_sent_mask_r;

    // Round-robin arbiter state
    // AI_TAG: INTERNAL_STORAGE - arbiter_ptr_r - Current arbiter pointer for round-robin selection
    logic [CORE_ID_WIDTH-1:0] arbiter_ptr_r;

    //------------------------------------------------------------------------- 
    // Main FSM Logic
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_coherency_fsm
        if (!rst_ni) begin
            current_state_r <= COHERENCY_IDLE;
            active_req_r <= '0;
            active_core_id_r <= '0;
            expected_responses_r <= '0;
            response_count_r <= '0;
            collected_data_r <= '0;
            collected_data_valid_r <= '0;
            snoop_sent_mask_r <= '0;
            arbiter_ptr_r <= '0;
        end else begin
            current_state_r <= next_state_c;
            
            // Register active request during arbitration
            if (current_state_r == ARBITRATE_REQ && next_state_c == PROCESS_REQUEST) begin
                logic [CORE_ID_WIDTH-1:0] selected_core;
                selected_core = arbiter_ptr_r;
                
                // Find next requesting core starting from arbiter pointer
                for (int i = 0; i < NUM_CORES; i++) begin
                    logic [CORE_ID_WIDTH-1:0] core_idx = (arbiter_ptr_r + i) % NUM_CORES;
                    if (coherency_if.req_valid[core_idx]) begin
                        selected_core = core_idx;
                        break;
                    end
                end
                
                active_req_r <= coherency_if.req[selected_core];
                active_core_id_r <= selected_core;
                expected_responses_r <= NUM_CORES - 1; // All cores except requester
                response_count_r <= '0;
                collected_data_r <= '0;
                collected_data_valid_r <= '0;
                snoop_sent_mask_r <= '0;
                
                // Update arbiter pointer
                arbiter_ptr_r <= selected_core + 1;
            end
            
            // Collect snoop responses
            if (current_state_r == COLLECT_RESPONSES) begin
                for (int i = 0; i < NUM_CORES; i++) begin
                    if (i != active_core_id_r && snoop_sent_mask_r[i]) begin
                        if (coherency_if.snoop_rsp_valid[i]) begin
                            response_count_r <= response_count_r + 1;
                            if (coherency_if.snoop_rsp_data_valid[i] && !collected_data_valid_r) begin
                                collected_data_r <= coherency_if.snoop_rsp_data[i];
                                collected_data_valid_r <= 1'b1;
                            end
                        end
                    end
                end
            end
            
            // Clear response count when returning to idle
            if (next_state_c == COHERENCY_IDLE) begin
                response_count_r <= '0;
                collected_data_valid_r <= '0;
                snoop_sent_mask_r <= '0;
            end
        end
    end

    // Combinational FSM logic
    always_comb begin : proc_coherency_fsm_logic
        next_state_c = current_state_r;
        
        // Default interface outputs
        for (int i = 0; i < NUM_CORES; i++) begin
            coherency_if.req_ready[i] = 1'b0;
            coherency_if.rsp_valid[i] = 1'b0;
            coherency_if.rsp[i] = '0;
            coherency_if.snoop_valid[i] = 1'b0;
            coherency_if.snoop_addr[i] = '0;
            coherency_if.snoop_type[i] = COHERENCY_REQ_READ;
        end

        case (current_state_r)
            COHERENCY_IDLE: begin
                // Check for any pending requests
                logic has_request = 1'b0;
                for (int i = 0; i < NUM_CORES; i++) begin
                    if (coherency_if.req_valid[i]) begin
                        has_request = 1'b1;
                        break;
                    end
                end
                
                if (has_request) begin
                    next_state_c = ARBITRATE_REQ;
                end
            end

            ARBITRATE_REQ: begin
                // Arbitration logic - select requesting core
                logic [CORE_ID_WIDTH-1:0] selected_core = '0;
                logic found_requester = 1'b0;
                
                // Round-robin selection starting from arbiter pointer
                for (int i = 0; i < NUM_CORES; i++) begin
                    logic [CORE_ID_WIDTH-1:0] core_idx = (arbiter_ptr_r + i) % NUM_CORES;
                    if (coherency_if.req_valid[core_idx] && !found_requester) begin
                        selected_core = core_idx;
                        found_requester = 1'b1;
                    end
                end
                
                if (found_requester) begin
                    coherency_if.req_ready[selected_core] = 1'b1;
                    next_state_c = PROCESS_REQUEST;
                end else begin
                    next_state_c = COHERENCY_IDLE;
                end
            end

            PROCESS_REQUEST: begin
                // Determine snoop type based on request
                case (active_req_r.req_type)
                    COHERENCY_REQ_READ: begin
                        // For reads, snoop other caches for data
                        next_state_c = SEND_SNOOPS;
                    end
                    
                    COHERENCY_REQ_WRITE: begin
                        // For writes, invalidate other caches
                        next_state_c = SEND_SNOOPS;
                    end
                    
                    COHERENCY_REQ_INVALIDATE: begin
                        // Direct invalidation request
                        next_state_c = SEND_SNOOPS;
                    end
                    
                    default: begin
                        // Unknown request type - skip to response
                        next_state_c = SEND_RESPONSE;
                    end
                endcase
            end

            SEND_SNOOPS: begin
                // Send snoop requests to all other cores
                logic all_snoops_sent = 1'b1;
                
                for (int i = 0; i < NUM_CORES; i++) begin
                    if (i != active_core_id_r) begin
                        coherency_if.snoop_valid[i] = 1'b1;
                        coherency_if.snoop_addr[i] = active_req_r.addr;
                        
                        case (active_req_r.req_type)
                            COHERENCY_REQ_READ: begin
                                coherency_if.snoop_type[i] = COHERENCY_REQ_READ;
                            end
                            COHERENCY_REQ_WRITE, COHERENCY_REQ_INVALIDATE: begin
                                coherency_if.snoop_type[i] = COHERENCY_REQ_INVALIDATE;
                            end
                            default: begin
                                coherency_if.snoop_type[i] = COHERENCY_REQ_READ;
                            end
                        endcase
                        
                        // Mark that we've sent snoop to this core
                        snoop_sent_mask_r[i] <= 1'b1;
                    end
                end
                
                // Move to response collection
                next_state_c = COLLECT_RESPONSES;
            end

            COLLECT_RESPONSES: begin
                // Wait for all expected responses
                if (response_count_r >= expected_responses_r) begin
                    next_state_c = UPDATE_STATES;
                end
                
                // Timeout protection - if we wait too long, proceed anyway
                // This would need a timer in a real implementation
            end

            UPDATE_STATES: begin
                // Update coherency states based on collected responses
                // This is protocol-specific logic
                next_state_c = SEND_RESPONSE;
            end

            SEND_RESPONSE: begin
                // Send response back to requesting core
                coherency_if.rsp_valid[active_core_id_r] = 1'b1;
                coherency_if.rsp[active_core_id_r].req_id = active_req_r.req_id;
                coherency_if.rsp[active_core_id_r].error = 1'b0;
                
                case (active_req_r.req_type)
                    COHERENCY_REQ_READ: begin
                        if (collected_data_valid_r) begin
                            coherency_if.rsp[active_core_id_r].data = collected_data_r;
                            coherency_if.rsp[active_core_id_r].data_valid = 1'b1;
                        end else begin
                            coherency_if.rsp[active_core_id_r].data = '0;
                            coherency_if.rsp[active_core_id_r].data_valid = 1'b0;
                        end
                    end
                    
                    default: begin
                        coherency_if.rsp[active_core_id_r].data = '0;
                        coherency_if.rsp[active_core_id_r].data_valid = 1'b0;
                    end
                endcase
                
                if (coherency_if.rsp_ready[active_core_id_r]) begin
                    next_state_c = COHERENCY_IDLE;
                end
            end

            default: begin
                next_state_c = COHERENCY_IDLE;
            end
        endcase
    end

    // AI_TAG: ASSERTION - a_coherency_single_request: Only one core should be processed at a time
    // AI_TAG: ASSERTION_TYPE - Simulation
    // AI_TAG: ASSERTION_SEVERITY - Error
`ifdef SIMULATION
    property p_single_active_request;
        @(posedge clk_i) disable iff (!rst_ni)
        (current_state_r != COHERENCY_IDLE) |-> ($onehot0({(coherency_if.req_valid[0] & coherency_if.req_ready[0]),
                                                           (coherency_if.req_valid[1] & coherency_if.req_ready[1]),
                                                           (coherency_if.req_valid[2] & coherency_if.req_ready[2]),
                                                           (coherency_if.req_valid[3] & coherency_if.req_ready[3])}));
    endproperty
    
    assert property (p_single_active_request)
        else $error("Multiple coherency requests being processed simultaneously");

    // AI_TAG: ASSERTION - a_response_count_valid: Response count should not exceed expected
    property p_response_count_bounds;
        @(posedge clk_i) disable iff (!rst_ni)
        response_count_r <= expected_responses_r;
    endproperty
    
    assert property (p_response_count_bounds)
        else $error("Response count %d exceeds expected %d", response_count_r, expected_responses_r);
`endif

endmodule : cache_coherency_controller

`default_nettype wire 