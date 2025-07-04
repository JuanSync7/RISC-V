//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: fence_unit.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: fence_unit
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-29
// DESCRIPTION: FENCE instruction implementation for memory ordering and I-cache sync.
// PRIMARY_PURPOSE: Implement FENCE and FENCE.I instructions per RISC-V spec.
// ROLE_IN_SYSTEM: Ensures memory ordering and instruction stream synchronization.
// PROBLEM_SOLVED: Provides memory barriers and cache coherency for RV32I compliance.
// MODULE_TYPE: RTL
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V ISA Specification v2.2
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

module fence_unit
import riscv_base_pkg::*;
import riscv_system_config_pkg::*;
#(
    parameter integer CONFIG_NUM_CORES = DEFAULT_CORE_CONFIG.num_cores
) (
    // Clock and Reset
    input  logic        clk_i,              // AI_TAG: PORT_DESC - System clock
    input  logic        rst_ni,             // AI_TAG: PORT_DESC - Active-low asynchronous reset
    
    // Control Interface
    input  logic        fence_req_i,        // AI_TAG: PORT_DESC - FENCE instruction request
    input  logic        fence_i_req_i,      // AI_TAG: PORT_DESC - FENCE.I instruction request
    input  logic [3:0]  fence_pred_i,       // AI_TAG: PORT_DESC - Predecessor operations
    input  logic [3:0]  fence_succ_i,       // AI_TAG: PORT_DESC - Successor operations
    output logic        fence_done_o,       // AI_TAG: PORT_DESC - FENCE operation complete
    
    // Memory System Interface
    output logic        mem_barrier_o,      // AI_TAG: PORT_DESC - Memory barrier request
    input  logic        mem_barrier_ack_i,  // AI_TAG: PORT_DESC - Memory barrier acknowledge
    
    // Cache Control Interface
    output logic        icache_flush_o,     // AI_TAG: PORT_DESC - I-cache flush request
    input  logic        icache_flush_ack_i, // AI_TAG: PORT_DESC - I-cache flush acknowledge
    output logic        dcache_flush_o,     // AI_TAG: PORT_DESC - D-cache flush request (optional)
    input  logic        dcache_flush_ack_i, // AI_TAG: PORT_DESC - D-cache flush acknowledge
    
    // Multi-core Synchronization (if applicable)
    output logic        global_sync_req_o,  // AI_TAG: PORT_DESC - Global synchronization request
    input  logic        global_sync_ack_i   // AI_TAG: PORT_DESC - Global synchronization acknowledge
);

    //-------------------------------------------------------------------------
    // FENCE Instruction Format
    //-------------------------------------------------------------------------
    // AI_TAG: FEATURE - Implements FENCE and FENCE.I instructions per RISC-V spec
    
    // FENCE predecessor and successor bits
    // Bit 3: Device input (I)
    // Bit 2: Device output (O)  
    // Bit 1: Memory reads (R)
    // Bit 0: Memory writes (W)
    typedef struct packed {
        logic dev_input;    // I
        logic dev_output;   // O
        logic mem_read;     // R
        logic mem_write;    // W
    } fence_bits_t;
    
    //-------------------------------------------------------------------------
    // FSM States
    //-------------------------------------------------------------------------
    // AI_TAG: FSM_NAME - fence_fsm
    // AI_TAG: FSM_PURPOSE - fence_fsm - Controls FENCE operation sequencing
    // AI_TAG: FSM_ENCODING - fence_fsm - one-hot
    // AI_TAG: FSM_RESET_STATE - fence_fsm - S_IDLE
    typedef enum logic [3:0] {
        S_IDLE,
        S_DRAIN_STORES,      // Wait for pending stores to complete
        S_MEMORY_BARRIER,    // Issue memory barrier
        S_FLUSH_ICACHE,      // Flush instruction cache
        S_FLUSH_DCACHE,      // Flush data cache (if needed)
        S_GLOBAL_SYNC,       // Multi-core synchronization
        S_COMPLETE           // Operation complete
    } fence_state_e;
    
    fence_state_e state_r, state_ns;
    
    // Decode fence bits
    fence_bits_t pred_bits, succ_bits;
    assign pred_bits = fence_bits_t'(fence_pred_i);
    assign succ_bits = fence_bits_t'(fence_succ_i);
    
    //-------------------------------------------------------------------------
    // Fence Operation Control
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Determine what operations are needed
    logic needs_mem_barrier;
    logic needs_icache_flush;
    logic needs_dcache_flush;
    logic needs_global_sync;
    
    always_comb begin
        // Default: no operations needed
        needs_mem_barrier = 1'b0;
        needs_icache_flush = 1'b0;
        needs_dcache_flush = 1'b0;
        needs_global_sync = 1'b0;
        
        if (fence_i_req_i) begin
            // FENCE.I always flushes instruction cache
            needs_icache_flush = 1'b1;
            // In multi-core systems, need global synchronization
            if (CONFIG_NUM_CORES > 1) begin
                needs_global_sync = 1'b1;
            end
        end else if (fence_req_i) begin
            // Regular FENCE instruction
            // Memory barrier needed if any memory operations are ordered
            needs_mem_barrier = (pred_bits.mem_read || pred_bits.mem_write) &&
                               (succ_bits.mem_read || succ_bits.mem_write);
            
            // Device I/O ordering
            if ((pred_bits.dev_input || pred_bits.dev_output) ||
                (succ_bits.dev_input || succ_bits.dev_output)) begin
                needs_mem_barrier = 1'b1;
                // Device operations may need cache flushes
                needs_dcache_flush = pred_bits.dev_output || succ_bits.dev_input;
            end
            
            // Multi-core synchronization for strong memory ordering
            if (CONFIG_NUM_CORES > 1 && needs_mem_barrier) begin
                needs_global_sync = 1'b1;
            end
        end
    end
    
    //-------------------------------------------------------------------------
    // FSM Next State Logic
    //-------------------------------------------------------------------------
    // AI_TAG: FSM_TRANSITION - fence_fsm: S_IDLE -> S_DRAIN_STORES when (fence_req_i || fence_i_req_i)
    // AI_TAG: FSM_TRANSITION - fence_fsm: S_DRAIN_STORES -> S_MEMORY_BARRIER when (needs_mem_barrier)
    // AI_TAG: FSM_TRANSITION - fence_fsm: S_MEMORY_BARRIER -> S_FLUSH_ICACHE when (mem_barrier_ack_i && needs_icache_flush)
    always_comb begin
        state_ns = state_r;
        
        case (state_r)
            S_IDLE: begin
                if (fence_req_i || fence_i_req_i) begin
                    state_ns = S_DRAIN_STORES;
                end
            end
            
            S_DRAIN_STORES: begin
                // In a real implementation, would wait for store buffer to drain
                // For now, proceed immediately
                if (needs_mem_barrier) begin
                    state_ns = S_MEMORY_BARRIER;
                end else if (needs_icache_flush) begin
                    state_ns = S_FLUSH_ICACHE;
                end else if (needs_dcache_flush) begin
                    state_ns = S_FLUSH_DCACHE;
                end else if (needs_global_sync) begin
                    state_ns = S_GLOBAL_SYNC;
                end else begin
                    state_ns = S_COMPLETE;
                end
            end
            
            S_MEMORY_BARRIER: begin
                if (mem_barrier_ack_i) begin
                    if (needs_icache_flush) begin
                        state_ns = S_FLUSH_ICACHE;
                    end else if (needs_dcache_flush) begin
                        state_ns = S_FLUSH_DCACHE;
                    end else if (needs_global_sync) begin
                        state_ns = S_GLOBAL_SYNC;
                    end else begin
                        state_ns = S_COMPLETE;
                    end
                end
            end
            
            S_FLUSH_ICACHE: begin
                if (icache_flush_ack_i) begin
                    if (needs_dcache_flush) begin
                        state_ns = S_FLUSH_DCACHE;
                    end else if (needs_global_sync) begin
                        state_ns = S_GLOBAL_SYNC;
                    end else begin
                        state_ns = S_COMPLETE;
                    end
                end
            end
            
            S_FLUSH_DCACHE: begin
                if (dcache_flush_ack_i) begin
                    if (needs_global_sync) begin
                        state_ns = S_GLOBAL_SYNC;
                    end else begin
                        state_ns = S_COMPLETE;
                    end
                end
            end
            
            S_GLOBAL_SYNC: begin
                if (global_sync_ack_i) begin
                    state_ns = S_COMPLETE;
                end
            end
            
            S_COMPLETE: begin
                state_ns = S_IDLE;
            end
            
            default: state_ns = S_IDLE;
        endcase
    end
    
    //-------------------------------------------------------------------------
    // State Register
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state_r <= S_IDLE;
        end else begin
            state_r <= state_ns;
        end
    end
    
    //-------------------------------------------------------------------------
    // Output Generation
    //-------------------------------------------------------------------------
    // AI_TAG: FSM_OUTPUT_ACTIONS - fence_fsm - S_MEMORY_BARRIER - Assert mem_barrier_o
    // AI_TAG: FSM_OUTPUT_ACTIONS - fence_fsm - S_FLUSH_ICACHE - Assert icache_flush_o
    // AI_TAG: FSM_OUTPUT_ACTIONS - fence_fsm - S_FLUSH_DCACHE - Assert dcache_flush_o
    // AI_TAG: FSM_OUTPUT_ACTIONS - fence_fsm - S_GLOBAL_SYNC - Assert global_sync_req_o
    // AI_TAG: FSM_OUTPUT_ACTIONS - fence_fsm - S_COMPLETE - Assert fence_done_o
    
    assign mem_barrier_o = (state_r == S_MEMORY_BARRIER);
    assign icache_flush_o = (state_r == S_FLUSH_ICACHE);
    assign dcache_flush_o = (state_r == S_FLUSH_DCACHE);
    assign global_sync_req_o = (state_r == S_GLOBAL_SYNC);
    assign fence_done_o = (state_r == S_COMPLETE);
    
    //-------------------------------------------------------------------------
    // Assertions
    //-------------------------------------------------------------------------
    // AI_TAG: ASSERTION - Only one fence type at a time
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    OneFenceType: assert property (@(posedge clk_i) disable iff (!rst_ni)
        !(fence_req_i && fence_i_req_i));
    
    // AI_TAG: ASSERTION - State machine returns to idle
    // AI_TAG: ASSERTION_TYPE - Formal
    // AI_TAG: ASSERTION_SEVERITY - Error
    EventuallyIdle: assert property (@(posedge clk_i) disable iff (!rst_ni)
        (state_r != S_IDLE) |-> ##[1:100] (state_r == S_IDLE));
    
    // AI_TAG: ASSERTION - Memory barrier must be acknowledged
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    MemBarrierAck: assert property (@(posedge clk_i) disable iff (!rst_ni)
        mem_barrier_o |-> ##[1:10] mem_barrier_ack_i);

endmodule : fence_unit

//=============================================================================
// Dependencies: riscv_base_pkg, riscv_system_config_pkg
//
// Instantiated In:
//   - core/execute_stage.sv
//   - core/pipeline/execute_stage.sv
//
// Performance:
//   - Critical Path: FSM state transitions
//   - Max Frequency: Limited by cache flush latency
//   - Area: Minimal - FSM and control logic only
//
// Verification Coverage:
//   - Code Coverage: TBD
//   - Functional Coverage: TBD
//   - Branch Coverage: TBD
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Vivado
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: fence_unit_tb.sv
//   - Test Vectors: TBD
//
//----
// Revision History:
// Version | Date       | Author         | Description
//=============================================================================
// 1.0.0   | 2025-01-29 | DesignAI      | Initial release
//=============================================================================