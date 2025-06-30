//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: qos_exception_handler.sv
// Module: qos_exception_handler
//
// Project Name: RISC-V RV32IM QoS-Enhanced Exception Handler
// Target Devices: ASIC/FPGA
//
// Description:
//   QoS-enhanced exception handler that assigns critical QoS levels to
//   exception memory accesses, debug operations, and interrupt handling.
//   Ensures system-critical operations receive highest memory priority.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module qos_exception_handler (
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Exception Inputs from Pipeline Stages ---
    input  exception_info_t fetch_exception_i,
    input  exception_info_t execute_exception_i,
    input  exception_info_t memory_exception_i,
    input  exception_info_t writeback_exception_i,

    // --- Interrupt Inputs ---
    input  logic        m_software_interrupt_i,
    input  logic        m_timer_interrupt_i,
    input  logic        m_external_interrupt_i,

    // --- CSR State Inputs ---
    input  logic        mstatus_mie_i,
    input  logic        mie_msie_i,
    input  logic        mie_mtie_i,
    input  logic        mie_meie_i,
    input  logic        mip_msip_i,
    input  logic        mip_mtip_i,
    input  logic        mip_meip_i,
    input  addr_t       mtvec_base_i,
    input  logic [1:0]  mtvec_mode_i,

    // --- Exception Outputs ---
    output logic        exception_valid_o,
    output exception_info_t exception_info_o,
    output addr_t       trap_vector_o,
    output logic        pipeline_flush_o,
    output interrupt_info_t interrupt_info_o,

    // --- QoS-Enhanced Memory Interface for Exception Handling ---
    output logic                mem_req_valid_o,
    output memory_req_t         mem_req_o,
    output qos_config_t         mem_qos_config_o,     // QoS for exception memory access
    input  logic                mem_req_ready_i,
    
    input  logic                mem_rsp_valid_i,
    input  memory_rsp_t         mem_rsp_i,
    output logic                mem_rsp_ready_o,

    // --- Debug Interface with QoS ---
    input  logic                debug_req_i,          // Debug request
    input  logic [31:0]         debug_addr_i,         // Debug address
    input  logic                debug_write_i,        // Debug write
    input  word_t               debug_wdata_i,        // Debug write data
    output logic                debug_req_ready_o,    // Debug ready
    
    output logic                debug_rsp_valid_o,    // Debug response valid
    output word_t               debug_rdata_o,        // Debug read data
    output logic                debug_error_o,        // Debug error
    
    // --- QoS Configuration ---
    input  logic                qos_enable_i,         // Global QoS enable
    output logic [31:0]         qos_violations_o      // QoS violations count
);

    //---------------------------------------------------------------------------
    // QoS-Enhanced Exception Information
    //---------------------------------------------------------------------------
    typedef struct packed {
        exception_info_t         exception_info;
        qos_config_t             qos_config;          // QoS for this exception
        logic                    memory_access_req;   // Requires memory access
        addr_t                   memory_addr;         // Memory address for exception
        logic                    debug_access;        // Debug-related exception
    } qos_exception_info_t;

    //---------------------------------------------------------------------------
    // Exception Priority and QoS Mapping
    //---------------------------------------------------------------------------
    function automatic qos_config_t get_exception_qos_config(
        input exception_info_t exc_info,
        input logic is_debug,
        input logic is_interrupt
    );
        qos_config_t qos_config;
        
        // Base configuration
        qos_config.urgent = 1'b1;                    // All exceptions are urgent
        qos_config.guaranteed_bw = 1'b1;             // Guarantee bandwidth
        qos_config.weight = QOS_WEIGHT_CRITICAL;     // Maximum weight
        qos_config.bandwidth_percent = 8'd50;        // 50% bandwidth allocation
        qos_config.preemptable = 1'b0;              // Cannot be preempted
        qos_config.real_time = 1'b1;                // Real-time requirement
        qos_config.retry_limit = 3'd0;              // No retries for exceptions
        qos_config.ordered = 1'b1;                  // Maintain ordering
        
        // QoS level and type based on exception type
        if (is_debug) begin
            // Debug access - highest priority
            qos_config.qos_level = QOS_LEVEL_CRITICAL;
            qos_config.transaction_type = QOS_TYPE_DEBUG;
            qos_config.max_latency_cycles = 16'd5;   // 5 cycles max for debug
        end else if (is_interrupt) begin
            // Interrupt handling - critical priority
            qos_config.qos_level = QOS_LEVEL_CRITICAL;
            qos_config.transaction_type = QOS_TYPE_EXCEPTION;
            qos_config.max_latency_cycles = 16'd10;  // 10 cycles max for interrupts
        end else begin
            // Exception handling based on type
            case (exc_info.cause)
                EXC_CAUSE_INSTR_ACCESS_FAULT,
                EXC_CAUSE_LOAD_ACCESS_FAULT,
                EXC_CAUSE_STORE_ACCESS_FAULT: begin
                    qos_config.qos_level = QOS_LEVEL_CRITICAL;
                    qos_config.transaction_type = QOS_TYPE_EXCEPTION;
                    qos_config.max_latency_cycles = 16'd10;
                end
                
                EXC_CAUSE_BREAKPOINT: begin
                    qos_config.qos_level = QOS_LEVEL_CRITICAL;
                    qos_config.transaction_type = QOS_TYPE_DEBUG;
                    qos_config.max_latency_cycles = 16'd5;
                end
                
                EXC_CAUSE_ECALL_M: begin
                    qos_config.qos_level = QOS_LEVEL_HIGH;
                    qos_config.transaction_type = QOS_TYPE_EXCEPTION;
                    qos_config.max_latency_cycles = 16'd15;
                end
                
                default: begin
                    qos_config.qos_level = QOS_LEVEL_HIGH;
                    qos_config.transaction_type = QOS_TYPE_EXCEPTION;
                    qos_config.max_latency_cycles = 16'd20;
                end
            endcase
        end
        
        // Core ID assignment (assuming single core for now)
        qos_config.core_id = 4'h0;
        
        return qos_config;
    endfunction

    //---------------------------------------------------------------------------
    // Internal Exception Processing
    //---------------------------------------------------------------------------
    qos_exception_info_t selected_exception;
    logic exception_memory_access_needed;
    logic debug_memory_access_needed;
    
    // Original exception handler logic (simplified)
    exception_info_t fetch_exception_detected;
    exception_info_t execute_exception_detected;
    exception_info_t memory_exception_detected;
    exception_info_t writeback_exception_detected;
    exception_info_t interrupt_detected;
    exception_info_t final_selected_exception;
    
    logic [3:0] exception_priorities;
    logic [3:0] highest_priority;
    logic interrupt_enabled;

    //---------------------------------------------------------------------------
    // Interrupt Detection and Masking (Original Logic)
    //---------------------------------------------------------------------------
    assign interrupt_enabled = mstatus_mie_i;
    
    assign interrupt_info_o.m_software_interrupt = mip_msip_i && mie_msie_i && interrupt_enabled;
    assign interrupt_info_o.m_timer_interrupt = mip_mtip_i && mie_mtie_i && interrupt_enabled;
    assign interrupt_info_o.m_external_interrupt = mip_meip_i && mie_meie_i && interrupt_enabled;
    
    assign interrupt_info_o.interrupt_pending = interrupt_info_o.m_software_interrupt ||
                                               interrupt_info_o.m_timer_interrupt ||
                                               interrupt_info_o.m_external_interrupt;

    always_comb begin
        interrupt_info_o.interrupt_cause = EXC_CAUSE_M_SOFTWARE_INTERRUPT; // Default
        if (interrupt_info_o.m_external_interrupt) begin
            interrupt_info_o.interrupt_cause = EXC_CAUSE_M_EXTERNAL_INTERRUPT;
        end else if (interrupt_info_o.m_timer_interrupt) begin
            interrupt_info_o.interrupt_cause = EXC_CAUSE_M_TIMER_INTERRUPT;
        end else if (interrupt_info_o.m_software_interrupt) begin
            interrupt_info_o.interrupt_cause = EXC_CAUSE_M_SOFTWARE_INTERRUPT;
        end
    end

    always_comb begin
        interrupt_detected.valid = interrupt_info_o.interrupt_pending;
        interrupt_detected.exc_type = EXC_TYPE_INTERRUPT;
        interrupt_detected.cause = interrupt_info_o.interrupt_cause;
        interrupt_detected.pc = '0;
        interrupt_detected.tval = '0;
        interrupt_detected.priority = PRIO_INTERRUPT;
    end

    //---------------------------------------------------------------------------
    // Exception Priority Resolution (Original Logic)
    //---------------------------------------------------------------------------
    assign fetch_exception_detected = fetch_exception_i;
    assign execute_exception_detected = execute_exception_i;
    assign memory_exception_detected = memory_exception_i;
    assign writeback_exception_detected = writeback_exception_i;

    assign exception_priorities[0] = fetch_exception_detected.valid ? fetch_exception_detected.priority : PRIO_NONE;
    assign exception_priorities[1] = execute_exception_detected.valid ? execute_exception_detected.priority : PRIO_NONE;
    assign exception_priorities[2] = memory_exception_detected.valid ? memory_exception_detected.priority : PRIO_NONE;
    assign exception_priorities[3] = writeback_exception_detected.valid ? writeback_exception_detected.priority : PRIO_NONE;

    always_comb begin
        highest_priority = PRIO_NONE;
        if (exception_priorities[0] != PRIO_NONE && exception_priorities[0] < highest_priority) highest_priority = exception_priorities[0];
        if (exception_priorities[1] != PRIO_NONE && exception_priorities[1] < highest_priority) highest_priority = exception_priorities[1];
        if (exception_priorities[2] != PRIO_NONE && exception_priorities[2] < highest_priority) highest_priority = exception_priorities[2];
        if (exception_priorities[3] != PRIO_NONE && exception_priorities[3] < highest_priority) highest_priority = exception_priorities[3];
    end

    always_comb begin
        final_selected_exception = '0;
        
        if (interrupt_detected.valid) begin
            final_selected_exception = interrupt_detected;
        end
        else if (fetch_exception_detected.valid && fetch_exception_detected.priority == highest_priority) begin
            final_selected_exception = fetch_exception_detected;
        end
        else if (execute_exception_detected.valid && execute_exception_detected.priority == highest_priority) begin
            final_selected_exception = execute_exception_detected;
        end
        else if (memory_exception_detected.valid && memory_exception_detected.priority == highest_priority) begin
            final_selected_exception = memory_exception_detected;
        end
        else if (writeback_exception_detected.valid && writeback_exception_detected.priority == highest_priority) begin
            final_selected_exception = writeback_exception_detected;
        end
    end

    //---------------------------------------------------------------------------
    // QoS-Enhanced Exception Processing
    //---------------------------------------------------------------------------
    always_comb begin : proc_qos_exception_processing
        // Create QoS-enhanced exception information
        selected_exception.exception_info = final_selected_exception;
        selected_exception.debug_access = debug_req_i || 
                                         (final_selected_exception.cause == EXC_CAUSE_BREAKPOINT);
        
        // Determine QoS configuration
        selected_exception.qos_config = get_exception_qos_config(
            final_selected_exception,
            selected_exception.debug_access,
            interrupt_detected.valid
        );
        
        // Determine if memory access is needed
        exception_memory_access_needed = final_selected_exception.valid && (
            // Need to fetch exception handler address
            (mtvec_mode_i == 2'b01) || // Vectored mode needs table lookup
            // Need to save/restore context
            (final_selected_exception.exc_type == EXC_TYPE_EXCEPTION) ||
            // Memory access fault needs investigation
            (final_selected_exception.cause == EXC_CAUSE_LOAD_ACCESS_FAULT) ||
            (final_selected_exception.cause == EXC_CAUSE_STORE_ACCESS_FAULT) ||
            (final_selected_exception.cause == EXC_CAUSE_INSTR_ACCESS_FAULT)
        );
        
        selected_exception.memory_access_req = exception_memory_access_needed;
        
        // Calculate memory address for exception
        if (mtvec_mode_i == 2'b01) begin
            // Vectored mode - calculate table entry address
            selected_exception.memory_addr = {mtvec_base_i[31:2], 2'b00} + 
                                            (final_selected_exception.cause << 2);
        end else begin
            // Direct mode - use base address
            selected_exception.memory_addr = {mtvec_base_i[31:2], 2'b00};
        end
    end

    //---------------------------------------------------------------------------
    // Debug Interface QoS Processing
    //---------------------------------------------------------------------------
    logic debug_active;
    qos_config_t debug_qos_config;
    
    always_comb begin : proc_debug_qos
        debug_active = debug_req_i;
        debug_memory_access_needed = debug_req_i;
        
        // Debug always gets critical QoS
        debug_qos_config = get_exception_qos_config('0, 1'b1, 1'b0);
    end

    //---------------------------------------------------------------------------
    // Memory Interface Arbitration
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        MEM_IDLE,
        MEM_EXCEPTION,
        MEM_DEBUG
    } mem_access_state_e;
    
    mem_access_state_e mem_state;
    logic [31:0] qos_violation_counter;
    
    always_comb begin : proc_memory_arbitration
        // Default outputs
        mem_req_valid_o = 1'b0;
        mem_req_o = '0;
        mem_qos_config_o = '0;
        debug_req_ready_o = 1'b0;
        
        // Prioritize debug access over exception access
        if (debug_memory_access_needed && qos_enable_i) begin
            mem_req_valid_o = 1'b1;
            mem_req_o.addr = debug_addr_i;
            mem_req_o.write = debug_write_i;
            mem_req_o.data = debug_wdata_i;
            mem_req_o.strb = 4'hF; // Full word access
            mem_qos_config_o = debug_qos_config;
            debug_req_ready_o = mem_req_ready_i;
        end else if (exception_memory_access_needed && qos_enable_i) begin
            mem_req_valid_o = 1'b1;
            mem_req_o.addr = selected_exception.memory_addr;
            mem_req_o.write = 1'b0; // Exception handling typically reads
            mem_req_o.data = '0;
            mem_req_o.strb = 4'hF; // Full word access
            mem_qos_config_o = selected_exception.qos_config;
        end
    end

    //---------------------------------------------------------------------------
    // QoS Violation Monitoring
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_qos_monitoring
        if (!rst_ni) begin
            qos_violation_counter <= 0;
        end else begin
            // Monitor for QoS violations in exception/debug access
            if (mem_req_valid_o && !mem_req_ready_i) begin
                // Memory not ready for critical access - potential violation
                qos_violation_counter <= qos_violation_counter + 1;
            end
            
            // Monitor debug access latency
            if (debug_req_i && !debug_req_ready_o) begin
                // Debug access delayed - critical violation
                qos_violation_counter <= qos_violation_counter + 1;
            end
        end
    end

    //---------------------------------------------------------------------------
    // Debug Response Handling
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_debug_response
        if (!rst_ni) begin
            debug_rsp_valid_o <= 1'b0;
            debug_rdata_o <= '0;
            debug_error_o <= 1'b0;
        end else begin
            if (mem_rsp_valid_i && debug_active) begin
                debug_rsp_valid_o <= 1'b1;
                debug_rdata_o <= mem_rsp_i.data;
                debug_error_o <= mem_rsp_i.error;
            end else begin
                debug_rsp_valid_o <= 1'b0;
                debug_error_o <= 1'b0;
            end
        end
    end

    //---------------------------------------------------------------------------
    // Trap Vector Generation (Original Logic with QoS Enhancement)
    //---------------------------------------------------------------------------
    always_comb begin
        if (final_selected_exception.valid) begin
            if (mtvec_mode_i == 2'b01) begin
                // Vectored mode - address calculated above with QoS
                trap_vector_o = selected_exception.memory_addr;
            end else begin
                // Direct mode
                trap_vector_o = {mtvec_base_i[31:2], 2'b00};
            end
        end else begin
            trap_vector_o = '0;
        end
    end

    //---------------------------------------------------------------------------
    // Output Assignments
    //---------------------------------------------------------------------------
    assign exception_valid_o = final_selected_exception.valid;
    assign exception_info_o = final_selected_exception;
    assign pipeline_flush_o = final_selected_exception.valid;
    assign qos_violations_o = qos_violation_counter;
    assign mem_rsp_ready_o = 1'b1; // Always ready to accept responses

endmodule : qos_exception_handler

`default_nettype wire 