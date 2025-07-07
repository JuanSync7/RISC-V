//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: exception_handler.sv
// Module: exception_handler
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Enhanced Exception Handler for the RISC-V core. Detects and prioritizes
//   exceptions and interrupts, generates trap vectors based on mtvec
//   configuration, provides exception information for CSR updates, and
//   handles interrupt masking and priority resolution.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_config_pkg::*;

module exception_handler #(
    parameter integer CORE_ID = 0
)
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Exception Inputs from Pipeline Stages ---
    // AI_TAG: PORT_DESC - fetch_exception_i - Exception from fetch stage (instruction faults)
    input  exception_info_t fetch_exception_i,
    // AI_TAG: PORT_DESC - execute_exception_i - Exception from execute stage (ALU, illegal instr)
    input  exception_info_t execute_exception_i,
    // AI_TAG: PORT_DESC - memory_exception_i - Exception from memory stage (load/store faults)
    input  exception_info_t memory_exception_i,
    // AI_TAG: PORT_DESC - writeback_exception_i - Exception from writeback stage (delayed faults)
    input  exception_info_t writeback_exception_i,

    // --- Interrupt Inputs ---
    // AI_TAG: PORT_DESC - m_software_interrupt_i - Machine software interrupt
    input  logic        m_software_interrupt_i,
    // AI_TAG: PORT_DESC - m_timer_interrupt_i - Machine timer interrupt
    input  logic        m_timer_interrupt_i,
    // AI_TAG: PORT_DESC - m_external_interrupt_i - Machine external interrupt
    input  logic        m_external_interrupt_i,

    // --- CSR State Inputs ---
    // AI_TAG: PORT_DESC - mstatus_mie_i - Machine interrupt enable from mstatus
    input  logic        mstatus_mie_i,
    // AI_TAG: PORT_DESC - mie_msie_i - Machine software interrupt enable
    input  logic        mie_msie_i,
    // AI_TAG: PORT_DESC - mie_mtie_i - Machine timer interrupt enable
    input  logic        mie_mtie_i,
    // AI_TAG: PORT_DESC - mie_meie_i - Machine external interrupt enable
    input  logic        mie_meie_i,
    // AI_TAG: PORT_DESC - mip_msip_i - Machine software interrupt pending
    input  logic        mip_msip_i,
    // AI_TAG: PORT_DESC - mip_mtip_i - Machine timer interrupt pending
    input  logic        mip_mtip_i,
    // AI_TAG: PORT_DESC - mip_meip_i - Machine external interrupt pending
    input  logic        mip_meip_i,
    // AI_TAG: PORT_DESC - mtvec_base_i - Trap vector base address
    input  addr_t       mtvec_base_i,
    // AI_TAG: PORT_DESC - mtvec_mode_i - Trap vector mode (00=direct, 01=vectored)
    input  logic [1:0]  mtvec_mode_i,

    // --- Exception Outputs ---
    // AI_TAG: PORT_DESC - exception_valid_o - Exception is valid and should be taken
    output logic        exception_valid_o,
    // AI_TAG: PORT_DESC - exception_info_o - Selected exception information
    output exception_info_t exception_info_o,
    // AI_TAG: PORT_DESC - trap_vector_o - Calculated trap vector address
    output addr_t       trap_vector_o,
    // AI_TAG: PORT_DESC - pipeline_flush_o - Pipeline should be flushed
    output logic        pipeline_flush_o,
    output exception_info_t exception_o,

    // --- Interrupt Outputs ---
    // AI_TAG: PORT_DESC - interrupt_info_o - Current interrupt state
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

    // AI_TAG: INTERNAL_WIRE - Internal exception and interrupt signals
    exception_info_t fetch_exception_detected;
    exception_info_t execute_exception_detected;
    exception_info_t memory_exception_detected;
    exception_info_t writeback_exception_detected;
    exception_info_t interrupt_detected;
    exception_info_t selected_exception;
    logic [3:0] exception_priorities;
    logic [3:0] highest_priority;
    logic interrupt_enabled;

    // AI_TAG: INTERNAL_LOGIC - Interrupt Detection and Masking
    // Check if interrupts are enabled and pending
    assign interrupt_enabled = mstatus_mie_i;
    
    // Detect enabled and pending interrupts
    assign interrupt_info_o.m_software_interrupt = mip_msip_i && mie_msie_i && interrupt_enabled;
    assign interrupt_info_o.m_timer_interrupt = mip_mtip_i && mie_mtie_i && interrupt_enabled;
    assign interrupt_info_o.m_external_interrupt = mip_meip_i && mie_meie_i && interrupt_enabled;
    
    // Determine if any interrupt is pending
    assign interrupt_info_o.interrupt_pending = interrupt_info_o.m_software_interrupt ||
                                               interrupt_info_o.m_timer_interrupt ||
                                               interrupt_info_o.m_external_interrupt;

    // AI_TAG: INTERNAL_LOGIC - Interrupt Priority Resolution
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

    // AI_TAG: INTERNAL_LOGIC - Interrupt Exception Generation
    always_comb begin
        interrupt_detected.valid = interrupt_info_o.interrupt_pending;
        interrupt_detected.exc_type = EXC_TYPE_INTERRUPT;
        interrupt_detected.cause = interrupt_info_o.interrupt_cause;
        interrupt_detected.pc = '0; // Will be set by the stage taking the interrupt
        interrupt_detected.tval = '0; // Interrupts don't have tval
        interrupt_detected.priority = PRIO_INTERRUPT;
    end

    // AI_TAG: INTERNAL_LOGIC - Exception Detection from Pipeline Stages
    // Pass through exceptions from pipeline stages
    assign fetch_exception_detected = fetch_exception_i;
    assign execute_exception_detected = execute_exception_i;
    assign memory_exception_detected = memory_exception_i;
    assign writeback_exception_detected = writeback_exception_i;

    // AI_TAG: INTERNAL_LOGIC - Exception Priority Resolution
    // Collect all exception priorities
    assign exception_priorities[0] = fetch_exception_detected.valid ? fetch_exception_detected.priority : PRIO_NONE;
    assign exception_priorities[1] = execute_exception_detected.valid ? execute_exception_detected.priority : PRIO_NONE;
    assign exception_priorities[2] = memory_exception_detected.valid ? memory_exception_detected.priority : PRIO_NONE;
    assign exception_priorities[3] = writeback_exception_detected.valid ? writeback_exception_detected.priority : PRIO_NONE;

    // Find highest priority exception
    always_comb begin
        highest_priority = PRIO_NONE;
        if (exception_priorities[0] != PRIO_NONE && exception_priorities[0] < highest_priority) highest_priority = exception_priorities[0];
        if (exception_priorities[1] != PRIO_NONE && exception_priorities[1] < highest_priority) highest_priority = exception_priorities[1];
        if (exception_priorities[2] != PRIO_NONE && exception_priorities[2] < highest_priority) highest_priority = exception_priorities[2];
        if (exception_priorities[3] != PRIO_NONE && exception_priorities[3] < highest_priority) highest_priority = exception_priorities[3];
    end

    // AI_TAG: INTERNAL_LOGIC - Exception Selection
    always_comb begin
        selected_exception = '0; // Default to no exception
        
        // Check interrupts first (highest priority)
        if (interrupt_detected.valid) begin
            selected_exception = interrupt_detected;
        end
        // Check pipeline exceptions in priority order
        else if (fetch_exception_detected.valid && fetch_exception_detected.priority == highest_priority) begin
            selected_exception = fetch_exception_detected;
        end
        else if (execute_exception_detected.valid && execute_exception_detected.priority == highest_priority) begin
            selected_exception = execute_exception_detected;
        end
        else if (memory_exception_detected.valid && memory_exception_detected.priority == highest_priority) begin
            selected_exception = memory_exception_detected;
        end
        else if (writeback_exception_detected.valid && writeback_exception_detected.priority == highest_priority) begin
            selected_exception = writeback_exception_detected;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Trap Vector Generation
    always_comb begin
        if (selected_exception.valid) begin
            if (selected_exception.exc_type == EXC_TYPE_INTERRUPT) begin
                // Interrupts always use vectored mode if enabled
                if (mtvec_mode_i == 2'b01) begin
                    trap_vector_o = {mtvec_base_i[31:2], 2'b00} + (selected_exception.cause << 2);
                end else begin
                    trap_vector_o = {mtvec_base_i[31:2], 2'b00};
                end
            end else begin
                // Exceptions use vectored mode if enabled
                if (mtvec_mode_i == 2'b01) begin
                    trap_vector_o = {mtvec_base_i[31:2], 2'b00} + (selected_exception.cause << 2);
                end else begin
                    trap_vector_o = {mtvec_base_i[31:2], 2'b00};
                end
            end
        end else begin
            trap_vector_o = '0;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Output Generation
    assign exception_valid_o = selected_exception.valid;
    assign exception_info_o = selected_exception;
    assign exception_o = selected_exception;
    assign pipeline_flush_o = selected_exception.valid;

    //---------------------------------------------------------------------------
    // QoS Configuration for Exception Handling
    //---------------------------------------------------------------------------
    function automatic qos_config_t get_exception_qos_config(
        input exception_info_t exc_info,
        input logic is_debug,
        input logic is_interrupt
    );
        qos_config_t qos_config;
        
        // Base configuration for all exceptions
        qos_config.urgent = 1'b1;                    // All exceptions are urgent
        qos_config.guaranteed_bw = 1'b1;             // Guarantee bandwidth
        qos_config.weight = QOS_WEIGHT_CRITICAL;     // Maximum weight
        qos_config.bandwidth_percent = QOS_EXCEPTION_BW_PERCENT;        // 50% bandwidth allocation
        qos_config.preemptable = 1'b0;              // Cannot be preempted
        qos_config.real_time = 1'b1;                // Real-time requirement
        qos_config.retry_limit = QOS_EXCEPTION_RETRY_LIMIT;              // No retries for exceptions
        qos_config.ordered = 1'b1;                  // Maintain ordering
        qos_config.core_id = CORE_ID[3:0];                  // Core ID
        
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
        
        return qos_config;
    endfunction

    //---------------------------------------------------------------------------
    // QoS-Enhanced Memory Access for Exception Handling
    //---------------------------------------------------------------------------
    logic exception_memory_access_needed;
    logic debug_memory_access_needed;
    logic [31:0] qos_violation_counter;
    qos_config_t exception_qos_config;
    qos_config_t debug_qos_config;
    
    always_comb begin : proc_exception_memory_qos
        // Determine if memory access is needed for exception handling
        exception_memory_access_needed = selected_exception.valid && (
            // Vectored mode needs table lookup
            (mtvec_mode_i == 2'b01) ||
            // Memory access faults need investigation
            (selected_exception.cause == EXC_CAUSE_LOAD_ACCESS_FAULT) ||
            (selected_exception.cause == EXC_CAUSE_STORE_ACCESS_FAULT) ||
            (selected_exception.cause == EXC_CAUSE_INSTR_ACCESS_FAULT)
        );
        
        // Configure QoS for exception handling
        exception_qos_config = get_exception_qos_config(
            selected_exception,
            1'b0,  // Not debug
            interrupt_detected.valid
        );
        
        // Debug memory access
        debug_memory_access_needed = debug_req_i;
        debug_qos_config = get_exception_qos_config(
            '0,    // No exception info for debug
            1'b1,  // Is debug
            1'b0   // Not interrupt
        );
    end

    //---------------------------------------------------------------------------
    // QoS Memory Interface Arbitration
    //---------------------------------------------------------------------------
    always_comb begin : proc_qos_memory_arbitration
        // Default outputs
        mem_req_valid_o = 1'b0;
        mem_req_o = '0;
        mem_qos_config_o = '0;
        debug_req_ready_o = 1'b0;
        
        // Prioritize debug access over exception access (both are critical)
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
            
            // Calculate exception memory address
            if (mtvec_mode_i == 2'b01) begin
                // Vectored mode - calculate table entry address
                mem_req_o.addr = {mtvec_base_i[31:2], 2'b00} + (selected_exception.cause << 2);
            end else begin
                // Direct mode - use base address
                mem_req_o.addr = {mtvec_base_i[31:2], 2'b00};
            end
            
            mem_req_o.write = 1'b0; // Exception handling typically reads
            mem_req_o.data = '0;
            mem_req_o.strb = 4'hF; // Full word access
            mem_qos_config_o = exception_qos_config;
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
            if (mem_rsp_valid_i && debug_memory_access_needed) begin
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
    // Additional Output Assignments
    //---------------------------------------------------------------------------
    assign qos_violations_o = qos_violation_counter;
    assign mem_rsp_ready_o = 1'b1; // Always ready to accept responses

endmodule : exception_handler

//=============================================================================
// Dependencies: riscv_core_pkg.sv
// Instantiated In:
//   - core/integration/core_subsystem.sv
//
// Performance:
//   - Critical Path: Exception detection to trap vector generation
//   - Max Frequency: TBD
//   - Area: TBD
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
//   - Testbench: TBD
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//=============================================================================