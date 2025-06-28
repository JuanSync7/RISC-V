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

module exception_handler
    import riscv_core_pkg::*;
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

    // --- Interrupt Outputs ---
    // AI_TAG: PORT_DESC - interrupt_info_o - Current interrupt state
    output interrupt_info_t interrupt_info_o
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
    assign pipeline_flush_o = selected_exception.valid;

endmodule : exception_handler

//=============================================================================
// Dependencies: riscv_core_pkg.sv
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
// NOTE: `default_nettype wire is set below for legacy compatibility. Prefer keeping `none` throughout the project and explicitly typing all signals. Remove if not required.
`default_nettype wire 