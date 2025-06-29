//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: exception_handler_tb.sv
// Module: exception_handler_tb
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Comprehensive testbench for the Exception Handler. Tests exception
//   prioritization, interrupt handling, trap vector generation, and
//   pipeline flush functionality. Validates complete M-mode exception support.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_types_pkg::*;
import riscv_exception_pkg::*;

module exception_handler_tb;
    // Clock and reset
    logic clk;
    logic rst_n;

    // Exception inputs from pipeline stages
    exception_info_t fetch_exception_i;
    exception_info_t execute_exception_i;
    exception_info_t memory_exception_i;
    exception_info_t writeback_exception_i;

    // Interrupt inputs
    logic        m_software_interrupt_i;
    logic        m_timer_interrupt_i;
    logic        m_external_interrupt_i;

    // CSR state inputs
    logic        mstatus_mie_i;
    logic        mie_msie_i, mie_mtie_i, mie_meie_i;
    logic        mip_msip_i, mip_mtip_i, mip_meip_i;
    addr_t       mtvec_base_i;
    logic [1:0]  mtvec_mode_i;

    // Exception outputs
    logic        exception_valid_o;
    exception_info_t exception_info_o;
    addr_t       trap_vector_o;
    logic        pipeline_flush_o;
    interrupt_info_t interrupt_info_o;

    // Instantiate Exception Handler
    exception_handler dut (
        .clk_i(clk),
        .rst_ni(rst_n),
        .fetch_exception_i(fetch_exception_i),
        .execute_exception_i(execute_exception_i),
        .memory_exception_i(memory_exception_i),
        .writeback_exception_i(writeback_exception_i),
        .m_software_interrupt_i(m_software_interrupt_i),
        .m_timer_interrupt_i(m_timer_interrupt_i),
        .m_external_interrupt_i(m_external_interrupt_i),
        .mstatus_mie_i(mstatus_mie_i),
        .mie_msie_i(mie_msie_i),
        .mie_mtie_i(mie_mtie_i),
        .mie_meie_i(mie_meie_i),
        .mip_msip_i(mip_msip_i),
        .mip_mtip_i(mip_mtip_i),
        .mip_meip_i(mip_meip_i),
        .mtvec_base_i(mtvec_base_i),
        .mtvec_mode_i(mtvec_mode_i),
        .exception_valid_o(exception_valid_o),
        .exception_info_o(exception_info_o),
        .trap_vector_o(trap_vector_o),
        .pipeline_flush_o(pipeline_flush_o),
        .interrupt_info_o(interrupt_info_o)
    );

    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

    // Test stimulus
    initial begin
        // Initialize signals
        rst_n = 0;
        fetch_exception_i = '0;
        execute_exception_i = '0;
        memory_exception_i = '0;
        writeback_exception_i = '0;
        m_software_interrupt_i = 0;
        m_timer_interrupt_i = 0;
        m_external_interrupt_i = 0;
        mstatus_mie_i = 0;
        mie_msie_i = 0;
        mie_mtie_i = 0;
        mie_meie_i = 0;
        mip_msip_i = 0;
        mip_mtip_i = 0;
        mip_meip_i = 0;
        mtvec_base_i = 32'h0000_1000;
        mtvec_mode_i = 2'b00; // Direct mode

        #20;
        rst_n = 1;
        #10;

        // Test 1: No exception condition
        $display("[TB] Test 1: No exception condition");
        test_no_exception();

        // Test 2: Exception prioritization
        $display("[TB] Test 2: Exception prioritization");
        test_exception_prioritization();

        // Test 3: Interrupt handling
        $display("[TB] Test 3: Interrupt handling");
        test_interrupt_handling();

        // Test 4: Trap vector generation
        $display("[TB] Test 4: Trap vector generation");
        test_trap_vector_generation();

        // Test 5: Pipeline flush functionality
        $display("[TB] Test 5: Pipeline flush functionality");
        test_pipeline_flush();

        // Test 6: CSR state interaction
        $display("[TB] Test 6: CSR state interaction");
        test_csr_interaction();

        // Test 7: Corner cases
        $display("[TB] Test 7: Corner cases");
        test_corner_cases();

        $display("[TB] All exception handler tests complete");
        $finish;
    end

    // Test 1: No exception condition
    task test_no_exception();
        // Clear all exceptions and interrupts
        fetch_exception_i = '0;
        execute_exception_i = '0;
        memory_exception_i = '0;
        writeback_exception_i = '0;
        m_software_interrupt_i = 0;
        m_timer_interrupt_i = 0;
        m_external_interrupt_i = 0;
        mstatus_mie_i = 0;

        @(posedge clk);
        @(posedge clk);

        if (!exception_valid_o && !pipeline_flush_o) begin
            $display("[TB] No exception condition - PASS");
        end else begin
            $display("[TB] ERROR: Exception detected when none should be");
        end
    endtask

    // Test 2: Exception prioritization
    task test_exception_prioritization();
        // Create multiple exceptions with different priorities
        fetch_exception_i.valid = 1;
        fetch_exception_i.cause = `CAUSE_FETCH_ACCESS;
        fetch_exception_i.tval  = 32'h0000_2000;

        execute_exception_i.valid = 1;
        execute_exception_i.cause = `CAUSE_ILLEGAL_INSTRUCTION;
        execute_exception_i.tval = 32'h0000_2004;

        memory_exception_i.valid = 1;
        memory_exception_i.cause = `CAUSE_LOAD_ACCESS_FAULT;
        memory_exception_i.tval = 32'h0000_2008;

        @(posedge clk);
        @(posedge clk);

        // Should select highest priority exception (instruction access fault)
        if (exception_valid_o && exception_info_o.cause == `CAUSE_FETCH_ACCESS) begin
            $display("[TB] Exception prioritization - PASS (selected cause %h)", exception_info_o.cause);
        end else begin
            $display("[TB] ERROR: Wrong exception priority selected (got %h, expected %h)", 
                    exception_info_o.cause, `CAUSE_FETCH_ACCESS);
        end

        // Clear exceptions
        fetch_exception_i = '0;
        execute_exception_i = '0;
        memory_exception_i = '0;
    endtask

    // Test 3: Interrupt handling
    task test_interrupt_handling();
        // Enable interrupts
        mstatus_mie_i = 1;
        mie_msie_i = 1;
        mie_mtie_i = 1;
        mie_meie_i = 1;

        // Test software interrupt
        mip_msip_i = 1;
        @(posedge clk);
        @(posedge clk);

        if (exception_valid_o && exception_info_o.exc_type == EXC_TYPE_INTERRUPT && 
            exception_info_o.cause == EXC_CAUSE_M_SOFTWARE_INTERRUPT) begin
            $display("[TB] Software interrupt handling - PASS");
        end else begin
            $display("[TB] ERROR: Software interrupt not handled correctly");
        end

        // Test timer interrupt
        mip_msip_i = 0;
        mip_mtip_i = 1;
        @(posedge clk);
        @(posedge clk);

        if (exception_valid_o && exception_info_o.exc_type == EXC_TYPE_INTERRUPT && 
            exception_info_o.cause == EXC_CAUSE_M_TIMER_INTERRUPT) begin
            $display("[TB] Timer interrupt handling - PASS");
        end else begin
            $display("[TB] ERROR: Timer interrupt not handled correctly");
        end

        // Test external interrupt
        mip_mtip_i = 0;
        mip_meip_i = 1;
        @(posedge clk);
        @(posedge clk);

        if (exception_valid_o && exception_info_o.exc_type == EXC_TYPE_INTERRUPT && 
            exception_info_o.cause == EXC_CAUSE_M_EXTERNAL_INTERRUPT) begin
            $display("[TB] External interrupt handling - PASS");
        end else begin
            $display("[TB] ERROR: External interrupt not handled correctly");
        end

        // Clear interrupts
        mip_meip_i = 0;
        mstatus_mie_i = 0;
    endtask

    // Test 4: Trap vector generation
    task test_trap_vector_generation();
        // Test direct mode
        mtvec_mode_i = 2'b00;
        mtvec_base_i = 32'h0000_1000;

        fetch_exception_i.valid = 1;
        fetch_exception_i.exc_type = EXC_TYPE_EXCEPTION;
        fetch_exception_i.cause = EXC_CAUSE_INSTR_ACCESS_FAULT;
        fetch_exception_i.pc = 32'h0000_2000;
        fetch_exception_i.priority = PRIO_INSTR_FAULT;

        @(posedge clk);
        @(posedge clk);

        if (trap_vector_o == 32'h0000_1000) begin
            $display("[TB] Direct mode trap vector - PASS");
        end else begin
            $display("[TB] ERROR: Direct mode trap vector incorrect (got %h, expected %h)", 
                    trap_vector_o, 32'h0000_1000);
        end

        // Test vectored mode
        mtvec_mode_i = 2'b01;
        mtvec_base_i = 32'h0000_2000;

        @(posedge clk);
        @(posedge clk);

        addr_t expected_vector = 32'h0000_2000 + (EXC_CAUSE_INSTR_ACCESS_FAULT << 2);
        if (trap_vector_o == expected_vector) begin
            $display("[TB] Vectored mode trap vector - PASS");
        end else begin
            $display("[TB] ERROR: Vectored mode trap vector incorrect (got %h, expected %h)", 
                    trap_vector_o, expected_vector);
        end

        // Clear exception
        fetch_exception_i = '0;
    endtask

    // Test 5: Pipeline flush functionality
    task test_pipeline_flush();
        // Create an exception
        execute_exception_i.valid = 1;
        execute_exception_i.exc_type = EXC_TYPE_EXCEPTION;
        execute_exception_i.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
        execute_exception_i.pc = 32'h0000_3000;
        execute_exception_i.priority = PRIO_ILLEGAL;

        @(posedge clk);
        @(posedge clk);

        if (pipeline_flush_o) begin
            $display("[TB] Pipeline flush on exception - PASS");
        end else begin
            $display("[TB] ERROR: Pipeline not flushed on exception");
        end

        // Clear exception
        execute_exception_i = '0;
    endtask

    // Test 6: CSR state interaction
    task test_csr_interaction();
        // Test with interrupts disabled
        mstatus_mie_i = 0;
        mip_msip_i = 1;
        mie_msie_i = 1;

        @(posedge clk);
        @(posedge clk);

        if (!exception_valid_o) begin
            $display("[TB] Interrupt disabled by CSR - PASS");
        end else begin
            $display("[TB] ERROR: Interrupt taken when disabled");
        end

        // Test with interrupts enabled
        mstatus_mie_i = 1;
        @(posedge clk);
        @(posedge clk);

        if (exception_valid_o && exception_info_o.exc_type == EXC_TYPE_INTERRUPT) begin
            $display("[TB] Interrupt enabled by CSR - PASS");
        end else begin
            $display("[TB] ERROR: Interrupt not taken when enabled");
        end

        // Clear interrupt
        mip_msip_i = 0;
        mstatus_mie_i = 0;
    endtask

    // Test 7: Corner cases
    task test_corner_cases();
        // Test multiple interrupts simultaneously
        mstatus_mie_i = 1;
        mie_msie_i = 1;
        mie_mtie_i = 1;
        mie_meie_i = 1;
        mip_msip_i = 1;
        mip_mtip_i = 1;
        mip_meip_i = 1;

        @(posedge clk);
        @(posedge clk);

        // Should prioritize external interrupt (highest priority)
        if (exception_valid_o && exception_info_o.cause == EXC_CAUSE_M_EXTERNAL_INTERRUPT) begin
            $display("[TB] Multiple interrupt prioritization - PASS");
        end else begin
            $display("[TB] ERROR: Wrong interrupt prioritized");
        end

        // Test exception with zero PC
        mip_meip_i = 0;
        fetch_exception_i.valid = 1;
        fetch_exception_i.exc_type = EXC_TYPE_EXCEPTION;
        fetch_exception_i.cause = EXC_CAUSE_INSTR_ACCESS_FAULT;
        fetch_exception_i.pc = 32'h0000_0000;
        fetch_exception_i.priority = PRIO_INSTR_FAULT;

        @(posedge clk);
        @(posedge clk);

        if (exception_valid_o && exception_info_o.pc == 32'h0000_0000) begin
            $display("[TB] Zero PC exception - PASS");
        end else begin
            $display("[TB] ERROR: Zero PC exception not handled");
        end

        // Clear all
        fetch_exception_i = '0;
        mip_msip_i = 0;
        mip_mtip_i = 0;
        mstatus_mie_i = 0;
    endtask

    // Coverage
    covergroup exception_handler_cg @(posedge clk);
        exception_valid_cp: coverpoint exception_valid_o;
        exception_type_cp: coverpoint exception_info_o.exc_type;
        exception_cause_cp: coverpoint exception_info_o.cause {
            bins interrupts[] = {EXC_CAUSE_M_SOFTWARE_INTERRUPT, EXC_CAUSE_M_TIMER_INTERRUPT, EXC_CAUSE_M_EXTERNAL_INTERRUPT};
            bins exceptions[] = {EXC_CAUSE_INSTR_ACCESS_FAULT, EXC_CAUSE_ILLEGAL_INSTRUCTION, EXC_CAUSE_LOAD_ACCESS_FAULT};
        }
        pipeline_flush_cp: coverpoint pipeline_flush_o;
        mtvec_mode_cp: coverpoint mtvec_mode_i;
        mstatus_mie_cp: coverpoint mstatus_mie_i;
        
        exception_type_valid_cross: cross exception_type_cp, exception_valid_cp;
        flush_valid_cross: cross pipeline_flush_cp, exception_valid_cp;
    endgroup

    exception_handler_cg eh_cg = new();

endmodule : exception_handler_tb 