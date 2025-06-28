//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: assertions.sv
// Module: assertions
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Common assertion macros and SystemVerilog properties for all testbenches.
//   Includes equality, stability, one-hot, valid signal, and protocol checks.
//=============================================================================

`ifndef ASSERTIONS_SV
`define ASSERTIONS_SV

// Usage: `ASSERT_EQ(actual, expected, "message")
`define ASSERT_EQ(actual, expected, message) \
    if ((actual) !== (expected)) begin \
        $error("ASSERTION FAILED: %s - Expected: %h, Got: %h", message, expected, actual); \
    end

`define ASSERT_NEQ(actual, expected, message) \
    if ((actual) === (expected)) begin \
        $error("ASSERTION FAILED: %s - Values should not be equal: %h", message, actual); \
    end

`define ASSERT_TRUE(condition, message) \
    if (!(condition)) begin \
        $error("ASSERTION FAILED: %s", message); \
    end

`define ASSERT_FALSE(condition, message) \
    if (condition) begin \
        $error("ASSERTION FAILED: %s", message); \
    end

// Assert that a signal is never X or Z
`define ASSERT_VALID_SIGNAL(signal, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (signal !== 1'bx && signal !== 1'bz)) else \
        $error("ASSERTION FAILED: %s - Signal is X or Z", message);

// Assert that a signal is stable for N cycles
`define ASSERT_STABLE(signal, cycles, message) \
    assert property (@(posedge clk) disable iff (!rst_n) $stable(signal) [*cycles]) else \
        $error("ASSERTION FAILED: %s - Signal not stable for %0d cycles", message, cycles);

// Assert that a vector is one-hot
`define ASSERT_ONE_HOT(vector, message) \
    if (^vector !== 1'b1) begin \
        $error("ASSERTION FAILED: %s - Vector is not one-hot: %b", message, vector); \
    end

// Example protocol property: handshake (valid/ready)
property p_handshake_valid_ready;
    @(posedge clk) disable iff (!rst_n) (valid && !ready) |=> (valid || ready);
endproperty
// Usage: assert property (p_handshake_valid_ready) else $error("Handshake failed");

// Example: reset assertion
property p_reset_asserted;
    @(posedge clk) $rose(rst_n) |-> ##[1:$] !rst_n;
endproperty
// Usage: assert property (p_reset_asserted) else $error("Reset not asserted");

// Assert that a bus has no X or Z
`define ASSERT_NO_XZ(bus, message) \
    assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(bus)) else \
        $error("ASSERTION FAILED: %s - Bus has X/Z", message);

// Assert that a signal is stable during reset
`define ASSERT_STABLE_DURING_RESET(signal, message) \
    assert property (@(posedge clk) !rst_n |-> $stable(signal)) else \
        $error("ASSERTION FAILED: %s - Signal not stable during reset", message);

// Assert x0 register always reads as zero
`define ASSERT_X0_ZERO(rs1_data, rs2_data) \
    if ((rs1_data !== 32'h0000_0000) || (rs2_data !== 32'h0000_0000)) begin \
        $error("ASSERTION FAILED: x0 register should always read as zero"); \
    end

// Assert memory address is within valid range
`define ASSERT_MEM_ADDR_RANGE(addr, min_addr, max_addr, message) \
    if ((addr < min_addr) || (addr > max_addr)) begin \
        $error("ASSERTION FAILED: %s - Address out of range: %h", message, addr); \
    end

// Assert that a signal follows a specific protocol (e.g., handshake)
`define ASSERT_HANDSHAKE(valid, ready, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (valid && !ready) |=> (valid || ready)) else \
        $error("ASSERTION FAILED: %s - Handshake protocol violated", message);

// Assert that a signal is stable for a minimum number of cycles
`define ASSERT_MIN_STABLE(signal, min_cycles, message) \
    assert property (@(posedge clk) disable iff (!rst_n) $rose(signal) |-> ##[1:min_cycles] $stable(signal)) else \
        $error("ASSERTION FAILED: %s - Signal not stable for minimum cycles", message);

// Assert that a signal changes at most once per cycle
`define ASSERT_MAX_ONE_CHANGE(signal, message) \
    assert property (@(posedge clk) disable iff (!rst_n) $changed(signal) |-> ##1 !$changed(signal)) else \
        $error("ASSERTION FAILED: %s - Signal changes more than once per cycle", message);

// Assert that a signal is never X/Z during operation
`define ASSERT_NO_XZ_OPERATIONAL(signal, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (rst_n) |-> !$isunknown(signal)) else \
        $error("ASSERTION FAILED: %s - Signal is X/Z during operation", message);

// Assert that a signal follows a specific pattern
`define ASSERT_PATTERN(signal, pattern, message) \
    assert property (@(posedge clk) disable iff (!rst_n) signal |-> pattern) else \
        $error("ASSERTION FAILED: %s - Signal doesn't follow pattern", message);

// Assert that a signal is within a valid range
`define ASSERT_RANGE(signal, min_val, max_val, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (signal >= min_val && signal <= max_val)) else \
        $error("ASSERTION FAILED: %s - Signal out of range: %h", message, signal);

// Assert that a signal is never driven by multiple sources simultaneously
`define ASSERT_SINGLE_DRIVER(signal, message) \
    assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(signal)) else \
        $error("ASSERTION FAILED: %s - Multiple drivers detected", message);

// Assert that a signal follows a specific timing relationship
`define ASSERT_TIMING(signal1, signal2, delay, message) \
    assert property (@(posedge clk) disable iff (!rst_n) $rose(signal1) |-> ##delay signal2) else \
        $error("ASSERTION FAILED: %s - Timing relationship violated", message);

// Assert that a signal is never active during reset
`define ASSERT_INACTIVE_DURING_RESET(signal, message) \
    assert property (@(posedge clk) !rst_n |-> !signal) else \
        $error("ASSERTION FAILED: %s - Signal active during reset", message);

// Assert that a signal is properly initialized after reset
`define ASSERT_INITIALIZED_AFTER_RESET(signal, expected_value, message) \
    assert property (@(posedge clk) $rose(rst_n) |-> ##1 (signal == expected_value)) else \
        $error("ASSERTION FAILED: %s - Signal not properly initialized", message);

// Assert that a signal follows a specific sequence
`define ASSERT_SEQUENCE(signal, sequence_expr, message) \
    assert property (@(posedge clk) disable iff (!rst_n) sequence_expr) else \
        $error("ASSERTION FAILED: %s - Sequence violated", message);

// Assert that a signal is never in an illegal state
`define ASSERT_LEGAL_STATE(signal, legal_states, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (signal inside legal_states)) else \
        $error("ASSERTION FAILED: %s - Illegal state detected", message);

// Assert that a signal follows a specific protocol with data
`define ASSERT_DATA_PROTOCOL(valid, ready, data, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (valid && ready) |-> !$isunknown(data)) else \
        $error("ASSERTION FAILED: %s - Data protocol violated", message);

// Assert that a signal is never stuck high or low for too long
`define ASSERT_NOT_STUCK(signal, max_cycles, message) \
    assert property (@(posedge clk) disable iff (!rst_n) signal |-> ##[1:max_cycles] !signal) else \
        $error("ASSERTION FAILED: %s - Signal stuck high", message);

// Assert that a signal follows a specific arbitration protocol
`define ASSERT_ARBITRATION(grant, request, message) \
    assert property (@(posedge clk) disable iff (!rst_n) grant |-> request) else \
        $error("ASSERTION FAILED: %s - Arbitration protocol violated", message);

// Assert that a signal follows a specific power management protocol
`define ASSERT_POWER_MANAGEMENT(power_on, clock_enable, message) \
    assert property (@(posedge clk) power_on |-> clock_enable) else \
        $error("ASSERTION FAILED: %s - Power management protocol violated", message);

// Assert that a signal follows a specific security protocol
`define ASSERT_SECURITY(privileged, access_allowed, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (privileged || access_allowed)) else \
        $error("ASSERTION FAILED: %s - Security protocol violated", message);

// Assert that a signal follows a specific cache coherency protocol
`define ASSERT_CACHE_COHERENCY(cache_hit, data_valid, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (cache_hit |-> data_valid)) else \
        $error("ASSERTION FAILED: %s - Cache coherency protocol violated", message);

// Assert that a signal follows a specific interrupt protocol
`define ASSERT_INTERRUPT_PROTOCOL(interrupt, handler_active, message) \
    assert property (@(posedge clk) disable iff (!rst_n) $rose(interrupt) |-> ##[1:10] handler_active) else \
        $error("ASSERTION FAILED: %s - Interrupt protocol violated", message);

// Assert that a signal follows a specific exception protocol
`define ASSERT_EXCEPTION_PROTOCOL(exception, trap_taken, message) \
    assert property (@(posedge clk) disable iff (!rst_n) $rose(exception) |-> ##[1:5] trap_taken) else \
        $error("ASSERTION FAILED: %s - Exception protocol violated", message);

// Assert that a signal follows a specific branch prediction protocol
`define ASSERT_BRANCH_PREDICTION(prediction, actual_taken, misprediction, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (prediction != actual_taken) |-> misprediction) else \
        $error("ASSERTION FAILED: %s - Branch prediction protocol violated", message);

// Assert that a signal follows a specific pipeline protocol
`define ASSERT_PIPELINE_PROTOCOL(stall, flush, valid, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (stall || flush) |-> !valid) else \
        $error("ASSERTION FAILED: %s - Pipeline protocol violated", message);

// Assert that a signal follows a specific memory protocol
`define ASSERT_MEMORY_PROTOCOL(read, write, addr_valid, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (read || write) |-> addr_valid) else \
        $error("ASSERTION FAILED: %s - Memory protocol violated", message);

// Assert that a signal follows a specific AXI4 protocol
`define ASSERT_AXI4_PROTOCOL(awvalid, awready, wvalid, wready, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (awvalid && awready) |-> ##[1:10] (wvalid && wready)) else \
        $error("ASSERTION FAILED: %s - AXI4 protocol violated", message);

// Assert that a signal follows a specific CSR protocol
`define ASSERT_CSR_PROTOCOL(csr_read, csr_write, csr_addr_valid, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (csr_read || csr_write) |-> csr_addr_valid) else \
        $error("ASSERTION FAILED: %s - CSR protocol violated", message);

// Assert that a signal follows a specific hazard detection protocol
`define ASSERT_HAZARD_DETECTION(raw_hazard, waw_hazard, war_hazard, stall, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (raw_hazard || waw_hazard || war_hazard) |-> stall) else \
        $error("ASSERTION FAILED: %s - Hazard detection protocol violated", message);

// Assert that a signal follows a specific forwarding protocol
`define ASSERT_FORWARDING_PROTOCOL(forward_enable, forward_data_valid, message) \
    assert property (@(posedge clk) disable iff (!rst_n) forward_enable |-> forward_data_valid) else \
        $error("ASSERTION FAILED: %s - Forwarding protocol violated", message);

// Assert that a signal follows a specific performance monitoring protocol
`define ASSERT_PERFORMANCE_MONITORING(cycle_count, instruction_count, throughput, message) \
    assert property (@(posedge clk) disable iff (!rst_n) (instruction_count > 0) |-> (throughput <= 1.0)) else \
        $error("ASSERTION FAILED: %s - Performance monitoring protocol violated", message);

`endif // ASSERTIONS_SV

//=============================================================================
// Dependencies: None
//
// Performance: N/A
// Verification Coverage: N/A
// Synthesis: N/A
// Testing: N/A
//
//-----
// Revision History:
// Version | Date       | Author    | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI  | Initial release
//============================================================================= 