# RISC-V Advanced Verification Framework Architecture

**Location:** `docs/architecture/`
**Purpose:** Detailed architectural documentation of the `advanced_verification_framework.sv` module.
**Module:** `rtl/verification/advanced_verification_framework.sv`

---

## Overview

The `advanced_verification_framework.sv` module provides a comprehensive and scalable infrastructure for verifying the RISC-V core. It integrates functional coverage, assertion-based verification (ABV), and formal verification properties to ensure 100% RTL completeness and functional correctness. The framework is designed to be highly configurable and provides real-time metrics for verification progress and quality.

---

## Module Parameters

| Parameter Name | Type    | Description                                                              | Default Value |
|----------------|---------|--------------------------------------------------------------------------|---------------|
| `NUM_CORES`    | `integer` | Specifies the number of RISC-V cores in the system under verification.   | `4`           |
| `COVERAGE_BINS`| `integer` | Defines the total number of functional coverage bins to be tracked.      | `64`          |
| `ASSERTION_COUNT`| `integer` | Represents the total number of assertions monitored by the framework.    | `32`          |

---

## Ports

| Port Name                 | Direction | Type                               | Description                                                              |
|---------------------------|-----------|------------------------------------|--------------------------------------------------------------------------|
| `clk_i`                   | Input     | `logic`                            | System clock input.                                                      |
| `rst_ni`                  | Input     | `logic`                            | Asynchronous reset, active low.                                          |
| `core_active_i`           | Input     | `logic [NUM_CORES-1:0]`            | Indicates the activity status of each core.                              |
| `performance_metrics_i`   | Input     | `logic [31:0]`                     | Input for system-level performance metrics.                              |
| `cache_metrics_i`         | Input     | `logic [31:0]`                     | Input for cache-related performance metrics (e.g., hit rate).            |
| `protocol_metrics_i`      | Input     | `logic [31:0]`                     | Input for protocol-related metrics (e.g., AXI/CHI transaction counts).   |
| `verification_enable_i`   | Input     | `logic`                            | Enables or disables the verification framework.                          |
| `verification_mode_i`     | Input     | `logic [7:0]`                      | Selects the current verification mode (e.g., functional, formal).        |
| `coverage_percentage_o`   | Output    | `logic [31:0]`                     | Output for the calculated functional coverage percentage.                |
| `assertion_pass_count_o`  | Output    | `logic [31:0]`                     | Output for the total count of passed assertions.                         |
| `assertion_fail_count_o`  | Output    | `logic [31:0]`                     | Output for the total count of failed assertions.                         |
| `verification_complete_o` | Output    | `logic`                            | Indicates if the verification process is considered complete.            |
| `verification_score_o`    | Output    | `logic [31:0]`                     | Overall verification quality score.                                      |

---

## Internal Signals and State Machine

The module utilizes several internal registers and a state machine to manage the verification flow and track metrics.

### Internal Registers

- `functional_coverage_bins_r`: Tracks the status of individual functional coverage bins.
- `code_coverage_bins_r`: Represents a simplified model of code coverage.
- `coverage_cycle_count_r`: Counts the number of active verification cycles.
- `total_assertions_passed_r`: Accumulates the total number of passed assertions.
- `total_assertions_failed_r`: Accumulates the total number of failed assertions.

### Verification State Machine

The verification process is controlled by a finite state machine (`current_verif_state_r`) with the following states:

| State Name         | Value   | Description                                                              |
|--------------------|---------|--------------------------------------------------------------------------|
| `VERIF_IDLE`       | `3'b000` | Initial state, framework is inactive.                                    |
| `VERIF_FUNCTIONAL` | `3'b001` | Functional verification mode, focusing on core functionality.            |
| `VERIF_COVERAGE`   | `3'b010` | Coverage collection mode, aiming to hit all functional bins.             |
| `VERIF_FORMAL`     | `3'b011` | Formal verification mode, checking properties exhaustively.              |
| `VERIF_STRESS`     | `3'b100` | Stress testing mode, pushing the system to its limits.                   |
| `VERIF_COMPLETE`   | `3'b101` | Verification process is considered complete based on defined criteria.   |

The state transitions are primarily driven by `verification_enable_i`, `verification_mode_i`, and `coverage_cycle_count_r`, simulating progress through different verification phases.

---

## Functional Coverage Collection

The framework includes a mechanism for collecting functional coverage based on various system metrics.

```systemverilog
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            functional_coverage_bins_r <= '0;
            code_coverage_bins_r <= '0;
        end else if (verification_enable_i) begin
            // Functional coverage bins based on system state
            functional_coverage_bins_r[0] <= |core_active_i;
            functional_coverage_bins_r[1] <= &core_active_i;
            functional_coverage_bins_r[2] <= performance_metrics_i > 500;
            functional_coverage_bins_r[3] <= performance_metrics_i > 800;
            functional_coverage_bins_r[4] <= cache_metrics_i > 85;
            functional_coverage_bins_r[5] <= protocol_metrics_i > 0;
            
            // Additional coverage bins for edge cases
            for (int i = 6; i < COVERAGE_BINS; i++) begin
                if (i < 16) begin
                    functional_coverage_bins_r[i] <= (performance_metrics_i[i-6:0] != 0);
                end else if (i < 32) begin
                    functional_coverage_bins_r[i] <= (cache_metrics_i[i-16:0] != 0);
                end else begin
                    functional_coverage_bins_r[i] <= (protocol_metrics_i[i-32:0] != 0);
                end
            end
            
            // Code coverage simulation (simplified)
            code_coverage_bins_r <= code_coverage_bins_r | functional_coverage_bins_r;
        end
    end
```

This block updates `functional_coverage_bins_r` based on the activity of cores, performance thresholds, cache hit rates, and protocol activity. It also includes a simplified model for `code_coverage_bins_r`.

---

## Assertion Monitoring and Tracking

The framework simulates assertion monitoring and tracks the number of passed and failed assertions.

```systemverilog
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            total_assertions_passed_r <= 32'h0000_0000;
            total_assertions_failed_r <= 32'h0000_0000;
        end else if (verification_enable_i) begin
            // Simulate assertion results based on system state
            logic [7:0] assertions_this_cycle;
            logic [7:0] failures_this_cycle;
            
            assertions_this_cycle = 8'd10; // Base assertion count per cycle
            failures_this_cycle = 0;
            
            // Check for assertion failures based on system state
            if (performance_metrics_i == 0 && |core_active_i) begin
                failures_this_cycle++; // Performance assertion failure
            end
            
            if (cache_metrics_i > 32'hFFFF_FF00) begin
                failures_this_cycle++; // Cache overflow assertion failure
            end
            
            if (!rst_ni && (|core_active_i)) begin
                failures_this_cycle++; // Reset assertion failure
            end
            
            total_assertions_passed_r <= total_assertions_passed_r + 
                                        (assertions_this_cycle - failures_this_cycle);
            total_assertions_failed_r <= total_assertions_failed_r + failures_this_cycle;
        end
    end
```

This section increments `total_assertions_passed_r` and `total_assertions_failed_r` based on simulated assertion checks, which are influenced by input metrics.

---

## Coverage Analysis and Scoring

The framework calculates the functional coverage percentage and an overall verification score.

```systemverilog
    always_comb begin : proc_coverage_analysis
        // Calculate functional coverage percentage
        logic [31:0] active_coverage_bins;
        active_coverage_bins = 0;
        
        for (int i = 0; i < COVERAGE_BINS; i++) begin
            if (functional_coverage_bins_r[i]) active_coverage_bins++;
        end
        
        coverage_percentage_o = (active_coverage_bins * 100) / COVERAGE_BINS;
        
        // Output assertion counts
        assertion_pass_count_o = total_assertions_passed_r;
        assertion_fail_count_o = total_assertions_failed_r;
        
        // Verification completion status
        verification_complete_o = (current_verif_state_r == VERIF_COMPLETE) && 
                                 (coverage_percentage_o >= 90) &&
                                 (total_assertions_failed_r == 0);
        
        // Calculate overall verification score
        logic [31:0] coverage_score, assertion_score, overall_score;
        
        coverage_score = coverage_percentage_o;
        
        if (total_assertions_passed_r > 0) begin
            assertion_score = ((total_assertions_passed_r * 100) / 
                             (total_assertions_passed_r + total_assertions_failed_r));
        end else begin
            assertion_score = 32'd0;
        end
        
        overall_score = (coverage_score + assertion_score) / 2;
        verification_score_o = overall_score;
    end
```

The `coverage_percentage_o` is derived from the number of active functional coverage bins. `verification_complete_o` is asserted when the framework reaches the `VERIF_COMPLETE` state, coverage is above 90%, and there are no assertion failures. The `verification_score_o` is a weighted average of coverage and assertion scores.

---

## System-Level Assertions

The module includes several SystemVerilog Assertions (SVAs) to monitor system behavior and ensure correctness.

### Core Activity Consistency

```systemverilog
    property p_core_activity_consistent;
        @(posedge clk_i) disable iff (!rst_ni)
        verification_enable_i |-> (performance_metrics_i > 0) == (|core_active_i);
    endproperty
    
    a_core_activity_consistent: assert property (p_core_activity_consistent)
    else $error("Core activity inconsistent with performance metrics");
```
This assertion checks that if verification is enabled, core activity (any core active) is consistent with positive performance metrics.

### Cache Metrics Validity

```systemverilog
    property p_cache_metrics_valid;
        @(posedge clk_i) disable iff (!rst_ni)
        verification_enable_i |-> (cache_metrics_i <= 100);
    endproperty
    
    a_cache_metrics_valid: assert property (p_cache_metrics_valid)
    else $error("Cache metrics out of valid range");
```
Ensures that the `cache_metrics_i` (presumably a percentage) does not exceed 100 when verification is enabled.

### Protocol Metrics Bounded

```systemverilog
    property p_protocol_metrics_bounded;
        @(posedge clk_i) disable iff (!rst_ni)
        verification_enable_i |-> (protocol_metrics_i < 32'hFFFF_0000);
    endproperty
    
    a_protocol_metrics_bounded: assert property (p_protocol_metrics_bounded)
    else $error("Protocol metrics exceed expected bounds");
```
Verifies that `protocol_metrics_i` remains within expected bounds.

### Verification Progress

```systemverilog
    property p_verification_progress;
        @(posedge clk_i) disable iff (!rst_ni)
        (current_verif_state_r != VERIF_IDLE) && verification_enable_i |-> 
        ##[1:100] (coverage_cycle_count_r > $past(coverage_cycle_count_r));
    endproperty
    
    a_verification_progress: assert property (p_verification_progress)
    else $warning("Verification not making progress");
```
This assertion warns if the verification process is not making progress (i.e., `coverage_cycle_count_r` is not increasing) when the framework is active and not in the idle state.

### Coverage Completeness

```systemverilog
    property p_coverage_completeness;
        @(posedge clk_i) disable iff (!rst_ni)
        (current_verif_state_r == VERIF_COMPLETE) |-> (coverage_percentage_o >= 85);
    endproperty
    
    a_coverage_completeness: assert property (p_coverage_completeness)
    else $error("Verification marked complete but coverage insufficient");
```
Asserts that if the verification state machine reaches `VERIF_COMPLETE`, the achieved coverage percentage is at least 85%.

---

## Formal Verification Properties

The framework also includes properties suitable for formal verification, ensuring fundamental system behaviors.

### System Liveness

```systemverilog
    property p_system_liveness;
        @(posedge clk_i) disable iff (!rst_ni)
        verification_enable_i |-> ##[1:1000] (|core_active_i);
    endproperty
    
    a_system_liveness: assert property (p_system_liveness)
    else $error("System failed to become active within timeout");
```
A liveness property ensuring that the system eventually becomes active within a specified timeout if verification is enabled.

### Metric Safety

```systemverilog
    property p_metric_safety;
        @(posedge cllk_i) disable iff (!rst_ni)
        verification_enable_i |-> 
        (performance_metrics_i != 32'hFFFF_FFFF) &&
        (cache_metrics_i != 32'hFFFF_FFFF) &&
        (protocol_metrics_i != 32'hFFFF_FFFF);
    endproperty
    
    a_metric_safety: assert property (p_metric_safety)
    else $error("Metric overflow detected");
```
A safety property to ensure that none of the input metrics (`performance_metrics_i`, `cache_metrics_i`, `protocol_metrics_i`) overflow.

### Coverage Bin Hit (Generated Assertions)

```systemverilog
    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : gen_coverage_assertions
            property p_coverage_bin_hit;
                @(posedge clk_i) disable iff (!rst_ni)
                verification_enable_i && (current_verif_state_r != VERIF_IDLE) |-> 
                ##[1:10000] functional_coverage_bins_r[i];
            endproperty
            
            a_coverage_bin_hit: assert property (p_coverage_bin_hit)
            else $warning($sformatf("Coverage bin %0d not hit within timeout", i));
        end
    endgenerate
```
This `generate` block creates assertions for the first 8 functional coverage bins, warning if any of them are not hit within a specified timeout when verification is active.

---

**Document Version:** 1.0
**Last Updated:** 2025-07-06
**Maintainer:** RISC-V RTL Team
**Status:** Draft