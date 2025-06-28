# RISC-V Testbench Structure

## Overview

This directory contains the testbench infrastructure for the RISC-V RV32IM core. The testbench structure is designed for comprehensive unit testing of individual modules, with support for integration and system-level testing.

## Directory Structure

```
tb/
├── unit/                          # Unit-level testbenches
│   ├── core/                      # Core pipeline stage tests
│   │   ├── fetch_stage_tb.sv
│   │   ├── decode_stage_tb.sv
│   │   ├── execute_stage_tb.sv
│   │   ├── mem_stage_tb.sv
│   │   └── writeback_stage_tb.sv
│   ├── units/                     # Functional unit tests
│   │   ├── alu_tb.sv
│   │   ├── reg_file_tb.sv
│   │   ├── mult_unit_tb.sv
│   │   ├── div_unit_tb.sv
│   │   ├── csr_regfile_tb.sv
│   │   └── exception_handler_tb.sv
│   ├── control/                   # Control logic tests
│   │   └── hazard_unit_tb.sv
│   ├── memory/                    # Memory system tests
│   │   ├── icache_tb.sv
│   │   ├── memory_wrapper_tb.sv
│   │   └── memory_req_rsp_tb.sv
│   ├── protocols/                 # Protocol adapter tests
│   │   └── axi4_adapter_tb.sv
│   └── prediction/                # Prediction unit tests
│       └── branch_predictor_tb.sv
├── common/                        # Shared testbench utilities
│   ├── test_utils.sv              # Common test functions and tasks
│   ├── test_data.sv               # Test vectors and stimulus data
│   ├── assertions.sv              # Common assertions and properties
│   └── coverage.sv                # Coverage definitions
├── integration/                   # Integration tests (future)
│   ├── pipeline_integration_tb.sv
│   └── memory_integration_tb.sv
├── system/                        # System-level tests (future)
│   └── riscv_core_tb.sv
└── scripts/                       # Test automation scripts
    ├── run_all_tests.py
    ├── run_unit_tests.py
    └── generate_test_report.py
```

## Unit Testbench Template

Each unit testbench follows a standardized structure:

### 1. Header Section
- Company and author information
- File and module names
- Project details
- Tool versions
- Description

### 2. Import and Parameters
```systemverilog
import riscv_core_pkg::*;
import test_utils::*;

// Test configuration
localparam integer NUM_TESTS = 1000;
localparam integer TIMEOUT_CYCLES = 100;
```

### 3. Signal Declarations
```systemverilog
// Clock and reset
logic clk;
logic rst_n;

// DUT interface signals
// ... module-specific signals

// Test control
test_stats_t test_stats;
logic test_done;
```

### 4. DUT Instantiation
```systemverilog
module_name dut (
    .clk_i(clk),
    .rst_n_i(rst_n),
    // ... other connections
);
```

### 5. Clock and Reset Generation
```systemverilog
initial begin
    generate_clock(clk, CLK_PERIOD);
end

initial begin
    generate_reset(rst_n, 5);
end
```

### 6. Test Stimulus
```systemverilog
initial begin
    // Initialize
    test_stats = '0;
    
    // Reset sequence
    generate_reset(rst_n, 5);
    @(posedge clk);
    
    // Run test suite
    run_basic_tests();
    run_edge_case_tests();
    run_random_tests();
    
    // Report results
    report_test_stats(test_stats);
    $finish;
end
```

### 7. Test Functions
```systemverilog
task automatic run_basic_tests();
    $display("Running Basic Tests...");
    test_case_1();
    test_case_2();
    // ...
endtask

task automatic test_case_1();
    string test_name = "Test Case 1";
    
    // Stimulus
    input_signal = test_value;
    @(posedge clk);
    
    // Verification
    `ASSERT_EQ(output_signal, expected_value, "Description");
    
    // Record result
    record_test_result(test_name, TEST_PASS, test_stats);
endtask
```

### 8. Coverage
```systemverilog
covergroup module_cg @(posedge clk);
    signal_cp: coverpoint signal_name {
        bins bin1 = {value1};
        bins bin2 = {value2};
    }
    // Cross coverage
    signal_cross: cross signal1_cp, signal2_cp;
endgroup
```

### 9. Assertions
```systemverilog
property p_signal_check;
    @(posedge clk) condition |-> expected_behavior;
endproperty
assert property (p_signal_check) else
    $error("Assertion failed");
```

## Test Categories

### 1. Basic Functional Tests
- Test normal operation with typical inputs
- Verify expected outputs for standard cases
- Test all supported operations/functions

### 2. Edge Case Tests
- Test boundary conditions
- Test with minimum/maximum values
- Test with zero/null inputs
- Test overflow/underflow conditions

### 3. Random Tests
- Generate random inputs
- Test with unexpected combinations
- Stress testing with high-frequency inputs
- Test corner cases that might be missed

### 4. Error Condition Tests
- Test invalid inputs
- Test error handling
- Test timeout conditions
- Test reset behavior

## Test Utilities

The `test_utils.sv` package provides:

### Common Functions
- `random_word()` - Generate random 32-bit words
- `random_addr()` - Generate random addresses
- `random_reg_addr()` - Generate random register addresses

### Common Tasks
- `generate_clock()` - Generate clock signal
- `generate_reset()` - Generate reset sequence
- `wait_for_signal()` - Wait for signal with timeout
- `record_test_result()` - Record test results
- `report_test_stats()` - Generate test summary

### Assertion Macros
- `ASSERT_EQ()` - Assert equality
- `ASSERT_NEQ()` - Assert inequality
- `ASSERT_TRUE()` - Assert true condition
- `ASSERT_FALSE()` - Assert false condition

### Coverage Macros
- `COVER_POINT()` - Define coverage point
- `COVER_CROSS()` - Define cross coverage

## Running Tests

### Individual Test
```bash
# Compile and run ALU test
vcs -full64 -sverilog -f filelist.f -o alu_tb
./alu_tb
```

### All Unit Tests
```bash
# Run all unit tests
python scripts/run_unit_tests.py
```

### Generate Report
```bash
# Generate test report
python scripts/generate_test_report.py
```

## Test Guidelines

### 1. Test Independence
- Each test should be independent
- Tests should not depend on previous test results
- Use proper initialization and cleanup

### 2. Test Completeness
- Test all functions/operations
- Test all input combinations
- Test error conditions
- Test boundary conditions

### 3. Test Readability
- Use descriptive test names
- Add comments explaining test purpose
- Use meaningful variable names
- Structure tests logically

### 4. Test Maintainability
- Use common utilities and macros
- Follow consistent naming conventions
- Document test requirements
- Keep tests simple and focused

### 5. Test Performance
- Minimize simulation time
- Use efficient test vectors
- Avoid redundant tests
- Use appropriate timeouts

## Coverage Goals

### Code Coverage
- Statement coverage: >95%
- Branch coverage: >90%
- Expression coverage: >85%

### Functional Coverage
- Feature coverage: 100%
- Operation coverage: 100%
- State coverage: >95%

### Error Coverage
- Error condition coverage: 100%
- Exception handling coverage: 100%

## Verification Status

| Module | Unit Tests | Integration Tests | System Tests | Coverage |
|--------|------------|-------------------|--------------|----------|
| ALU | ✅ | ❌ | ❌ | TBD |
| Register File | ❌ | ❌ | ❌ | TBD |
| Memory Wrapper | ❌ | ❌ | ❌ | TBD |
| Branch Predictor | ❌ | ❌ | ❌ | TBD |
| Pipeline Stages | ❌ | ❌ | ❌ | TBD |

## Future Enhancements

1. **Integration Tests**: Test interactions between modules
2. **System Tests**: Full system-level verification
3. **Performance Tests**: Measure timing and throughput
4. **Power Tests**: Measure power consumption
5. **Formal Verification**: Use formal methods for critical paths
6. **Continuous Integration**: Automated test execution
7. **Coverage Analysis**: Automated coverage reporting
8. **Test Generation**: Automated test vector generation

## Dependencies

- SystemVerilog 2012 or later
- VCS, ModelSim, or similar simulator
- Python 3.6+ (for automation scripts)
- RISC-V core package (`riscv_core_pkg.sv`)
- Test utilities package (`test_utils.sv`) 