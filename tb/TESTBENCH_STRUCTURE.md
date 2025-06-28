# RISC-V Testbench Structure Guide

## Overview

This document describes the comprehensive testbench structure designed for unit testing each SystemVerilog file individually in the RISC-V RV32IM core project. The structure is optimized for front-end engineering functional testing with a focus on maintainability, scalability, and comprehensive coverage.

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
│   │   ├── alu_tb.sv             # ✅ Implemented
│   │   ├── reg_file_tb.sv        # ✅ Implemented
│   │   ├── mult_unit_tb.sv       # ❌ TODO
│   │   ├── div_unit_tb.sv        # ❌ TODO
│   │   ├── csr_regfile_tb.sv     # ❌ TODO
│   │   └── exception_handler_tb.sv # ❌ TODO
│   ├── control/                   # Control logic tests
│   │   └── hazard_unit_tb.sv     # ❌ TODO
│   ├── memory/                    # Memory system tests
│   │   ├── icache_tb.sv          # ✅ Existing
│   │   ├── memory_wrapper_tb.sv  # ❌ TODO
│   │   └── memory_req_rsp_tb.sv  # ❌ TODO
│   ├── protocols/                 # Protocol adapter tests
│   │   └── axi4_adapter_tb.sv    # ❌ TODO
│   └── prediction/                # Prediction unit tests
│       └── branch_predictor_tb.sv # ❌ TODO
├── common/                        # Shared testbench utilities
│   ├── test_utils.sv             # ✅ Implemented
│   ├── test_data.sv              # ❌ TODO
│   ├── assertions.sv             # ❌ TODO
│   └── coverage.sv               # ❌ TODO
├── integration/                   # Integration tests (future)
│   ├── pipeline_integration_tb.sv
│   └── memory_integration_tb.sv
├── system/                        # System-level tests (future)
│   └── riscv_core_tb.sv
├── scripts/                       # Test automation scripts
│   ├── run_all_tests.py          # ✅ Implemented
│   ├── run_unit_tests.py         # ✅ Implemented
│   └── generate_test_report.py   # ❌ TODO
├── filelists/                     # Generated filelists
├── Makefile                      # ✅ Implemented
├── README.md                     # ✅ Implemented
└── TESTBENCH_STRUCTURE.md        # This file
```

## Key Components

### 1. Common Test Utilities (`tb/common/test_utils.sv`)

The `test_utils.sv` package provides standardized utilities for all testbenches:

#### Test Configuration
```systemverilog
parameter integer CLK_PERIOD = 10;        // 100MHz clock
parameter integer TIMEOUT_CYCLES = 1000;  // Timeout for tests
parameter integer MAX_TEST_ITERATIONS = 100; // Max iterations for random tests
```

#### Test Status Management
```systemverilog
typedef enum logic [1:0] {
    TEST_PASS = 2'b00,
    TEST_FAIL = 2'b01,
    TEST_TIMEOUT = 2'b10,
    TEST_SKIP = 2'b11
} test_result_e;
```

#### Common Functions
- `random_word()` - Generate random 32-bit words
- `random_addr()` - Generate random addresses
- `random_reg_addr()` - Generate random register addresses
- `generate_clock()` - Generate clock signal
- `generate_reset()` - Generate reset sequence
- `record_test_result()` - Record test results
- `report_test_stats()` - Generate test summary

#### Assertion Macros
```systemverilog
`define ASSERT_EQ(actual, expected, message)
`define ASSERT_NEQ(actual, expected, message)
`define ASSERT_TRUE(condition, message)
`define ASSERT_FALSE(condition, message)
```

### 2. Unit Testbench Template

Each unit testbench follows a standardized structure:

#### Header Section
- Company and author information
- File and module names
- Project details
- Tool versions
- Description

#### Import and Configuration
```systemverilog
import riscv_core_pkg::*;
import test_utils::*;

localparam integer NUM_TESTS = 1000;
localparam integer TIMEOUT_CYCLES = 100;
```

#### Signal Declarations
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

#### Test Organization
```systemverilog
// Main test sequence
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

#### Test Categories
1. **Basic Functional Tests** - Normal operation with typical inputs
2. **Edge Case Tests** - Boundary conditions and extreme values
3. **Random Tests** - Stress testing with random inputs
4. **Error Condition Tests** - Invalid inputs and error handling

### 3. Example: ALU Testbench

The ALU testbench demonstrates the complete structure:

#### Test Functions
```systemverilog
task automatic run_basic_arithmetic_tests();
    test_add_operation();
    test_sub_operation();
    test_slt_operation();
    test_sltu_operation();
endtask

task automatic test_add_operation();
    string test_name = "ADD Operation";
    
    // Stimulus
    operand_a_i = 32'h0000_0001;
    operand_b_i = 32'h0000_0002;
    alu_op_i = ALU_OP_ADD;
    @(posedge clk);
    
    // Verification
    `ASSERT_EQ(result_o, 32'h0000_0003, "ADD: 1 + 2 = 3");
    
    // Record result
    record_test_result(test_name, TEST_PASS, test_stats);
endtask
```

#### Coverage
```systemverilog
covergroup alu_cg @(posedge clk);
    alu_op_cp: coverpoint alu_op_i {
        bins add = {ALU_OP_ADD};
        bins sub = {ALU_OP_SUB};
        // ... other operations
    }
    
    zero_cp: coverpoint zero_o;
    overflow_cp: coverpoint overflow_o;
    
    // Cross coverage
    alu_op_zero_cross: cross alu_op_cp, zero_cp;
endgroup
```

#### Assertions
```systemverilog
property p_zero_flag;
    @(posedge clk) (result_o == 0) |-> zero_o;
endproperty
assert property (p_zero_flag) else
    $error("Zero flag not set when result is zero");
```

## Usage Examples

### 1. Running Individual Tests

#### Using Makefile
```bash
# Run ALU test
make alu_test

# Run Register File test
make reg_test

# Run all tests
make all
```

#### Using Python Script
```bash
# Run all unit tests
python tb/scripts/run_unit_tests.py

# Run specific test
python tb/scripts/run_unit_tests.py --test alu_tb.sv

# Use different simulator
python tb/scripts/run_unit_tests.py --simulator modelsim
```

#### Manual Compilation
```bash
# Compile ALU test
cd tb/unit/units
vcs -full64 -sverilog -f ../../filelists/alu_tb.f -o alu_tb
./alu_tb
```

### 2. Test Development Workflow

1. **Create Testbench Structure**
   ```systemverilog
   module module_name_tb;
       import riscv_core_pkg::*;
       import test_utils::*;
       
       // Signal declarations
       // DUT instantiation
       // Clock generation
       // Test stimulus
       // Test functions
       // Coverage
       // Assertions
   endmodule
   ```

2. **Add Test Functions**
   ```systemverilog
   task automatic run_basic_tests();
       test_case_1();
       test_case_2();
       // ...
   endtask
   
   task automatic test_case_1();
       string test_name = "Test Case 1";
       // Stimulus and verification
       record_test_result(test_name, TEST_PASS, test_stats);
   endtask
   ```

3. **Add Coverage**
   ```systemverilog
   covergroup module_cg @(posedge clk);
       // Define coverage points
   endgroup
   ```

4. **Add Assertions**
   ```systemverilog
   property p_signal_check;
       @(posedge clk) condition |-> expected_behavior;
   endproperty
   assert property (p_signal_check) else
       $error("Assertion failed");
   ```

### 3. Test Categories and Guidelines

#### Basic Functional Tests
- Test normal operation with typical inputs
- Verify expected outputs for standard cases
- Test all supported operations/functions
- Use meaningful test names and descriptions

#### Edge Case Tests
- Test boundary conditions (min/max values)
- Test with zero/null inputs
- Test overflow/underflow conditions
- Test reset behavior

#### Random Tests
- Generate random inputs using utility functions
- Test with unexpected combinations
- Stress testing with high-frequency inputs
- Test corner cases that might be missed

#### Error Condition Tests
- Test invalid inputs
- Test error handling mechanisms
- Test timeout conditions
- Test exception handling

## Best Practices

### 1. Test Independence
- Each test should be independent
- Tests should not depend on previous test results
- Use proper initialization and cleanup
- Reset state between tests if needed

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

## Future Enhancements

### 1. Integration Tests
- Test interactions between modules
- Pipeline stage integration
- Memory system integration
- Control signal integration

### 2. System Tests
- Full system-level verification
- End-to-end instruction execution
- Performance benchmarking
- Power analysis

### 3. Advanced Features
- Formal verification integration
- Coverage-driven test generation
- Continuous integration setup
- Automated regression testing

### 4. Documentation
- Test plan generation
- Coverage report generation
- Test result analysis
- Performance metrics

## Dependencies

- SystemVerilog 2012 or later
- VCS, ModelSim, or similar simulator
- Python 3.6+ (for automation scripts)
- RISC-V core package (`riscv_core_pkg.sv`)
- Test utilities package (`test_utils.sv`)

## Conclusion

This testbench structure provides a solid foundation for comprehensive unit testing of the RISC-V RV32IM core. The standardized approach ensures consistency across all testbenches while providing the flexibility needed for different module types. The automation tools and utilities make it easy to develop, run, and maintain tests as the project evolves.

The structure is designed to scale from individual unit tests to integration and system-level testing, supporting the complete verification lifecycle of the RISC-V core project. 