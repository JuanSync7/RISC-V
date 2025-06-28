# Common Testbench Utilities

## Overview

This directory contains shared utilities, interfaces, and components used across all testbenches in the RISC-V verification framework. These components provide a standardized approach to testbench development and ensure consistency across the verification environment.

## Files

| File | Description | Status |
|------|-------------|--------|
| `test_utils.sv` | Core test utilities and macros | ✅ Complete |
| `test_data.sv` | Test vector generation | ✅ Complete |
| `assertions.sv` | Common assertions and properties | ✅ Complete |
| `coverage.sv` | Coverage definitions | ✅ Complete |
| `test_env.sv` | Verification environment | ✅ Complete |
| `driver.sv` | Test stimulus driver | ✅ Complete |
| `monitor.sv` | Signal monitoring | ✅ Complete |
| `scoreboard.sv` | Result checking | ✅ Complete |
| `checker.sv` | Protocol checking | ✅ Complete |
| `verification_plan.sv` | Verification plan definition | ✅ Complete |
| `VERIFICATION_FRAMEWORK.md` | Framework documentation | ✅ Complete |

## Core Components

### Test Utilities (`test_utils.sv`)
The core utilities package provides standardized functions and macros for all testbenches.

#### Key Features
- **Test Configuration**: Clock generation, reset sequences, timeouts
- **Random Generation**: Random data, addresses, register values
- **Test Management**: Result recording, statistics reporting
- **Assertion Macros**: Standardized assertion functions
- **Utility Functions**: Common helper functions

#### Usage Example
```systemverilog
import test_utils::*;

// Generate clock and reset
generate_clock(clk, CLK_PERIOD);
generate_reset(rst_n, 5);

// Generate random test data
logic [31:0] random_data = random_word();
logic [31:0] random_addr = random_addr();

// Record test results
record_test_result("Test Name", TEST_PASS, test_stats);
```

### Test Data Generation (`test_data.sv`)
Provides test vectors and stimulus data for comprehensive testing.

#### Features
- **Instruction Vectors**: RISC-V instruction test vectors
- **Data Patterns**: Common data patterns for testing
- **Edge Cases**: Boundary condition test data
- **Random Sequences**: Constrained random test data

#### Usage Example
```systemverilog
import test_data::*;

// Get test instruction
logic [31:0] test_instruction = get_add_instruction(5, 10, 15);

// Get edge case data
logic [31:0] max_value = get_max_32bit_value();
logic [31:0] zero_value = get_zero_value();
```

### Assertions (`assertions.sv`)
Common assertions and properties for protocol and functional verification.

#### Features
- **Protocol Assertions**: Memory interface, bus protocol
- **Functional Assertions**: ALU operations, register behavior
- **Timing Assertions**: Clock domain, setup/hold timing
- **Coverage Properties**: Functional coverage properties

#### Usage Example
```systemverilog
import assertions::*;

// Protocol assertion
property p_memory_request;
    @(posedge clk) disable iff (!rst_n)
    mem_req_o |-> ##[1:3] mem_rvalid_i;
endproperty
assert property (p_memory_request) else
    $error("Memory request timeout");

// Functional assertion
`ASSERT_EQ(alu_result, expected_result, "ALU result mismatch");
```

### Coverage (`coverage.sv`)
Coverage definitions and collection utilities.

#### Features
- **Code Coverage**: Statement, branch, expression coverage
- **Functional Coverage**: Feature, operation, state coverage
- **Cross Coverage**: Multi-dimensional coverage
- **Coverage Reporting**: Automated coverage reporting

#### Usage Example
```systemverilog
import coverage::*;

// Define coverage group
covergroup alu_cg @(posedge clk);
    alu_op_cp: coverpoint alu_op_i {
        bins add = {ALU_OP_ADD};
        bins sub = {ALU_OP_SUB};
        bins slt = {ALU_OP_SLT};
    }
    zero_cp: coverpoint zero_o;
    alu_op_zero_cross: cross alu_op_cp, zero_cp;
endgroup
```

### Verification Environment (`test_env.sv`)
Standardized verification environment for testbench development.

#### Components
- **Driver**: Generates test stimulus and controls test flow
- **Monitor**: Observes DUT behavior and captures signals
- **Scoreboard**: Compares expected vs actual results
- **Checker**: Validates protocol compliance and timing
- **Coverage**: Tracks functional and code coverage

#### Usage Example
```systemverilog
import test_env::*;

// Create test environment
test_env env;

// Configure environment
test_config_t config;
config.num_tests = 1000;
config.timeout_cycles = 1000;
env = new(config);

// Run test
env.run();
env.report();
```

## Test Framework Features

### Standardized Test Structure
Each testbench follows a consistent template:
- **Header Section**: File information and description
- **Configuration**: Test parameters and constants
- **Signal Declaration**: Clock, reset, and DUT interfaces
- **Test Organization**: Basic, edge case, random, and error tests
- **Coverage**: Functional and code coverage definitions
- **Assertions**: Property-based verification

### Test Categories
1. **Basic Functional Tests**: Normal operation with typical inputs
2. **Edge Case Tests**: Boundary conditions and extreme values
3. **Random Tests**: Stress testing with random inputs
4. **Error Condition Tests**: Invalid inputs and error handling

### Assertion Macros
```systemverilog
// Equality assertion
`ASSERT_EQ(actual, expected, message)

// Inequality assertion
`ASSERT_NEQ(actual, expected, message)

// Boolean assertions
`ASSERT_TRUE(condition, message)
`ASSERT_FALSE(condition, message)
```

### Coverage Macros
```systemverilog
// Coverage point
`COVER_POINT(signal, bins)

// Cross coverage
`COVER_CROSS(signal1, signal2)
```

## Usage Guidelines

### Test Development
1. **Import Utilities**: Import required packages
2. **Configure Test**: Set up test parameters
3. **Generate Stimulus**: Use utility functions for test data
4. **Apply Stimulus**: Drive DUT inputs
5. **Verify Results**: Use assertions and scoreboard
6. **Record Results**: Track test statistics
7. **Generate Coverage**: Collect coverage data

### Best Practices
- **Test Independence**: Each test should be independent
- **Comprehensive Coverage**: Test all functions and edge cases
- **Readable Tests**: Use descriptive names and comments
- **Maintainable Code**: Use common utilities and macros
- **Performance**: Optimize test execution time

### Error Handling
- **Timeout Detection**: Use timeout mechanisms
- **Error Reporting**: Provide clear error messages
- **Recovery**: Implement error recovery mechanisms
- **Debugging**: Include debug information

## Performance Considerations

### Test Execution
- **Parallel Execution**: Support for parallel test execution
- **Resource Management**: Efficient memory and CPU usage
- **Timeout Management**: Appropriate timeout values
- **Coverage Optimization**: Efficient coverage collection

### Memory Usage
- **Test Data**: Efficient test data generation
- **Waveform Storage**: Configurable waveform storage
- **Coverage Data**: Optimized coverage data structures

## Future Enhancements

### Phase 1: Framework Improvements
1. **Advanced Coverage**: More sophisticated coverage models
2. **Performance Optimization**: Faster test execution
3. **Debug Support**: Enhanced debugging capabilities

### Phase 2: Advanced Features
1. **Formal Verification**: Integration with formal tools
2. **Coverage-Driven Testing**: Automated test generation
3. **Continuous Integration**: CI/CD integration

### Phase 3: System Integration
1. **Multi-Core Testing**: Support for multi-core verification
2. **Power Verification**: Power-aware testing
3. **Security Testing**: Security-focused verification

## Dependencies

### Internal Dependencies
- `riscv_core_pkg.sv`: Core package definitions
- SystemVerilog interfaces for communication

### External Dependencies
- SystemVerilog 2012 or later
- VCS, ModelSim, or similar simulator
- Python 3.6+ (for automation scripts)

## Contributing

When adding new utilities:

1. Follow the established naming conventions
2. Include comprehensive documentation
3. Add appropriate error handling
4. Create corresponding tests
5. Update this README with new utility information
6. Ensure backward compatibility

## Support

For questions or issues:
1. Check the utility documentation
2. Review existing usage examples
3. Consult the verification framework documentation
4. Check the testbench examples 