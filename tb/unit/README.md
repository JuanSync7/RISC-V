# Unit Testbenches

## Overview
This directory contains unit-level testbenches for individual components and modules of the RISC-V processor, organized by functional categories. These testbenches provide detailed validation of specific components in isolation.

## Purpose
- Validate individual RTL modules and components
- Provide focused testing for specific functionality
- Enable rapid debugging and development iteration
- Support component-level verification and validation

## Directory Structure

### Core Components (`core/`)
- `decode_stage_tb.sv` - Decode stage testbench ([Test Cases](decode_stage_tb_testcases.md))
- `execute_stage_tb.sv` - Execute stage testbench ([Test Cases](execute_stage_tb_testcases.md))
- `mem_stage_tb.sv` - Memory stage testbench ([Test Cases](mem_stage_tb_testcases.md))
- `writeback_stage_tb.sv` - Writeback stage testbench ([Test Cases](writeback_stage_tb_testcases.md))
- `system_integration_validator_tb.sv` - System integration validation testbench

### Execution Components (`execution/`)
- `reorder_buffer_tb.sv` - Reorder buffer functionality testbench

### Functional Units (`units/`)
- `alu_tb.sv` - ALU (Arithmetic Logic Unit) testbench
- `branch_predictor_tb.sv` - Branch predictor validation testbench
- `csr_regfile_tb.sv` - CSR register file testbench
- `div_unit_tb.sv` - Division unit testbench
- `exception_handler_tb.sv` - Exception handler testbench
- `mult_unit_tb.sv` - Multiplication unit testbench
- `reg_file_tb.sv` - Register file testbench
- `fpu_tb.sv` - Floating Point Unit testbench ([Test Cases](fpu_tb_testcases.md))
- `vpu_tb.sv` - Vector Processing Unit testbench ([Test Cases](vpu_tb_testcases.md))
- `mliu_tb.sv` - Machine Learning Inference Unit testbench ([Test Cases](mliu_tb_testcases.md))

## Testing Categories

### Arithmetic and Logic Units
- **ALU Testing**: Comprehensive arithmetic and logic operation validation
- **Multiplication Unit**: Integer multiplication testing with various operands
- **Division Unit**: Integer division and remainder operation testing
- **Data Path Validation**: Verify data flow and result accuracy

### Control and Prediction
- **Branch Predictor**: Prediction accuracy and algorithm validation
- **Exception Handler**: Exception detection and handling testing
- **System Validation**: Integration and control flow testing

### Storage and Registers
- **Register File**: Register read/write operations and bypass testing
- **CSR Register File**: Control and Status Register functionality
- **Reorder Buffer**: Out-of-order execution support testing

## Unit Test Features

### Comprehensive Coverage
- **Functional Coverage**: All operations and modes tested
- **Corner Cases**: Boundary conditions and edge cases
- **Error Conditions**: Invalid operations and error handling
- **Performance Validation**: Timing and latency requirements

### Test Methodologies
- **Directed Testing**: Specific test scenarios for known requirements
- **Random Testing**: Pseudo-random stimulus for broader coverage
- **Constraint-Based**: Constrained random testing for valid scenarios
- **Regression Testing**: Automated test suite execution

### Verification Infrastructure
- **Self-Checking**: Automated result verification
- **Reference Models**: Golden reference comparison
- **Assertion-Based**: SystemVerilog assertions for property checking
- **Coverage Metrics**: Code and functional coverage tracking

## Individual Component Testing

### ALU Testbench
- All arithmetic operations (add, subtract, etc.)
- Logic operations (AND, OR, XOR, etc.)
- Shift operations (logical and arithmetic)
- Comparison operations

### Branch Predictor Testbench
- Prediction algorithm validation
- Training and adaptation testing
- Accuracy measurement and analysis
- Performance impact assessment

### Register File Testbench
- Simultaneous read/write operations
- Register bypass and forwarding
- Multi-port access validation
- Data integrity verification

## Integration with System Testing
- Component test results feed into integration testing
- Interface compliance verification for system integration
- Performance characteristics inform system-level optimization
- Error handling validation supports system reliability

## Dependencies
- Individual RTL modules under test
- Common verification infrastructure (`tb/common/`)
- Shared packages and interfaces (`rtl/shared/`)
- Test utilities and frameworks

## Usage
Run individual unit tests:
```bash
make test_alu
make test_branch_predictor
make test_reg_file
make test_all_units
```

---
**Document Version:** 1.0  
**Last Updated:** 2025-07-05  
**Status:** Active 