# Functional Unit Testbenches

## Overview
This directory contains unit testbenches for individual functional units of the RISC-V processor, including arithmetic, logic, control, and specialized processing units. These testbenches provide comprehensive validation of basic processor building blocks.

## Purpose
- Validate individual functional unit implementations
- Test arithmetic and logic operations comprehensively
- Verify control and status register functionality
- Ensure proper exception handling and branch prediction

## Contents

### Functional Unit Testbench Files
- `alu_tb.sv` - Arithmetic Logic Unit comprehensive testbench
- `branch_predictor_tb.sv` - Branch predictor algorithm validation testbench
- `csr_regfile_tb.sv` - Control and Status Register file testbench
- `div_unit_tb.sv` - Division unit implementation testbench
- `exception_handler_tb.sv` - Exception handling mechanism testbench
- `mult_unit_tb.sv` - Multiplication unit implementation testbench
- `reg_file_tb.sv` - General-purpose register file testbench

## Testing Categories

### Arithmetic Units
- **ALU Testing**: All arithmetic and logic operations
- **Multiplication Unit**: Integer multiplication with various bit-widths
- **Division Unit**: Integer division and remainder operations
- **Result Accuracy**: Verify mathematical correctness

### Control and Prediction Units
- **Branch Predictor**: Prediction algorithm accuracy and adaptation
- **Exception Handler**: Exception detection, prioritization, and handling
- **CSR Register File**: Control and status register access and functionality

### Storage Units
- **Register File**: General-purpose register read/write operations
- **Multi-Port Access**: Simultaneous register access validation
- **Data Integrity**: Register data consistency and correctness

## Individual Unit Testing

### ALU Testbench (`alu_tb.sv`)
- **Arithmetic Operations**: Add, subtract, compare operations
- **Logic Operations**: AND, OR, XOR, NOT operations
- **Shift Operations**: Logical and arithmetic shifts
- **Flag Generation**: Condition code and flag validation

### Multiplication Unit (`mult_unit_tb.sv`)
- **Signed/Unsigned Multiplication**: Various multiplication modes
- **Bit-Width Testing**: Different operand sizes
- **Corner Cases**: Zero, maximum, and minimum value testing
- **Performance Validation**: Timing and throughput characteristics

### Division Unit (`div_unit_tb.sv`)
- **Division Operations**: Quotient and remainder calculation
- **Signed/Unsigned Division**: Different division modes
- **Error Conditions**: Division by zero and overflow handling
- **Algorithm Validation**: Division algorithm correctness

### Branch Predictor (`branch_predictor_tb.sv`)
- **Prediction Algorithms**: Bimodal, two-level, tournament predictors
- **Training and Adaptation**: Predictor learning validation
- **Accuracy Measurement**: Prediction accuracy characterization
- **Performance Impact**: Predictor performance evaluation

### Register File (`reg_file_tb.sv`)
- **Read/Write Operations**: Register access functionality
- **Bypass Testing**: Register forwarding and bypass logic
- **Multi-Port Access**: Concurrent register access validation
- **Reset and Initialization**: Register initialization testing

### CSR Register File (`csr_regfile_tb.sv`)
- **CSR Access**: Control and status register read/write
- **Privilege Levels**: Access control based on privilege mode
- **Exception Integration**: CSR updates during exception handling
- **Performance Counters**: Performance counter functionality

### Exception Handler (`exception_handler_tb.sv`)
- **Exception Detection**: Various exception condition detection
- **Priority Resolution**: Exception prioritization and handling
- **State Preservation**: Processor state saving and restoration
- **Recovery Testing**: Exception recovery and resumption

## Verification Methodology

### Test Coverage
- **Functional Coverage**: All operations and modes covered
- **Code Coverage**: Statement, branch, and condition coverage
- **Corner Case Testing**: Boundary conditions and edge cases
- **Error Injection**: Error condition testing and validation

### Validation Techniques
- **Self-Checking Tests**: Automated result verification
- **Reference Model**: Golden reference comparison
- **Assertion-Based**: SystemVerilog assertions for property checking
- **Randomized Testing**: Constrained random test generation

## Performance Testing
- **Latency Measurement**: Operation completion time
- **Throughput Analysis**: Operations per cycle capability
- **Resource Utilization**: Internal resource usage
- **Power Analysis**: Power consumption characteristics

## Dependencies
- Functional unit RTL (`rtl/units/`)
- Core packages and interfaces (`rtl/shared/`)
- Common verification infrastructure (`tb/common/`)
- Test utilities and reference models

## Usage
Execute functional unit tests:
```bash
make test_alu
make test_mult_unit
make test_div_unit
make test_branch_predictor
make test_reg_file
make test_csr_regfile
make test_exception_handler
make test_all_units
```

---
**Document Version:** 1.0  
**Last Updated:** 2024-12-19  
**Status:** Active 