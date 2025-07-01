# Memory System Testbenches

## Overview
This directory contains SystemVerilog testbenches specifically designed for testing the memory subsystem components of the RISC-V processor, including memory interfaces, wrappers, and request-response protocols.

## Purpose
- Validate memory subsystem functionality
- Test memory interface protocols
- Verify memory wrapper implementations
- Ensure memory system performance

## Contents

### Memory Testbench Files
- `memory_req_rsp_tb.sv` - Memory request-response interface testbench
- `memory_wrapper_tb.sv` - Memory wrapper functionality testbench

## Testing Focus

### Memory Interface Testing
- **Request-Response Protocol**: Validate memory transaction protocols
- **Interface Compliance**: Ensure standard interface compliance
- **Data Integrity**: Verify data correctness through memory operations
- **Timing Validation**: Check timing requirements and constraints

### Memory Wrapper Testing
- **Wrapper Functionality**: Test memory wrapper operations
- **QoS Features**: Validate Quality of Service implementations
- **Protocol Translation**: Test protocol conversion capabilities
- **Error Handling**: Verify error detection and recovery

## Test Scenarios

### Basic Functionality
- **Read Operations**: Single and burst read transactions
- **Write Operations**: Single and burst write transactions
- **Mixed Operations**: Interleaved read and write operations
- **Address Testing**: Various address patterns and ranges

### Advanced Features
- **QoS Testing**: Priority-based request handling
- **Burst Transactions**: Multi-beat burst operations
- **Atomic Operations**: Atomic read-modify-write operations
- **Cache Interactions**: Cache-coherent memory operations

### Performance Testing
- **Bandwidth Testing**: Memory bandwidth utilization
- **Latency Measurement**: Memory access latency characterization
- **Throughput Analysis**: Transaction throughput validation
- **QoS Performance**: Service level compliance testing

### Error Scenarios
- **Invalid Transactions**: Test error detection capabilities
- **Timeout Handling**: Verify timeout mechanisms
- **Protocol Violations**: Test protocol error handling
- **Recovery Testing**: Error recovery and retry mechanisms

## Verification Features

### Test Generation
- **Random Stimulus**: Pseudo-random test generation
- **Directed Tests**: Specific scenario testing
- **Coverage-Driven**: Coverage-guided test generation
- **Constraint-Based**: Constrained random testing

### Checking and Monitoring
- **Protocol Checkers**: Automated protocol compliance checking
- **Data Checking**: End-to-end data integrity verification
- **Performance Monitoring**: Real-time performance metrics
- **Coverage Collection**: Functional and code coverage tracking

## Integration with System
- Interface with cache system testbenches
- Integration with core memory interface testing
- Coordination with system-level memory testing
- Support for multi-level memory hierarchy testing

## Dependencies
- Memory system RTL (`rtl/memory/`)
- Common verification framework (`tb/common/`)
- System interfaces (`rtl/shared/interfaces/`)
- Memory packages (`rtl/shared/packages/`)

## Usage
Execute memory tests using the simulation framework:
```bash
make memory_test
make memory_wrapper_test
make memory_req_rsp_test
```

---
**Document Version:** 1.0  
**Last Updated:** 2024-12-19  
**Status:** Active 