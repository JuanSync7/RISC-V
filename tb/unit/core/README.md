# Core Unit Testbenches

## Overview
This directory contains unit testbenches specifically for core-level components of the RISC-V processor, focusing on system integration validation and core control functionality.

## Purpose
- Validate core-level integration components
- Test system integration validation functionality
- Verify core subsystem coordination
- Ensure proper core-level control and management

## Contents

### Core Testbench Files
- `system_integration_validator_tb.sv` - System integration validation testbench

## Testing Focus

### System Integration Validation
- **Component Integration**: Validate integration between core components
- **Interface Compliance**: Verify interface protocol compliance
- **Control Flow Validation**: Test control signal propagation and timing
- **Error Detection**: Validate error detection and reporting mechanisms

### Core Subsystem Testing
- **Pipeline Coordination**: Test coordination between pipeline stages
- **Execution Engine Integration**: Validate out-of-order execution integration
- **Memory Interface**: Test core-to-memory system interfaces
- **Performance Monitoring**: Validate performance counter integration

## Validation Scenarios

### Integration Testing
- **Multi-Component Interaction**: Test interaction between multiple core components
- **Data Flow Validation**: Verify data flow through core subsystems
- **Control Signal Testing**: Validate control signal generation and propagation
- **Exception Handling**: Test exception detection and handling integration

### Performance Validation
- **Throughput Testing**: Measure and validate instruction throughput
- **Latency Analysis**: Characterize and validate operation latencies
- **Resource Utilization**: Monitor and validate resource usage
- **Performance Counter Accuracy**: Verify performance monitoring accuracy

### Error and Corner Cases
- **Error Injection**: Test error detection and recovery mechanisms
- **Boundary Conditions**: Test system behavior at operational limits
- **Stress Testing**: Validate system behavior under high load
- **Recovery Testing**: Test system recovery from error conditions

## Test Infrastructure

### Validation Framework
- **Automated Checking**: Comprehensive automated result validation
- **Reference Models**: Golden reference comparison for validation
- **Assertion-Based**: SystemVerilog assertions for property checking
- **Coverage Tracking**: Functional and code coverage measurement

### System Monitoring
- **Performance Monitoring**: Real-time performance metric collection
- **Interface Monitoring**: Monitor interface transactions and compliance
- **Error Logging**: Comprehensive error detection and logging
- **Debug Support**: Enhanced debugging and visibility features

## Integration with System
- Interfaces with pipeline stage testbenches
- Coordinates with execution engine testing
- Integrates with memory system validation
- Supports full system integration testing

## Dependencies
- Core integration modules (`rtl/core/integration/`)
- System validation components
- Common verification infrastructure (`tb/common/`)
- Core subsystem interfaces and packages

## Usage
Execute core unit tests:
```bash
make test_system_integration_validator
make test_core_integration
make test_core_validation
```

---
**Document Version:** 1.0  
**Last Updated:** 2024-12-19  
**Status:** Active 