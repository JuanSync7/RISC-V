# Testbench Scripts

## Overview
This directory contains Python scripts and utilities for running, managing, and analyzing testbenches for the RISC-V processor project. These scripts automate testing workflows and provide comprehensive test execution capabilities.

## Purpose
- Automate testbench execution and management
- Provide comprehensive test suite running capabilities
- Enable regression testing and continuous validation
- Support test result analysis and reporting

## Contents

### Test Execution Scripts
- `run_phase1_tests.py` - Phase 1 integration test execution script
- `run_unit_tests.py` - Unit test execution and management script

## Script Functions

### Test Execution Management
- **Automated Test Running**: Execute tests with minimal manual intervention
- **Test Suite Management**: Organize and run related test groups
- **Parallel Execution**: Run multiple tests concurrently for efficiency
- **Result Aggregation**: Collect and summarize test results

### Regression Testing
- **Nightly Regression**: Automated nightly test runs
- **Commit Validation**: Test validation on code changes
- **Performance Regression**: Track performance metrics over time
- **Coverage Tracking**: Monitor test coverage evolution

## Test Categories

### Phase 1 Tests
- **Core Functionality**: Basic processor core validation
- **Memory System**: Memory subsystem testing
- **Integration**: Component integration validation
- **Performance**: Basic performance benchmarking

### Unit Tests
- **Individual Modules**: Test single RTL modules
- **Component Testing**: Test specific components in isolation
- **Interface Testing**: Validate module interfaces
- **Edge Case Testing**: Test boundary conditions

## Script Features

### Configuration Management
- **Test Configuration**: Flexible test parameter configuration
- **Environment Setup**: Automated test environment preparation
- **Tool Integration**: Integration with simulation tools
- **Result Formatting**: Standardized result reporting

### Analysis and Reporting
- **Pass/Fail Analysis**: Test result categorization
- **Performance Metrics**: Performance data collection and analysis
- **Coverage Reports**: Test coverage analysis and reporting
- **Trend Analysis**: Historical test result trending

## Usage Examples

### Running Phase 1 Tests
```bash
python run_phase1_tests.py --config phase1_config.yaml
python run_phase1_tests.py --verbose --parallel 4
```

### Running Unit Tests
```bash
python run_unit_tests.py --module alu
python run_unit_tests.py --all --coverage
```

### Advanced Options
- **Selective Testing**: Run specific test subsets
- **Debug Mode**: Enhanced debugging output
- **Coverage Collection**: Enable coverage analysis
- **Performance Profiling**: Collect performance metrics

## Integration Points
- CI/CD pipeline integration
- Test result database storage
- Performance monitoring systems
- Coverage analysis tools

## Dependencies
- Python 3.7+ with required packages
- Simulation tools (ModelSim, VCS, etc.)
- Test configuration files
- RTL design files and testbenches

## Configuration
Scripts use YAML configuration files for:
- Test suite definitions
- Tool-specific settings
- Environment parameters
- Reporting preferences

---
**Document Version:** 1.0  
**Last Updated:** 2024-12-19  
**Status:** Active 