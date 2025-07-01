# Branch Prediction

## Overview
This directory contains SystemVerilog modules that implement advanced branch prediction mechanisms for the RISC-V processor, including multiple prediction algorithms and return address prediction.

## Purpose
- Implement high-accuracy branch prediction
- Minimize pipeline stalls from control hazards
- Support speculative execution
- Provide multiple prediction algorithm options

## Contents

### Branch Prediction Modules
- `branch_predictor.sv` - Main branch predictor with multiple algorithm support
- `return_stack_buffer.sv` - Return address stack for function calls
- `tournament_predictor.sv` - Tournament predictor combining multiple algorithms

## Prediction Algorithms

### Supported Predictors
- **Bimodal Predictor**: Simple 2-bit saturating counter
- **Two-Level Adaptive**: Global and local history predictors
- **Tournament Predictor**: Meta-predictor choosing between algorithms
- **Return Stack Buffer**: Dedicated return address prediction

### Advanced Features
- **Branch Target Buffer (BTB)**: Branch target address caching
- **Pattern History Table**: Branch pattern learning
- **Global History Register**: Global branch correlation
- **Confidence Estimation**: Prediction confidence tracking

## Architecture
```
Branch Prediction System
├── Branch Target Buffer (BTB)
├── Pattern History Table (PHT)
├── Global History Register (GHR)
├── Tournament Meta-Predictor
└── Return Stack Buffer (RSB)
```

### Prediction Flow
1. **Address Lookup**: Check BTB for branch target
2. **Direction Prediction**: Predict taken/not-taken
3. **Target Prediction**: Predict branch target address
4. **Return Prediction**: Special handling for function returns
5. **Confidence Assessment**: Evaluate prediction confidence

## Performance Metrics
- Branch prediction accuracy (target: >95%)
- Misprediction penalty reduction
- Speculative execution enablement
- Pipeline throughput improvement

## Integration Points
- Fetch stage integration for instruction address prediction
- Execution stage feedback for predictor updates
- Exception handling for misprediction recovery
- Performance monitoring integration

## Configuration
Prediction algorithms are configurable through:
- Predictor table sizes
- History register lengths
- Tournament predictor weights
- Return stack depth

## Dependencies
- Pipeline fetch stage (`rtl/core/pipeline/`)
- Control logic (`rtl/core/control/`)
- Configuration packages (`rtl/config/`)
- Performance monitoring system

---
**Document Version:** 1.0  
**Last Updated:** 2024-12-19  
**Status:** Active 