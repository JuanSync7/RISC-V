# Memory Wrappers

## Overview
This directory contains SystemVerilog modules that provide memory interface wrappers and adapters for the RISC-V processor system, including standard memory interfaces and QoS-aware memory wrappers.

## Purpose
- Provide standardized memory interfaces
- Abstract memory system complexity from cores
- Implement QoS-aware memory access
- Enable flexible memory system configuration

## Contents

### Memory Wrapper Modules
- `memory_wrapper.sv` - Standard memory interface wrapper
- `qos_memory_wrapper.sv` - QoS-aware memory interface wrapper

## Wrapper Functions

### Standard Memory Wrapper
- **Interface Standardization**: Provide consistent memory interface
- **Protocol Translation**: Convert between different memory protocols
- **Request Buffering**: Buffer memory requests and responses
- **Error Handling**: Detect and handle memory errors

### QoS Memory Wrapper
- **Quality of Service**: Implement QoS policies for memory access
- **Priority Management**: Manage request priorities and classes
- **Bandwidth Allocation**: Allocate memory bandwidth per service class
- **Latency Control**: Control and guarantee memory latencies

## Interface Abstraction

### Core-Facing Interface
- **Simplified Interface**: Easy-to-use memory interface for cores
- **Request/Response Model**: Simple request-response protocol
- **Burst Support**: Support for burst transactions
- **Atomic Operations**: Support for atomic memory operations

### Memory-Facing Interface
- **Protocol Adaptation**: Adapt to specific memory protocols
- **Timing Optimization**: Optimize memory access timing
- **Error Correction**: Integrate with memory error correction
- **Performance Monitoring**: Monitor memory performance metrics

## QoS Features

### Service Classes
- **Real-Time**: Guaranteed latency and bandwidth
- **High Priority**: Preferential treatment
- **Best Effort**: Standard service level
- **Background**: Low priority, background tasks

### QoS Policies
- **Strict Priority**: Absolute priority ordering
- **Weighted Fair Queuing**: Proportional bandwidth sharing
- **Deadline Scheduling**: Meet timing deadlines
- **Adaptive Policies**: Dynamic policy adjustment

## System Integration

### Memory System Architecture
```
Cores → Memory Wrappers → Memory Controllers → Physical Memory
         ↓
    QoS Policies
    Priority Queues
    Bandwidth Control
```

### Configuration Options
- **QoS Policy Selection**: Choose appropriate QoS policies
- **Buffer Sizes**: Configure request and response buffers
- **Timeout Values**: Set transaction timeout values
- **Error Handling**: Configure error detection and recovery

## Performance Features
- **Request Pipelining**: Pipeline memory requests
- **Response Buffering**: Buffer responses for improved throughput
- **Burst Optimization**: Optimize burst transaction handling
- **Latency Hiding**: Hide memory latency through buffering

## Dependencies
- Memory controllers (`rtl/memory/controllers/`)
- System interfaces (`rtl/shared/interfaces/`)
- QoS packages (`rtl/shared/packages/`)
- Protocol adapters (`rtl/protocol/`)

## Debug and Monitoring
- Memory access tracing
- QoS performance monitoring
- Error logging and reporting
- System-level visibility

---

**Document Version:** 1.0  
**Last Updated:** 2025-07-05  
**Maintainer:** RISC-V RTL Team  
**Status:** Active