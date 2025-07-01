# Cache System

## Overview
This directory contains SystemVerilog modules that implement the hierarchical cache system for the RISC-V processor, including L1, L2, and L3 caches with advanced features like prefetching and Quality of Service (QoS) support.

## Purpose
- Implement multi-level cache hierarchy
- Provide high-performance memory access
- Support cache coherency protocols
- Enable advanced cache optimizations

## Contents

### Cache Modules
- `icache.sv` - L1 instruction cache
- `l2_cache.sv` - L2 unified cache
- `l3_cache.sv` - L3 shared cache
- `matrix_lru.sv` - Matrix-based LRU replacement policy
- `prefetch_unit.sv` - Hardware prefetcher
- `qos_aware_cache.sv` - QoS-integrated cache controller

## Cache Hierarchy

### L1 Caches
- **I-Cache**: Instruction cache with branch prediction integration
- **D-Cache**: Data cache with store buffer and load forwarding
- **Size**: Typically 32KB-64KB per cache
- **Associativity**: 4-way or 8-way set associative

### L2 Cache
- **Unified Cache**: Combined instruction and data
- **Size**: Typically 256KB-1MB
- **Associativity**: 8-way or 16-way set associative
- **Features**: Write-back, allocation on miss

### L3 Cache
- **Shared Cache**: Shared among multiple cores
- **Size**: Typically 2MB-16MB
- **Associativity**: 16-way set associative
- **Features**: Last-level cache with coherency support

## Advanced Features

### Replacement Policies
- **Matrix LRU**: Precise LRU implementation
- **Pseudo-LRU**: Approximated LRU for higher associativity
- **Random**: Simple random replacement
- **FIFO**: First-in-first-out replacement

### Prefetching
- **Stride Prefetcher**: Detects regular access patterns
- **Stream Prefetcher**: Identifies streaming accesses
- **Tagged Prefetcher**: Correlation-based prefetching
- **Adaptive Control**: Dynamic prefetch aggressiveness

### Quality of Service
- **Priority Classes**: Different service levels
- **Bandwidth Allocation**: Guaranteed bandwidth per class
- **Latency Control**: Latency-sensitive traffic prioritization
- **Monitoring**: QoS metrics collection

## Cache Coherency
- Integration with coherency controllers
- Support for MESI/MOESI protocols
- Snoop-based and directory-based coherency
- Invalidation and update propagation

## Performance Optimizations
- **Critical Word First**: Prioritize critical data
- **Non-Blocking Caches**: Multiple outstanding misses
- **Write Combining**: Combine multiple writes
- **Victim Caches**: Reduce conflict misses

## Dependencies
- Memory controllers (`rtl/memory/controllers/`)
- Coherency system (`rtl/memory/coherency/`)
- System interfaces (`rtl/shared/interfaces/`)
- Configuration packages (`rtl/config/`)

---
**Document Version:** 1.0  
**Last Updated:** 2024-12-19  
**Status:** Active 