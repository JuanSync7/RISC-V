# Cache Coherency

## Overview
This directory contains SystemVerilog modules that implement cache coherency protocols for multi-core RISC-V systems, ensuring data consistency across multiple processor cores and cache levels.

## Purpose
- Maintain cache coherency in multi-core systems
- Implement industry-standard coherency protocols
- Provide scalable coherency solutions
- Support both snoop-based and directory-based protocols

## Contents

### Coherency Modules
- `cache_coherency_controller.sv` - Main coherency controller implementation

## Coherency Protocols

### Supported Protocols
- **MESI Protocol**: Modified, Exclusive, Shared, Invalid
- **MOESI Protocol**: Modified, Owned, Exclusive, Shared, Invalid
- **MSI Protocol**: Modified, Shared, Invalid (simplified)

### Protocol Features
- **Snoop-Based**: Broadcast-based coherency for smaller systems
- **Directory-Based**: Scalable coherency for larger systems
- **Hybrid Approaches**: Combination of snoop and directory methods

## Coherency States

### MESI States
- **Modified (M)**: Cache line is dirty and exclusive
- **Exclusive (E)**: Cache line is clean and exclusive
- **Shared (S)**: Cache line is clean and possibly shared
- **Invalid (I)**: Cache line is not valid

### State Transitions
- Read miss, write miss, and snoop operations
- Invalidation and update propagation
- Writeback and eviction handling
- Replacement policy integration

## System Architecture

### Coherency Infrastructure
- **Snoop Bus**: Broadcast medium for coherency messages
- **Directory**: Centralized or distributed sharing information
- **Coherency Controllers**: Per-cache coherency management
- **Interconnect Integration**: Network-on-chip coherency support

### Message Types
- **Snoop Requests**: Read, write, invalidate
- **Snoop Responses**: Hit, miss, retry
- **Data Transfers**: Cache-to-cache transfers
- **Acknowledgments**: Transaction completion

## Performance Considerations

### Optimization Techniques
- **Silent Drops**: Avoid unnecessary responses
- **Fast Path**: Optimize common cases
- **Pipelining**: Overlap coherency operations
- **Batch Processing**: Group related operations

### Scalability Features
- **Hierarchical Coherency**: Multi-level coherency domains
- **Region-Based**: Coherency at memory region granularity
- **Adaptive Protocols**: Dynamic protocol selection

## Integration Points
- Cache controllers (`rtl/memory/cache/`)
- Memory controllers (`rtl/memory/controllers/`)
- System interconnect
- Multi-core integration (`rtl/core/integration/`)

## Verification Support
- Coherency protocol checkers
- Race condition detection
- Liveness and safety property verification
- Performance monitoring and analysis

## Dependencies
- Cache system implementations
- System interconnect interfaces
- Multi-core system architecture
- Memory interface protocols

---
**Document Version:** 1.0  
**Last Updated:** 2025-07-05  
**Status:** Active 