# RISC-V Multi-Core QoS Implementation Guide

## Overview

This document describes the Quality of Service (QoS) implementation for the RISC-V multi-core system. The QoS system ensures critical transactions receive appropriate priority while preventing starvation of lower-priority traffic.

## QoS Architecture

### 1. QoS Levels (0-15)

| Level | Name | Priority | Usage |
|-------|------|----------|-------|
| 15 (0xF) | CRITICAL | Highest | Debug, Exception handling |
| 12 (0xC) | HIGH | High | CPU instruction fetch |
| 8 (0x8) | MEDIUM_HIGH | Medium-High | CPU data access |
| 6 (0x6) | MEDIUM | Medium | L2 cache operations |
| 4 (0x4) | MEDIUM_LOW | Medium-Low | L3 cache operations |
| 2 (0x2) | LOW | Low | Background operations |
| 1 (0x1) | BEST_EFFORT | Lowest | DMA, peripheral access |
| 0 (0x0) | NONE | No QoS | Legacy compatibility |

### 2. Transaction Types

- **QOS_TYPE_DEBUG**: Debug access (Critical priority)
- **QOS_TYPE_EXCEPTION**: Exception handling (Critical priority)
- **QOS_TYPE_INSTR_FETCH**: Instruction fetch (High priority)
- **QOS_TYPE_DATA_ACCESS**: Data access (Medium-High priority)
- **QOS_TYPE_CACHE_FILL**: Cache line fill (Medium priority)
- **QOS_TYPE_CACHE_WB**: Cache writeback (Medium-Low priority)
- **QOS_TYPE_PREFETCH**: Prefetch operations (Low priority)
- **QOS_TYPE_DMA**: DMA transfers (Best effort)
- **QOS_TYPE_PERIPHERAL**: Peripheral access (Best effort)
- **QOS_TYPE_BACKGROUND**: Background tasks (Best effort)

### 3. Arbitration Policies

The QoS arbiter supports multiple arbitration policies:

- **Round-Robin (0)**: Fair arbitration without QoS consideration
- **Strict Priority (1)**: Highest QoS level always wins
- **Weighted Round-Robin (2)**: QoS-aware with anti-starvation (recommended)
- **Fair Arbitration (3)**: Aging-based to prevent starvation

## Implementation Details

### QoS Package (`riscv_qos_pkg.sv`)

```systemverilog
import riscv_qos_pkg::*;

// Get QoS level for transaction type
logic [3:0] qos_level = get_qos_level(QOS_TYPE_INSTR_FETCH); // Returns QOS_LEVEL_HIGH

// Configure QoS for a core
qos_config_t core_qos;
core_qos.qos_level = QOS_LEVEL_HIGH;
core_qos.transaction_type = QOS_TYPE_INSTR_FETCH;
core_qos.urgent = 1'b0;
core_qos.weight = 8'd200;
core_qos.max_latency_cycles = 16'd25;
core_qos.bandwidth_percent = 8'd30;
core_qos.core_id = 4'd0;
core_qos.real_time = 1'b1;
```

### QoS Arbiter (`qos_arbiter.sv`)

The QoS arbiter provides:

1. **Priority-based arbitration** with configurable policies
2. **Anti-starvation mechanisms** using aging algorithms
3. **Performance monitoring** with violation tracking
4. **Bandwidth allocation** control per QoS level

### Protocol Integration

#### AXI4 QoS Assignment

```systemverilog
// Dynamic QoS assignment in AXI4 adapter
assign axi_if.awqos = get_qos_level(transaction_type);
assign axi_if.arqos = get_qos_level(transaction_type);
```

#### CHI QoS Integration

```systemverilog
// CHI protocol QoS field
assign chi_if.txreq.qos = get_qos_level(transaction_type);
```

#### TileLink QoS (via User Field)

```systemverilog
// TileLink embeds QoS in user field
assign tl_if.a_user[3:0] = get_qos_level(transaction_type);
```

## Configuration Examples

### High-Performance Computing Setup

```systemverilog
// Core 0: High-priority compute core
core_qos_config[0].qos_level = QOS_LEVEL_HIGH;
core_qos_config[0].bandwidth_percent = 8'd40;
core_qos_config[0].weight = 8'd255;

// Core 1-3: Standard cores  
for (int i = 1; i < 4; i++) begin
    core_qos_config[i].qos_level = QOS_LEVEL_MEDIUM;
    core_qos_config[i].bandwidth_percent = 8'd20;
    core_qos_config[i].weight = 8'd100;
end
```

### Real-Time System Setup

```systemverilog
// Real-time core with strict latency requirements
core_qos_config[0].qos_level = QOS_LEVEL_CRITICAL;
core_qos_config[0].real_time = 1'b1;
core_qos_config[0].max_latency_cycles = 16'd10;
core_qos_config[0].urgent = 1'b1;
```

### Mixed Workload Setup

```systemverilog
// Interactive core (high priority)
core_qos_config[0].qos_level = QOS_LEVEL_HIGH;
core_qos_config[0].bandwidth_percent = 8'd35;

// Batch processing cores (medium priority)
core_qos_config[1].qos_level = QOS_LEVEL_MEDIUM;
core_qos_config[1].bandwidth_percent = 8'd25;

// Background tasks (low priority)
core_qos_config[2].qos_level = QOS_LEVEL_LOW;
core_qos_config[2].bandwidth_percent = 8'd15;
```

## Performance Monitoring

The QoS system provides comprehensive performance monitoring:

### Key Metrics

- **QoS Violations**: Transactions exceeding latency deadlines
- **Total Requests**: Total arbitrated transactions
- **Starvation Flags**: Per-core starvation detection
- **Bandwidth Utilization**: Actual vs. allocated bandwidth

### Monitoring Interface

```systemverilog
// Performance monitoring outputs from QoS arbiter
output logic [31:0] qos_violations_o;      // Violation count
output logic [31:0] total_requests_o;      // Total request count  
output logic [NUM_CORES-1:0] starvation_flags_o; // Starvation indicators
```

## Tuning Guidelines

### Latency Optimization

1. **Set appropriate QoS levels** based on criticality
2. **Configure max_latency_cycles** for time-sensitive operations
3. **Use urgent flag** for exceptional cases
4. **Enable real_time mode** for hard real-time requirements

### Throughput Optimization

1. **Use weighted round-robin** arbitration
2. **Balance bandwidth allocation** across cores
3. **Adjust weights** based on workload characteristics
4. **Monitor starvation flags** and adjust accordingly

### Power Optimization

1. **Use lower QoS levels** for non-critical operations
2. **Implement QoS-aware power gating** in downstream components
3. **Reduce arbitration frequency** for best-effort traffic

## Debug and Verification

### QoS Validation

1. **Verify QoS level assignment** for different transaction types
2. **Check arbitration fairness** under various load conditions
3. **Validate anti-starvation mechanisms** work correctly
4. **Monitor performance counters** for unexpected violations

### Common Issues

1. **QoS inversion**: Lower priority blocking higher priority
2. **Starvation**: Complete blocking of low-priority traffic
3. **Bandwidth allocation**: Mismatch between allocated and actual bandwidth
4. **Latency violations**: Exceeding configured deadlines

## Best Practices

1. **Start with conservative settings** and tune based on measurements
2. **Use performance monitoring** to guide optimization
3. **Implement QoS-aware software** that understands priority levels
4. **Regular calibration** of QoS parameters based on workload changes
5. **Document QoS policies** clearly for system integrators

## Future Extensions

1. **Dynamic QoS adjustment** based on system load
2. **QoS inheritance** for dependent transactions
3. **Multi-level QoS** with sub-priorities
4. **QoS-aware cache replacement** policies
5. **Integration with system-level power management** 