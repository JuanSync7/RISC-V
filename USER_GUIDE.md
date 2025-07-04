# RISC-V Core Implementation User Guide

## Table of Contents
1. [Overview](#overview)
2. [Quick Start](#quick-start)
3. [Architecture](#architecture)
4. [Configuration System](#configuration-system)
5. [Building the Core](#building-the-core)
6. [Integration Guide](#integration-guide)
7. [Verification](#verification)
8. [Customization](#customization)
9. [Troubleshooting](#troubleshooting)

## Overview

This is a highly configurable RISC-V processor implementation supporting RV32I base ISA with optional M, A, C, F, and V extensions. The design is parameterizable from simple embedded microcontrollers to complex multi-core application processors.

### Key Features
- **Flexible ISA Support**: RV32I base with M, A, C, F, V extensions
- **Scalable Architecture**: 1-8 cores, in-order or out-of-order
- **Hierarchical Cache**: Configurable L1/L2/L3 caches
- **Standard Peripherals**: CLINT, PLIC, UART, GPIO, SPI, I2C
- **Configuration Profiles**: Embedded, Application, Server
- **RISC-V Compliant**: Follows official RISC-V specifications

## Quick Start

### 1. List Available Configurations
```bash
cd /workspace
python3 scripts/configure_riscv.py --list-profiles
```

### 2. Generate Configuration
```bash
# For embedded systems (single-core RV32IM)
python3 scripts/configure_riscv.py --profile embedded

# For IoT/Linux (multi-core RV32IMAC)
python3 scripts/configure_riscv.py --profile application

# For high-performance (OoO RV32IMACFV)
python3 scripts/configure_riscv.py --profile server
```

### 3. Build the Core
```bash
cd configs/embedded
make compile_verilator
```

## Architecture

### Pipeline Structure
The core implements a classic 5-stage pipeline:
1. **Fetch (IF)**: Instruction fetch with branch prediction
2. **Decode (ID)**: Instruction decode and register read
3. **Execute (EX)**: ALU operations, address calculation
4. **Memory (MEM)**: Load/store operations
5. **Writeback (WB)**: Register file update

### Memory Hierarchy
```
┌─────────┐  ┌─────────┐
│ I-Cache │  │ D-Cache │  (L1: 4-64KB, 2-8 way)
└────┬────┘  └────┬────┘
     │            │
     └─────┬──────┘
           │
      ┌────┴────┐
      │ L2 Cache│         (L2: 128-512KB, 8-16 way)
      └────┬────┘
           │
      ┌────┴────┐
      │ L3 Cache│         (L3: 1-8MB, 16 way)
      └────┬────┘
           │
      ┌────┴────┐
      │   DRAM  │
      └─────────┘
```

### Interrupt Architecture
- **CLINT**: Core-local timer and software interrupts
- **PLIC**: Platform-level external interrupt controller
- Machine mode (M-mode) interrupt handling
- Optional supervisor mode (S-mode) support

## Configuration System

### Configuration Profiles

| Profile | Cores | Pipeline | ISA | Cache | Use Case |
|---------|-------|----------|-----|-------|----------|
| Embedded | 1 | In-order | RV32IM | 4KB L1 | Microcontrollers |
| Application | 4 | In-order | RV32IMAC | 16KB L1, 128KB L2 | IoT, Embedded Linux |
| Server | 8 | OoO | RV32IMACFV | 64KB L1, 512KB L2, 8MB L3 | Application Processors |

### Custom Configuration
Create a JSON file with your requirements:
```json
{
  "isa": "RV32IMAC",
  "num_cores": 2,
  "pipeline": "in_order",
  "cache": {
    "icache_size_kb": 8,
    "icache_ways": 4,
    "dcache_size_kb": 8,
    "dcache_ways": 4,
    "l2_cache_size_kb": 64,
    "l2_cache_ways": 8
  },
  "features": {
    "branch_predictor": "tournament",
    "mmu_enable": true,
    "atomic_enable": true,
    "compressed_enable": true
  },
  "peripherals": {
    "clint": true,
    "plic": true,
    "uart": true,
    "gpio": true
  }
}
```

Then generate:
```bash
python3 scripts/configure_riscv.py --profile custom --custom-config my_config.json
```

## Building the Core

### Prerequisites
- SystemVerilog simulator (Verilator, ModelSim, VCS, or Icarus Verilog)
- Python 3.6+
- Make

### Build Commands
```bash
# Configure
python3 scripts/configure_riscv.py --profile embedded

# Build with different simulators
cd configs/embedded
make compile_verilator   # Verilator (fastest, free)
make compile_iverilog    # Icarus Verilog (free)
make compile_modelsim    # ModelSim
make compile_vcs         # Synopsys VCS

# Run simulation
make sim
```

### Build Options
- `NUM_CORES=N`: Override number of cores
- `CACHE_SIZE=N`: Override cache size
- `DEBUG=1`: Enable debug features

## Integration Guide

### SoC Integration
```systemverilog
// Instantiate the RISC-V core
riscv_core #(
    .NUM_CORES(4),
    .ICACHE_SIZE_KB(16),
    .DCACHE_SIZE_KB(16)
) u_riscv_core (
    .clk_i(sys_clk),
    .rst_ni(sys_rst_n),
    
    // Instruction memory interface
    .imem_req_o(imem_req),
    .imem_addr_o(imem_addr),
    .imem_data_i(imem_data),
    .imem_ready_i(imem_ready),
    
    // Data memory interface
    .dmem_req_o(dmem_req),
    .dmem_we_o(dmem_we),
    .dmem_addr_o(dmem_addr),
    .dmem_wdata_o(dmem_wdata),
    .dmem_rdata_i(dmem_rdata),
    .dmem_ready_i(dmem_ready),
    
    // Interrupts
    .irq_software_i(soft_irq),
    .irq_timer_i(timer_irq),
    .irq_external_i(ext_irq)
);
```

### Memory Map
```
0x0000_0000 - 0x0FFF_FFFF : ROM/Flash (256MB)
0x1000_0000 - 0x1FFF_FFFF : Reserved
0x2000_0000 - 0x3FFF_FFFF : CLINT (Core-Local Interrupts)
0x4000_0000 - 0x5FFF_FFFF : Reserved
0x6000_0000 - 0x6FFF_FFFF : Peripherals
0x7000_0000 - 0x7FFF_FFFF : Reserved
0x8000_0000 - 0xBFFF_FFFF : DRAM (1GB)
0xC000_0000 - 0xCFFF_FFFF : PLIC (Platform Interrupts)
```

### Peripheral Integration
```systemverilog
// UART Example
uart_16550 u_uart (
    .clk_i(sys_clk),
    .rst_ni(sys_rst_n),
    .addr_i(periph_addr[2:0]),
    .data_i(periph_wdata),
    .data_o(uart_rdata),
    .we_i(uart_sel & periph_we),
    .re_i(uart_sel & periph_re),
    .rx_i(uart_rx),
    .tx_o(uart_tx)
);
```

## Verification

### Running Tests
```bash
# Run ISA compliance tests
cd verification
make run_isa_tests

# Run specific test suite
make run_rv32i_tests
make run_rv32m_tests

# Run all tests
make run_all_tests
```

### Test Coverage
- RISC-V ISA Compliance Tests
- Interrupt and Exception Tests
- Memory System Tests
- Multi-core Coherency Tests
- Performance Benchmarks

## Customization

### Adding New Instructions
1. Define opcode in `riscv_config_pkg.sv`
2. Add decode logic in `decode_stage.sv`
3. Implement execution in appropriate unit
4. Update documentation

### Adding Peripherals
1. Create peripheral module in `rtl/peripherals/`
2. Add to memory map
3. Update configuration system
4. Add testbench

### Cache Configuration
Edit cache parameters in configuration:
```systemverilog
// In your configuration package
parameter ICACHE_SIZE_KB = 32;
parameter ICACHE_WAYS = 4;
parameter ICACHE_LINE_SIZE = 64;
```

## Troubleshooting

### Common Issues

**Q: Build fails with "package not found"**
A: Ensure all package files are included in correct order:
```bash
# Check file list in Makefile
grep "RTL_SOURCES" configs/*/Makefile
```

**Q: Simulation hangs**
A: Check for:
- Reset properly deasserted
- Clock running
- Memory models responding

**Q: Performance lower than expected**
A: Verify:
- Branch predictor enabled
- Caches properly sized
- Forwarding paths working

### Debug Features
- Waveform dumps: Add `+define+DUMP_VCD`
- Instruction trace: Add `+define+TRACE_ENABLE`
- Performance counters: Check CSR registers

### Getting Help
1. Check existing documentation in `docs/`
2. Review test failures in `verification/logs/`
3. Enable debug outputs with compilation flags

## Advanced Topics

### Out-of-Order Configuration
```json
{
  "pipeline": "out_of_order",
  "features": {
    "ooo_enable": true,
    "rob_size": 128,
    "rs_size": 64,
    "phys_regs": 128
  }
}
```

### Multi-Core Setup
- Coherent caches with MESI protocol
- Inter-core interrupts via CLINT
- Shared L2/L3 caches
- Atomic operations support

### Security Features
- Physical Memory Protection (PMP)
- User/Supervisor/Machine modes
- Secure boot support (optional)

## Performance Optimization

### Synthesis Guidelines
- Target frequency: 100-200MHz (FPGA), 1-2GHz (ASIC)
- Critical paths typically in:
  - Cache tag comparison
  - Branch resolution
  - Forwarding multiplexers

### Area Optimization
- Disable unused features
- Reduce cache sizes
- Use 2-way caches minimum
- Share functional units

## Conclusion

This RISC-V implementation provides a solid foundation for both learning and production use. The modular design and comprehensive configuration system allow adaptation to various use cases from simple embedded controllers to complex application processors.

For additional information:
- RISC-V Specifications: https://riscv.org/specifications/
- Project Documentation: See `/workspace/docs/`
- Example SoCs: See `/workspace/examples/`