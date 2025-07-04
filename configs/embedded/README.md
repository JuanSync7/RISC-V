# RISC-V Configuration: embedded

Generated on: 2025-07-04 21:00:38

## Overview

This configuration implements a RV32IM RISC-V processor with the following characteristics:

- **ISA**: RV32IM
- **Number of Cores**: 1
- **Pipeline Type**: in_order

## Cache Hierarchy

| Level | Size | Ways | Line Size |
|-------|------|------|-----------|
| L1 I-Cache | 4 KB | 2 | 64B |
| L1 D-Cache | 4 KB | 2 | 64B |

## Features

- **Branch Predictor**: simple
- **Out-of-Order Execution**: Disabled
- **MMU**: Disabled
- **FPU**: Disabled
- **Atomic Instructions**: Disabled
- **Compressed Instructions**: Disabled
- **Vector Instructions**: Disabled

## Peripherals

| Peripheral | Status |
|------------|--------|
| CLINT (Timer) | Enabled |
| PLIC (Interrupts) | Enabled |
| UART | Enabled |
| GPIO | Enabled |
| SPI | Disabled |
| I2C | Disabled |

## Building

To build this configuration:

```bash
cd configs/embedded
make compile_verilator  # For Verilator
make compile_iverilog   # For Icarus Verilog
```

## Testing

Run the test suite:

```bash
make test
```

## Integration

To integrate this core into your SoC:

1. Include the generated configuration package
2. Instantiate the `riscv_core` module
3. Connect the bus interfaces
4. Configure memory maps for peripherals
