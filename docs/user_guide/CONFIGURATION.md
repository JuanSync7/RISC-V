# Core Configuration

This document describes the parameters that can be used to configure the RISC-V core.

## Feature Enablement

The following parameters in `rtl/config/core/riscv_core_config_pkg.sv` can be used to enable or disable specific features of the core:

- `ENABLE_FPU`: Set to `1` to enable the Floating-Point Unit (FPU), or `0` to disable it.
- `ENABLE_VPU`: Set to `1` to enable the Vector Processing Unit (VPU), or `0` to disable it.
- `ENABLE_ML_INFERENCE`: Set to `1` to enable the Machine Learning Inference Unit, or `0` to disable it.

When a feature is disabled, any attempt to execute an instruction that uses that feature will result in an illegal instruction exception.

## Bus Timeout

The `BUS_TIMEOUT_CYCLES` parameter in `rtl/config/core/riscv_verification_config_pkg.sv` sets the number of clock cycles that the memory wrapper will wait for a response from the bus before asserting an error. This prevents the core from stalling indefinitely if a bus transaction hangs.