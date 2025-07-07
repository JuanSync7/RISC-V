#!/bin/bash
# compile_pkgs.sh

# This script compiles the core packages to verify their correctness.

# Assuming a SystemVerilog compiler (like VCS) is in the PATH
vlog -work work "C:/Users/Juan.Kok/OneDrive - Sondrel Ltd/Documents/GitHub/RISC-V/rtl/config/riscv_config_pkg.sv"
vlog -work work "C:/Users/Juan.Kok/OneDrive - Sondrel Ltd/Documents/GitHub/RISC-V/rtl/pkg/riscv_types_pkg.sv"

if [ $? -eq 0 ]; then
    echo "Task 1.1 Verification PASSED: Packages compiled successfully."
else
    echo "Task 1.1 Verification FAILED: Compilation errors."
fi