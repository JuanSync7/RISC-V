# RISC-V Core Simulation Guide

This guide provides instructions on how to simulate the RISC-V core using the provided testbenches and scripts.

## Table of Contents

- [Introduction](#introduction)
- [Prerequisites](#prerequisites)
- [Simulation Scripts](#simulation-scripts)
- [Running Unit Tests](#running-unit-tests)
- [Running Integration Tests](#running-integration-tests)
- [Advanced Simulation](#advanced-simulation)

## Introduction

The verification environment for the RISC-V core is built using SystemVerilog and UVM. It includes a comprehensive set of testbenches to verify the core at different levels, from individual units to full system integration.

This guide will walk you through the process of running these simulations and interpreting the results.

## Prerequisites

Before running simulations, ensure you have the following tools installed:

-   A SystemVerilog simulator (e.g., Synopsys VCS, Cadence Xcelium, Mentor QuestaSim)
-   Python 3.x
-   Make

You will also need to set up your environment by sourcing the appropriate setup scripts for your simulator.

## Simulation Scripts

The primary script for running unit tests is located in `tb/scripts/run_unit_tests.py`. This script automatically finds and runs all unit testbenches.

For more complex simulations and integration tests, the project provides a comprehensive `Makefile` in the root directory.

## Running Unit Tests

### Using the Python Script

The easiest way to run all unit tests is to use the `run_unit_tests.py` script.

```bash
python3 tb/scripts/run_unit_tests.py
```

This will discover, compile, and run all `*_tb.sv` files located in the `tb/unit/` directory and its subdirectories.

### Using Make

You can also run individual unit tests or all unit tests using the `Makefile` in the root directory.

To run all unit tests:

```bash
make units
```

To run a specific unit test, use its target name. For example, to run the ALU test:

```bash
make alu
```

You can specify the simulator using the `TOOL` variable (e.g., `TOOL=modelsim`).

## Running Integration Tests

Integration tests verify the a larger part of the core. These are run using the `Makefile` in the root directory.

To run the core integration test:

```bash
make core_integration
```

## Advanced Simulation

The root `Makefile` provides several options for more advanced simulation control.

-   **Enable Waveform Generation**: Use `WAVES=1` to generate waveform files (e.g., VCD or SHM) for debugging.
-   **Enable Coverage Collection**: Use `COVERAGE=1` to enable code coverage analysis.
-   **Set Random Seed**: Use `SEED=<number>` to set a specific random seed for the simulation, which is useful for reproducing test failures.

Example:

```bash
make core_integration WAVES=1 SEED=42
``` 