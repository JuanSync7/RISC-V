# Configuration Architecture

## 1. Overview
This document describes the configuration architecture of the RISC-V core, detailing how various design parameters are managed to enable flexible customization and scalability. The goal is to provide a clear understanding of how different features and performance characteristics can be tailored without modifying the core RTL logic.

## 2. Key Principles
- **Parameterization**: All major architectural features, sizes, and behavioral options are controlled through SystemVerilog parameters.
- **Centralized Configuration**: Key global parameters are defined and managed within dedicated configuration packages, primarily `riscv_config_pkg.sv`.
- **Modularity**: Modules are designed to be configurable independently, with parameters passed down through the hierarchy.
- **Readability and Maintainability**: Parameter names follow strict naming conventions (UPPER_CASE_SNAKE_CASE with specific prefixes) to enhance clarity.

## 3. Types of Parameters

### 3.1. Module Parameters (`parameter`)
- **Definition**: Declared at the module level and can be overridden during module instantiation.
- **Purpose**: Used for design-time configurable aspects such as data widths, FIFO depths, number of units, or enabling/disabling major features.
- **Naming Convention**: `CONFIG_<PARAMETER_NAME>` (e.g., `CONFIG_DATA_WIDTH`, `CONFIG_FIFO_DEPTH`).

### 3.2. Local Parameters (`localparam`)
- **Definition**: Declared within a module or package, their values are derived from other parameters or constants and cannot be overridden.
- **Purpose**: Used for internal constants or values calculated based on configurable parameters (e.g., address width derived from memory size).
- **Naming Convention**: `LP_<PARAMETER_NAME>` (e.g., `LP_ADDR_BITS`, `LP_COUNT_WIDTH`).

### 3.3. Type Parameters (`parameter type`)
- **Definition**: Allow passing SystemVerilog data types as parameters to modules or interfaces.
- **Purpose**: Used to define generic data types that can vary based on configuration, promoting type safety and flexibility (e.g., `addr_t`, `word_t`).
- **Naming Convention**: `TYPE_<PARAMETER_NAME>` (e.g., `TYPE_ADDR`, `TYPE_DATA`).

## 4. Centralized Configuration with `riscv_config_pkg.sv`

`riscv_config_pkg.sv` serves as the primary repository for global configuration parameters that affect multiple parts of the RISC-V core. By importing this package, modules can access these parameters consistently.

### 4.1. Key Parameters in `riscv_config_pkg.sv` (Examples)
- `ENABLE_FPU`: Boolean to enable/disable the Floating Point Unit.
- `ENABLE_VPU`: Boolean to enable/disable the Vector Processing Unit.
- `ENABLE_ML_INFERENCE`: Boolean to enable/disable the Machine Learning Inference Unit.
- `DATA_WIDTH`: Global data bus width (e.g., 32).
- `ADDR_WIDTH`: Global address bus width (e.g., 32).
- `RESET_VECTOR`: Default program counter value after reset.
- `BTB_ENTRIES`, `BHT_ENTRIES`: Parameters for branch prediction unit sizing.
- `INSTR_CACHE_SIZE`, `DATA_CACHE_SIZE`: Parameters for cache sizing.

### 4.2. Usage Example
```systemverilog
// In a module that needs global configuration
import riscv_config_pkg::*;

module my_module #(
    parameter integer MY_LOCAL_PARAM = CONFIG_DATA_WIDTH / 2
) (
    // ... ports
);

    // Conditional instantiation based on global parameter
    `ifdef ENABLE_FPU
        fpu_unit u_fpu (
            // ... connections
        );
    `endif

    // Using a global parameter for a local declaration
    logic [CONFIG_DATA_WIDTH-1:0] my_data_signal;

endmodule
```

## 5. Guidelines for Adding New Configurable Parameters
1.  **Identify Scope**: Determine if the parameter is local to a module or global across the design.
2.  **Global Parameters**: If global, add it to `riscv_config_pkg.sv` with the `CONFIG_` prefix.
3.  **Module-Specific Parameters**: If local, declare it within the module with the `CONFIG_` prefix.
4.  **Derived Constants**: Use `localparam` with the `LP_` prefix for values derived from other parameters.
5.  **Type Definitions**: Use `parameter type` with the `TYPE_` prefix for generic types.
6.  **Documentation**: Add clear comments for each parameter, explaining its purpose, valid range, and default value.
7.  **Consistency**: Adhere to the naming conventions and ensure consistent usage throughout the codebase.

## 6. Impact on Design Flow
- **Synthesis**: Parameters are typically resolved at synthesis time, allowing the synthesis tool to optimize the design based on the chosen configuration.
- **Simulation**: Parameters can be easily changed during simulation setup to test different configurations without recompiling the RTL.
- **Verification**: Testbenches can be parameterized to verify different core configurations, ensuring robustness across the design space.

## 7. Future Considerations
- **Configuration Management Tool**: Develop or integrate a tool for easier management and generation of configuration files.
- **Formal Verification of Parameters**: Use formal methods to verify the correctness of parameter interactions and constraints.
- **Runtime Configuration**: Explore mechanisms for limited runtime configuration of certain features (e.g., via CSRs).
