//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_config_pkg.sv
// Module: riscv_config_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   This top-level package aggregates all specialized configuration packages
//   for the RISC-V processor design. By importing this single package, a module
//   gains access to all configuration parameters across the entire system.
//   This approach maintains backward compatibility while improving modularity.
//   
//   This package also imports the types packages to provide access to 
//   implementation-fixed constants that were moved from config packages.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_config_pkg;

    // Import all specialized configuration packages
    import riscv_core_config_pkg::*;
    import riscv_memory_config_pkg::*;
    import riscv_pipeline_config_pkg::*;
    import riscv_soc_config_pkg::*;
    import riscv_verification_config_pkg::*;
    
    // Import types packages for implementation-fixed constants
    import riscv_core_types_pkg::*;
    import riscv_memory_types_pkg::*;
    import riscv_pipeline_types_pkg::*;

endpackage : riscv_config_pkg

`default_nettype wire