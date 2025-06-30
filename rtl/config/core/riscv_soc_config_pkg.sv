//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_soc_config_pkg.sv
// Module: riscv_soc_config_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   This package contains System-on-Chip (SoC) level configurations, including
//   multi-core setup, security features, debug infrastructure, and power management.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_soc_config_pkg;
    import riscv_qos_pkg::*;

    //---------------------------------------------------------------------------
    // 4. Multi-Core Configuration
    //---------------------------------------------------------------------------
    parameter integer MAX_CORES = 4;                  // Maximum number of cores supported
    parameter integer CORE_ID_WIDTH = $clog2(MAX_CORES);
    parameter integer DEFAULT_NUM_CORES = 1;          // Default number of cores
    
    //---------------------------------------------------------------------------
    // 11. Security and Safety Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_ECC_WIDTH = 8;               // ECC bits per 64-bit word
    parameter integer DEFAULT_PARITY_WIDTH = 1;            // Parity bit per byte
    
    //---------------------------------------------------------------------------
    // 12. Debug Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_DEBUG_REGISTERS = 8;
    parameter integer DEFAULT_BREAKPOINTS = 4;
    parameter integer DEFAULT_WATCHPOINTS = 4;
    parameter integer DEFAULT_DEBUG_CHANNELS = 16;
    
    //---------------------------------------------------------------------------
    // 13. Power Management Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_POWER_DOMAINS = 2;           // Core + Memory
    parameter integer DEFAULT_CLOCK_DOMAINS = 1;           // Single clock domain

    //---------------------------------------------------------------------------
    // 14. QoS Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_QOS_LEVELS = 8;                  // Number of QoS priority levels

    // QoS Priority Levels
    parameter integer QOS_LEVEL_CRITICAL      = 7;
    parameter integer QOS_LEVEL_HIGH          = 6;
    parameter integer QOS_LEVEL_MEDIUM_HIGH   = 5;
    parameter integer QOS_LEVEL_MEDIUM        = 4;
    parameter integer QOS_LEVEL_LOW           = 2;

    // QoS Transaction Types
    parameter logic [1:0] QOS_TYPE_INSTR_FETCH  = 2'b00;
    parameter logic [1:0] QOS_TYPE_DATA_ACCESS  = 2'b01;
    parameter logic [1:0] QOS_TYPE_PREFETCH     = 2'b10;

    // QoS Weights
    parameter integer QOS_WEIGHT_CRITICAL     = 100;
    parameter integer QOS_WEIGHT_HIGH         = 50;
    parameter integer QOS_WEIGHT_MEDIUM_HIGH  = 25;
    parameter integer QOS_WEIGHT_MEDIUM       = 10;
    parameter integer QOS_WEIGHT_LOW          = 1;

    // QoS Latency Targets (in cycles)
    parameter integer QOS_INSTR_LATENCY_CRITICAL    = 10;
    parameter integer QOS_INSTR_LATENCY_NORMAL      = 50;
    parameter integer QOS_DATA_LATENCY_CRITICAL     = 10;
    parameter integer QOS_DATA_STORE_LATENCY_NORMAL = 100;
    parameter integer QOS_DATA_LOAD_LATENCY_NORMAL  = 60;

    // QoS Bandwidth Allocation
    parameter integer QOS_INSTR_BW_PERCENT = 50; // Guaranteed bandwidth % for instructions
    parameter integer QOS_DATA_BW_PERCENT  = 50; // Guaranteed bandwidth % for data

    // QoS Retry Limits
    parameter integer QOS_INSTR_RETRY_LIMIT = 5;
    parameter integer QOS_DATA_RETRY_LIMIT  = 5;

    // Default QoS settings for CSRs
    parameter integer DEFAULT_QOS_WEIGHT = 100;
    parameter integer DEFAULT_QOS_LATENCY_LIMIT = 100;
    parameter integer DEFAULT_QOS_BW_ALLOC = 25;
    parameter qos_arbiter_policy_e DEFAULT_QOS_ARBITER_POLICY = QOS_ARBITER_WEIGHTED_RR;

    //---------------------------------------------------------------------------
    // CSR Address Configuration
    //---------------------------------------------------------------------------
    // QoS CSR address range (Custom CSR space)
    parameter logic [11:0] QOS_CSR_BASE = 12'hBC0;                  // Base address for QoS CSRs
    parameter logic [11:0] QOS_CSR_END = 12'hBDF;                   // End address for QoS CSRs
    
    // Individual QoS CSR addresses
    parameter logic [11:0] CSR_QOS_CONTROL = 12'hBC0;               // Global QoS control
    parameter logic [11:0] CSR_QOS_STATUS = 12'hBC1;                // QoS status register
    parameter logic [11:0] CSR_QOS_VIOLATIONS = 12'hBC2;            // QoS violation count
    parameter logic [11:0] CSR_QOS_REQUESTS = 12'hBC3;              // Total request count
    
    // Per-core QoS configuration CSRs (0xBC4-0xBC7)
    parameter logic [11:0] CSR_QOS_CORE0_CFG = 12'hBC4;             // Core 0 QoS config
    parameter logic [11:0] CSR_QOS_CORE1_CFG = 12'hBC5;             // Core 1 QoS config
    parameter logic [11:0] CSR_QOS_CORE2_CFG = 12'hBC6;             // Core 2 QoS config
    parameter logic [11:0] CSR_QOS_CORE3_CFG = 12'hBC7;             // Core 3 QoS config
    
    // QoS performance monitoring CSRs
    parameter logic [11:0] CSR_QOS_PERF_BASE = 12'hBC8;             // Base for performance CSRs
    
    // QoS bandwidth allocation CSRs (0xBD0-0xBD3)
    parameter logic [11:0] CSR_QOS_BW_CORE0 = 12'hBD0;              // Core 0 bandwidth
    parameter logic [11:0] CSR_QOS_BW_CORE1 = 12'hBD1;              // Core 1 bandwidth
    parameter logic [11:0] CSR_QOS_BW_CORE2 = 12'hBD2;              // Core 2 bandwidth
    parameter logic [11:0] CSR_QOS_BW_CORE3 = 12'hBD3;              // Core 3 bandwidth
    
    // QoS debug and monitoring CSRs
    parameter logic [11:0] CSR_QOS_DEBUG = 12'hBD4;                 // Debug control
    parameter logic [11:0] CSR_QOS_MONITOR = 12'hBD5;               // Monitoring control
    
    //---------------------------------------------------------------------------
    // Power Management Configuration
    //---------------------------------------------------------------------------
    // Voltage levels (3-bit encoding)
    parameter logic [2:0] VOLTAGE_LEVEL_MIN = 3'b001;               // Minimum voltage
    parameter logic [2:0] VOLTAGE_LEVEL_LOW = 3'b010;               // Low voltage
    parameter logic [2:0] VOLTAGE_LEVEL_MID = 3'b100;               // Mid voltage (default)
    parameter logic [2:0] VOLTAGE_LEVEL_HIGH = 3'b110;              // High voltage
    parameter logic [2:0] VOLTAGE_LEVEL_MAX = 3'b111;               // Maximum voltage
    
    // Frequency levels (4-bit encoding)
    parameter logic [3:0] FREQUENCY_LEVEL_MIN = 4'h2;               // Minimum frequency
    parameter logic [3:0] FREQUENCY_LEVEL_LOW = 4'h4;               // Low frequency
    parameter logic [3:0] FREQUENCY_LEVEL_MID = 4'h8;               // Mid frequency (default)
    parameter logic [3:0] FREQUENCY_LEVEL_HIGH = 4'hC;              // High frequency
    parameter logic [3:0] FREQUENCY_LEVEL_MAX = 4'hF;               // Maximum frequency
    
    // Performance thresholds
    parameter integer THERMAL_THROTTLE_PERFORMANCE = 32;            // Low performance for thermal safety
    parameter integer HIGH_CACHE_MISS_PERFORMANCE = 224;            // High performance for memory-bound (0xE0)
    parameter integer CACHE_MISS_THRESHOLD_PERCENT = 50;            // Cache miss threshold for performance scaling
    parameter integer PERFORMANCE_DEMAND_MASK = 8'hF0;              // Mask for performance demand upper nibble
    
    // Clock gating thresholds
    parameter integer L3_CACHE_GATING_THRESHOLD = 10;               // L3 cache miss rate threshold for gating
    
    //---------------------------------------------------------------------------
    // Performance Monitoring Default Values
    //---------------------------------------------------------------------------
    // Default performance metrics (scaled by 1000 for precision)
    parameter integer DEFAULT_IPC_SCALED = 850;                     // Default IPC (0.85 * 1000)
    parameter integer DEFAULT_L1_HIT_RATE_SCALED = 950;             // Default L1 hit rate (95%)
    parameter integer DEFAULT_L2_HIT_RATE_SCALED = 800;             // Default L2 hit rate (80%)
    parameter integer DEFAULT_BRANCH_ACCURACY_SCALED = 850;         // Default branch accuracy (85%)
    parameter integer DEFAULT_PIPELINE_UTIL_SCALED = 750;           // Default pipeline utilization (75%)
    
    // Performance calculation precision
    parameter integer PERFORMANCE_SCALING_FACTOR = 1000;            // Scaling factor for percentage calculations
    parameter integer IPC_HIGH_THRESHOLD = 800;                     // High IPC threshold for power estimation
    
    // Power estimation parameters
    parameter integer BASE_POWER_MW = 500;                          // Base power in milliwatts
    parameter integer CORE_POWER_MW = 250;                          // Power per active core in milliwatts
    parameter integer HIGH_ACTIVITY_POWER_MW = 300;                 // Additional power for high activity
    parameter integer LOW_ACTIVITY_POWER_MW = 100;                  // Additional power for low activity

endpackage : riscv_soc_config_pkg

`default_nettype wire 