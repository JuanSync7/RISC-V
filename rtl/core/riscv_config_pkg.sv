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
//   Comprehensive configuration package that centralizes all hard-coded values
//   and provides complete flexibility for the RISC-V processor design.
//   This package should be imported by all other packages and modules.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_config_pkg;

    //---------------------------------------------------------------------------
    // 1. Core Architecture Configuration
    //---------------------------------------------------------------------------
    parameter integer XLEN = 32;                    // Data width (32 for RV32, 64 for RV64)
    parameter integer ADDR_WIDTH = 32;              // Address width
    parameter integer REG_COUNT = 32;               // Number of architectural registers
    parameter integer REG_ADDR_WIDTH = $clog2(REG_COUNT);
    
    // Reset vector configuration
    parameter logic [ADDR_WIDTH-1:0] DEFAULT_RESET_VECTOR = 32'h0000_0000;
    
    //---------------------------------------------------------------------------
    // 2. RISC-V Instruction Encoding Constants
    //---------------------------------------------------------------------------
    // Opcodes (RISC-V specification)
    parameter logic [6:0] OPCODE_LUI    = 7'b0110111;
    parameter logic [6:0] OPCODE_AUIPC  = 7'b0010111;
    parameter logic [6:0] OPCODE_JAL    = 7'b1101111;
    parameter logic [6:0] OPCODE_JALR   = 7'b1100111;
    parameter logic [6:0] OPCODE_BRANCH = 7'b1100011;
    parameter logic [6:0] OPCODE_LOAD   = 7'b0000011;
    parameter logic [6:0] OPCODE_STORE  = 7'b0100011;
    parameter logic [6:0] OPCODE_OP_IMM = 7'b0010011;
    parameter logic [6:0] OPCODE_OP     = 7'b0110011;
    parameter logic [6:0] OPCODE_FENCE  = 7'b0001111;
    parameter logic [6:0] OPCODE_SYSTEM = 7'b1110011;

    // DPU Custom Opcodes
    parameter logic [6:0] OPCODE_CUSTOM0 = 7'b0001011; // Example custom opcode

    // DPU Funct3 fields for unit selection
    parameter logic [2:0] FUNCT3_DPU_FPU = 3'b000;
    parameter logic [2:0] FUNCT3_DPU_VPU = 3'b001;
    parameter logic [2:0] FUNCT3_DPU_MLIU = 3'b010;

    // DPU Funct7 fields for operation selection (examples)
    // FPU Operations (used with FUNCT3_DPU_FPU)
    parameter logic [6:0] FUNCT7_FPU_ADD = 7'b0000000;
    parameter logic [6:0] FUNCT7_FPU_SUB = 7'b0000001;
    parameter logic [6:0] FUNCT7_FPU_MUL = 7'b0000010;

    // VPU Operations (used with FUNCT3_DPU_VPU)
    parameter logic [6:0] FUNCT7_VPU_ADD = 7'b0000000;
    parameter logic [6:0] FUNCT7_VPU_SUB = 7'b0000001;

    // MLIU Operations (used with FUNCT3_DPU_MLIU)
    parameter logic [6:0] FUNCT7_MLIU_INFER = 7'b0000000;

    // Function codes
    parameter logic [6:0] FUNCT7_M_EXT = 7'b0000001;
    
    // Common instruction encodings
    parameter logic [31:0] NOP_INSTRUCTION = 32'h00000013;  // addi x0, x0, 0
    
    //---------------------------------------------------------------------------
    // 3. Exception and Interrupt Configuration
    //---------------------------------------------------------------------------
    // Exception cause codes (RISC-V specification)
    parameter logic [31:0] CAUSE_MISALIGNED_FETCH       = 32'h0;
    parameter logic [31:0] CAUSE_FETCH_ACCESS           = 32'h1;
    parameter logic [31:0] CAUSE_ILLEGAL_INSTRUCTION    = 32'h2;
    parameter logic [31:0] CAUSE_BREAKPOINT             = 32'h3;
    parameter logic [31:0] CAUSE_MISALIGNED_LOAD        = 32'h4;
    parameter logic [31:0] CAUSE_LOAD_ACCESS            = 32'h5;
    parameter logic [31:0] CAUSE_MISALIGNED_STORE       = 32'h6;
    parameter logic [31:0] CAUSE_STORE_ACCESS           = 32'h7;
    parameter logic [31:0] CAUSE_ECALL_U                = 32'h8;
    parameter logic [31:0] CAUSE_ECALL_S                = 32'h9;
    parameter logic [31:0] CAUSE_ECALL_M                = 32'hB;
    parameter logic [31:0] CAUSE_INSTRUCTION_PAGE_FAULT = 32'hC;
    parameter logic [31:0] CAUSE_LOAD_PAGE_FAULT        = 32'hD;
    parameter logic [31:0] CAUSE_STORE_PAGE_FAULT       = 32'hF;
    
    // Interrupt base (MSB is 1)
    parameter logic [31:0] CAUSE_INTERRUPT              = 32'h80000000;
    parameter logic [31:0] CAUSE_M_SOFTWARE_INTERRUPT   = (CAUSE_INTERRUPT | 3);
    parameter logic [31:0] CAUSE_M_TIMER_INTERRUPT      = (CAUSE_INTERRUPT | 7);
    parameter logic [31:0] CAUSE_M_EXTERNAL_INTERRUPT   = (CAUSE_INTERRUPT | 11);
    
    // CSR addresses (RISC-V specification)
    parameter logic [11:0] MSTATUS_ADDR  = 12'h300;
    parameter logic [11:0] MISA_ADDR     = 12'h301;
    parameter logic [11:0] MIE_ADDR      = 12'h304;
    parameter logic [11:0] MTVEC_ADDR    = 12'h305;
    parameter logic [11:0] MSCRATCH_ADDR = 12'h340;
    parameter logic [11:0] MEPC_ADDR     = 12'h341;
    parameter logic [11:0] MCAUSE_ADDR   = 12'h342;
    parameter logic [11:0] MTVAL_ADDR    = 12'h343;
    parameter logic [11:0] MIP_ADDR      = 12'h344;
    parameter logic [11:0] MHARTID_ADDR  = 12'hF14;
    
    //---------------------------------------------------------------------------
    // 4. Multi-Core Configuration
    //---------------------------------------------------------------------------
    parameter integer MAX_CORES = 4;                  // Maximum number of cores supported
    parameter integer CORE_ID_WIDTH = $clog2(MAX_CORES);
    parameter integer DEFAULT_NUM_CORES = 1;          // Default number of cores
    
    //---------------------------------------------------------------------------
    // 5. Cache System Configuration
    //---------------------------------------------------------------------------
    // Cache sizes (in bytes)
    parameter integer DEFAULT_L1_CACHE_SIZE = 32*1024;     // 32KB
    parameter integer DEFAULT_L2_CACHE_SIZE = 256*1024;    // 256KB
    parameter integer DEFAULT_L3_CACHE_SIZE = 2*1024*1024; // 2MB
    
    // Cache associativity
    parameter integer DEFAULT_L1_CACHE_WAYS = 2;
    parameter integer DEFAULT_L2_CACHE_WAYS = 8;
    parameter integer DEFAULT_L3_CACHE_WAYS = 16;
    
    // Cache line size
    parameter integer DEFAULT_CACHE_LINE_SIZE = 64;        // 64 bytes per line
    
    //---------------------------------------------------------------------------
    // 6. Branch Predictor Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_BTB_ENTRIES = 64;
    parameter integer DEFAULT_BHT_ENTRIES = 256;
    parameter integer DEFAULT_PHT_ENTRIES = 1024;
    parameter integer DEFAULT_SELECTOR_ENTRIES = 512;
    parameter integer DEFAULT_GLOBAL_HISTORY_WIDTH = 8;
    parameter integer DEFAULT_RSB_ENTRIES = 16;
    parameter integer DEFAULT_RAS_ENTRIES = 8;
    
    // Branch predictor counter widths
    parameter integer BTB_COUNTER_WIDTH = 2;
    parameter integer BHT_COUNTER_WIDTH = 2;
    parameter integer PHT_COUNTER_WIDTH = 2;
    parameter integer SELECTOR_COUNTER_WIDTH = 2;
    parameter integer CONFIDENCE_WIDTH = 8;
    
    // Branch predictor type configuration
    parameter string DEFAULT_BRANCH_PREDICTOR_TYPE = "TOURNAMENT";  // "BIMODAL", "GSHARE", "TOURNAMENT"
    
    // Execution mode configuration
    parameter string DEFAULT_EXECUTION_MODE = "OUT_OF_ORDER";       // "IN_ORDER" or "OUT_OF_ORDER"
    
    //---------------------------------------------------------------------------
    // 7. Out-of-Order Engine Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_ROB_SIZE = 32;
    parameter integer DEFAULT_RS_SIZE = 16;
    parameter integer DEFAULT_PHYS_REGS = 64;
    
    // Functional unit counts
    parameter integer DEFAULT_NUM_ALU_UNITS = 2;
    parameter integer DEFAULT_NUM_MULT_UNITS = 1;
    parameter integer DEFAULT_NUM_DIV_UNITS = 1;
    
    // Division unit latency
    parameter integer DEFAULT_DIV_LATENCY = 32;
    
    //---------------------------------------------------------------------------
    // 8. Memory System Configuration
    //---------------------------------------------------------------------------
    // Prefetch unit configuration
    parameter integer DEFAULT_STRIDE_TABLE_SIZE = 64;
    parameter integer DEFAULT_PREFETCH_DISTANCE = 4;
    
    // Memory protocol configuration
    parameter integer DEFAULT_AXI4_ID_WIDTH = 4;
    parameter integer DEFAULT_AXI4_ADDR_WIDTH = 32;
    parameter integer DEFAULT_AXI4_DATA_WIDTH = 32;
    parameter integer DEFAULT_AXI4_STRB_WIDTH = DEFAULT_AXI4_DATA_WIDTH/8;
    
    //---------------------------------------------------------------------------
    // 9. Verification Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_CLK_PERIOD = 10;             // 100MHz clock
    parameter integer DEFAULT_TIMEOUT_CYCLES = 1000;
    parameter integer DEFAULT_MAX_TEST_ITERATIONS = 100;
    
    //---------------------------------------------------------------------------
    // 10. Performance Configuration
    //---------------------------------------------------------------------------
    // Target frequencies (MHz)
    parameter integer TARGET_FREQ_ASIC = 1000;             // 1GHz for ASIC
    parameter integer TARGET_FREQ_FPGA = 100;              // 100MHz for FPGA
    
    // Pipeline configuration
    parameter integer DEFAULT_PIPELINE_STAGES = 5;         // IF, ID, EX, MEM, WB
    
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
    
    //---------------------------------------------------------------------------
    // 13. Power Management Configuration
    //---------------------------------------------------------------------------
    parameter integer DEFAULT_POWER_DOMAINS = 2;           // Core + Memory
    parameter integer DEFAULT_CLOCK_DOMAINS = 1;           // Single clock domain
    
    //---------------------------------------------------------------------------
    // 14. Configuration Validation Functions
    //---------------------------------------------------------------------------
    // Function to validate cache configuration
    function automatic logic validate_cache_config(
        input integer cache_size,
        input integer line_size,
        input integer ways
    );
        // Cache size must be power of 2
        if ((cache_size & (cache_size - 1)) != 0) return 1'b0;
        // Line size must be power of 2 and >= 4 bytes
        if ((line_size & (line_size - 1)) != 0 || line_size < 4) return 1'b0;
        // Ways must be power of 2
        if ((ways & (ways - 1)) != 0) return 1'b0;
        // Cache size must be >= line_size * ways
        if (cache_size < (line_size * ways)) return 1'b0;
        return 1'b1;
    endfunction
    
    // Function to calculate cache parameters
    function automatic integer calc_cache_sets(
        input integer cache_size,
        input integer line_size,
        input integer ways
    );
        return cache_size / (line_size * ways);
    endfunction
    
    function automatic integer calc_cache_index_bits(
        input integer cache_size,
        input integer line_size,
        input integer ways
    );
        return $clog2(calc_cache_sets(cache_size, line_size, ways));
    endfunction
    
    function automatic integer calc_cache_offset_bits(
        input integer line_size
    );
        return $clog2(line_size);
    endfunction
    
    function automatic integer calc_cache_tag_bits(
        input integer addr_width,
        input integer cache_size,
        input integer line_size,
        input integer ways
    );
        return addr_width - calc_cache_index_bits(cache_size, line_size, ways) - calc_cache_offset_bits(line_size);
    endfunction
    
    //---------------------------------------------------------------------------
    // 15. Configuration Presets
    //---------------------------------------------------------------------------
    // Small configuration (for FPGA or area-constrained designs)
    parameter integer SMALL_L1_CACHE_SIZE = 8*1024;        // 8KB
    parameter integer SMALL_L2_CACHE_SIZE = 64*1024;       // 64KB
    parameter integer SMALL_ROB_SIZE = 16;
    parameter integer SMALL_RS_SIZE = 8;
    parameter integer SMALL_BTB_ENTRIES = 32;
    parameter integer SMALL_BHT_ENTRIES = 128;
    
    // Large configuration (for high-performance designs)
    parameter integer LARGE_L1_CACHE_SIZE = 64*1024;       // 64KB
    parameter integer LARGE_L2_CACHE_SIZE = 512*1024;      // 512KB
    parameter integer LARGE_L3_CACHE_SIZE = 8*1024*1024;   // 8MB
    parameter integer LARGE_ROB_SIZE = 64;
    parameter integer LARGE_RS_SIZE = 32;
    parameter integer LARGE_BTB_ENTRIES = 128;
    parameter integer LARGE_BHT_ENTRIES = 512;
    parameter integer LARGE_NUM_ALU_UNITS = 4;
    parameter integer LARGE_NUM_MULT_UNITS = 2;
    parameter integer LARGE_NUM_DIV_UNITS = 2;

    //---------------------------------------------------------------------------
    // 14. Enhanced Multi-Core Configuration
    //---------------------------------------------------------------------------
    parameter integer MAX_CORES_SUPPORTED = 8;          // Maximum cores hardware can support
    parameter integer CORE_ID_WIDTH_MAX = $clog2(MAX_CORES_SUPPORTED);
    parameter integer DEFAULT_MSG_WIDTH = 32;           // Inter-core message width
    parameter integer DEFAULT_NUM_BARRIERS = 8;         // Hardware barrier count
    parameter integer DEFAULT_BARRIER_TIMEOUT = 10000;  // Barrier timeout cycles
    
    // Core topology configuration
    parameter string DEFAULT_TOPOLOGY = "RING";         // "RING", "MESH", "TORUS", "XBAR"
    parameter integer MESH_WIDTH = 2;                   // For mesh topology
    parameter integer MESH_HEIGHT = 2;                  // For mesh topology
    
    //---------------------------------------------------------------------------
    // 15. Enhanced Cache Configuration
    //---------------------------------------------------------------------------
    // L1 Cache detailed configuration
    parameter integer DEFAULT_L1_ICACHE_SIZE = 32*1024;     // 32KB instruction cache
    parameter integer DEFAULT_L1_DCACHE_SIZE = 32*1024;     // 32KB data cache
    parameter integer DEFAULT_L1_ICACHE_WAYS = 2;           // I-cache associativity
    parameter integer DEFAULT_L1_DCACHE_WAYS = 2;           // D-cache associativity
    parameter integer DEFAULT_L1_ICACHE_LINE_SIZE = 64;     // I-cache line size
    parameter integer DEFAULT_L1_DCACHE_LINE_SIZE = 64;     // D-cache line size
    
    // Cache replacement policies
    parameter string DEFAULT_L1_REPLACEMENT = "LRU";        // "LRU", "RANDOM", "FIFO"
    parameter string DEFAULT_L2_REPLACEMENT = "LRU";        // L2 replacement policy
    parameter string DEFAULT_L3_REPLACEMENT = "LRU";        // L3 replacement policy
    
    // Cache coherency configuration
    parameter string DEFAULT_COHERENCY_PROTOCOL = "MESI";   // "MESI", "MOESI", "MSI"
    parameter integer DEFAULT_SNOOP_FILTER_SIZE = 1024;     // Snoop filter entries
    
    // Cache performance tuning
    parameter integer DEFAULT_CACHE_MISS_PENALTY = 100;     // Cycles for cache miss
    parameter integer DEFAULT_COHERENCY_LATENCY = 10;       // Coherency operation latency
    parameter integer DEFAULT_WRITEBACK_LATENCY = 50;       // Writeback latency
    
    //---------------------------------------------------------------------------
    // 16. Enhanced Protocol Configuration
    //---------------------------------------------------------------------------
    // Protocol selection and capabilities
    parameter string DEFAULT_MEMORY_PROTOCOL = "AXI4";      // Default memory protocol
    parameter logic  ENABLE_AXI4_PROTOCOL = 1'b1;           // Enable AXI4 support
    parameter logic  ENABLE_CHI_PROTOCOL = 1'b1;            // Enable CHI support
    parameter logic  ENABLE_TILELINK_PROTOCOL = 1'b1;       // Enable TileLink support
    parameter logic  ENABLE_PROTOCOL_SWITCHING = 1'b1;      // Dynamic protocol switching
    
    // Protocol-specific parameters
    parameter integer DEFAULT_AXI4_MAX_OUTSTANDING = 16;    // AXI4 outstanding transactions
    parameter integer DEFAULT_CHI_MAX_OUTSTANDING = 32;     // CHI outstanding transactions
    parameter integer DEFAULT_TL_MAX_OUTSTANDING = 16;      // TileLink outstanding transactions
    
    // CHI-specific configuration
    parameter integer DEFAULT_CHI_NODE_ID = 1;              // CHI node ID
    parameter integer DEFAULT_CHI_HOME_NODE_ID = 0;         // CHI home node ID
    parameter string  DEFAULT_CHI_VERSION = "CHI_B";        // CHI specification version
    
    // TileLink-specific configuration  
    parameter integer DEFAULT_TL_SOURCE_ID_BASE = 0;        // TileLink source ID base
    parameter string  DEFAULT_TL_VERSION = "TL_UL";         // TileLink version (TL-UL/TL-UH/TL-C)
    
    //---------------------------------------------------------------------------
    // 17. Enhanced Performance Configuration
    //---------------------------------------------------------------------------
    // Performance monitoring
    parameter integer DEFAULT_PERF_COUNTERS = 16;           // Number of performance counters
    parameter integer DEFAULT_PERF_COUNTER_WIDTH = 64;      // Performance counter width
    parameter logic   ENABLE_PERF_MONITORING = 1'b1;        // Enable performance monitoring
    parameter integer DEFAULT_PERF_SAMPLE_RATE = 1000;      // Performance sampling rate
    
    // Bandwidth and latency targets
    parameter integer TARGET_MEMORY_BANDWIDTH_GBPS = 10;    // Target memory bandwidth (Gbps)
    parameter integer TARGET_CACHE_LATENCY_CYCLES = 2;      // Target cache access latency
    parameter integer TARGET_COHERENCY_LATENCY_CYCLES = 10; // Target coherency latency
    
    // Power management
    parameter logic   ENABLE_CLOCK_GATING = 1'b1;           // Enable clock gating
    parameter logic   ENABLE_POWER_GATING = 1'b0;           // Enable power gating
    parameter integer DEFAULT_IDLE_TIMEOUT = 1000;          // Idle timeout for power management
    
    //---------------------------------------------------------------------------
    // 18. Enhanced Debug and Verification Configuration
    //---------------------------------------------------------------------------
    // Debug capabilities
    parameter logic   ENABLE_DEBUG_MODULE = 1'b1;           // Enable debug module
    parameter integer DEFAULT_DEBUG_ADDRESS_BASE = 32'h1000; // Debug module base address
    parameter integer DEFAULT_DEBUG_ROM_SIZE = 4096;        // Debug ROM size
    parameter logic   ENABLE_TRACE_UNIT = 1'b1;             // Enable trace unit
    parameter integer DEFAULT_TRACE_BUFFER_SIZE = 8192;     // Trace buffer size
    
    // Verification configuration
    parameter logic   ENABLE_ASSERTIONS = 1'b1;             // Enable SVA assertions
    parameter logic   ENABLE_COVERAGE = 1'b1;               // Enable coverage collection
    parameter integer DEFAULT_SIM_TIMEOUT = 100000;         // Simulation timeout cycles
    parameter logic   ENABLE_RANDOM_DELAYS = 1'b0;          // Enable random delays in testbench
    
    // Test configuration
    parameter integer DEFAULT_TEST_ITERATIONS = 1000;       // Default test iterations
    parameter integer DEFAULT_STRESS_TEST_TIME = 1000000;   // Stress test duration
    parameter logic   ENABLE_DIRECTED_TESTS = 1'b1;         // Enable directed tests
    parameter logic   ENABLE_RANDOM_TESTS = 1'b1;           // Enable random tests
    
    //---------------------------------------------------------------------------
    // 21. Accelerator Configuration
    //---------------------------------------------------------------------------
    parameter logic ENABLE_DATA_ACCELERATOR = 1'b0; // Enable/Disable Data Processing Unit (DPU)
    parameter logic ENABLE_FPU = 1'b0;              // Enable/Disable Floating Point Unit
    parameter logic ENABLE_VPU = 1'b0;              // Enable/Disable Vector Processing Unit
    parameter logic ENABLE_ML_INFERENCE = 1'b0;     // Enable/Disable Machine Learning Inference Unit

    //---------------------------------------------------------------------------
    // 19. Enhanced Memory System Configuration  
    //---------------------------------------------------------------------------
    // Memory hierarchy configuration
    parameter integer DEFAULT_MEMORY_CHANNELS = 1;          // Number of memory channels
    parameter integer DEFAULT_MEMORY_RANKS = 1;             // Memory ranks per channel
    parameter integer DEFAULT_MEMORY_BANKS = 8;             // Memory banks per rank
    parameter integer DEFAULT_MEMORY_PAGE_SIZE = 4096;      // Memory page size
    
    // Memory timing parameters
    parameter integer DEFAULT_MEMORY_LATENCY = 100;         // Memory access latency
    parameter integer DEFAULT_MEMORY_REFRESH_PERIOD = 7800; // Refresh period (ns)
    parameter integer DEFAULT_MEMORY_ROW_CYCLE_TIME = 50;   // Row cycle time
    parameter integer DEFAULT_MEMORY_COLUMN_CYCLE_TIME = 15; // Column cycle time
    
    // Address mapping configuration
    parameter string  DEFAULT_ADDRESS_MAPPING = "ROW_BANK_COL"; // Address mapping scheme
    parameter logic   ENABLE_ADDRESS_SCRAMBLING = 1'b0;     // Enable address scrambling
    parameter integer DEFAULT_INTERLEAVE_SIZE = 64;         // Interleave size (bytes)
    
    //---------------------------------------------------------------------------
    // 20. FPGA vs ASIC Configuration
    //---------------------------------------------------------------------------
    // Target-specific configuration
    parameter string  DEFAULT_TARGET = "ASIC";               // "ASIC" or "FPGA"
    parameter logic   FPGA_OPTIMIZATIONS = 1'b0;            // Enable FPGA-specific optimizations
    parameter logic   ASIC_OPTIMIZATIONS = 1'b1;            // Enable ASIC-specific optimizations
    
    // FPGA-specific parameters
    parameter integer FPGA_MAX_FREQUENCY_MHZ = 100;         // Maximum FPGA frequency
    parameter logic   FPGA_USE_BLOCK_RAM = 1'b1;            // Use FPGA block RAM
    parameter logic   FPGA_USE_DSP_SLICES = 1'b1;           // Use FPGA DSP slices
    parameter string  FPGA_FAMILY = "ULTRASCALE_PLUS";      // FPGA family
    
    // ASIC-specific parameters  
    parameter integer ASIC_MAX_FREQUENCY_MHZ = 1000;        // Maximum ASIC frequency
    parameter string  ASIC_PROCESS_NODE = "7nm";            // Process node
    parameter string  ASIC_LIBRARY = "TYPICAL";             // Library corner
    parameter integer ASIC_VOLTAGE_MV = 800;                // Operating voltage (mV)
    parameter integer ASIC_TEMPERATURE_C = 25;              // Operating temperature (C)

    //---------------------------------------------------------------------------
    // 16. Cache Topology Configuration (NEW)
    //---------------------------------------------------------------------------
    // Cache topology selection - determines cache clustering strategy
    parameter string DEFAULT_CACHE_TOPOLOGY = "UNIFIED";  // "UNIFIED", "CLUSTERED", "NUMA", "DISTRIBUTED"
    parameter integer DEFAULT_CACHE_CLUSTERS = 1;         // Number of cache clusters
    parameter integer DEFAULT_L2_INSTANCES = 1;           // Number of L2 cache instances
    parameter integer DEFAULT_L3_INSTANCES = 1;           // Number of L3 cache instances
    parameter integer DEFAULT_MEMORY_CONTROLLERS = 1;     // Number of memory controllers
    
    // Cache cluster configuration
    parameter integer DEFAULT_CORES_PER_CLUSTER = 4;      // Cores per cache cluster
    parameter logic   DEFAULT_NUMA_ENABLED = 1'b0;        // NUMA support enabled
    parameter logic   DEFAULT_ADAPTIVE_CLUSTERING = 1'b0; // Dynamic cluster assignment
    
    // Cache interconnect configuration
    parameter string DEFAULT_CACHE_INTERCONNECT = "BUS";   // "BUS", "CROSSBAR", "RING", "MESH"
    parameter integer DEFAULT_INTERCONNECT_WIDTH = 32;     // Interconnect data width
    parameter integer DEFAULT_INTERCONNECT_BANDWIDTH = 100; // Bandwidth in GB/s
    
    // Cache line size calculation helpers
    parameter integer DEFAULT_CACHE_LINE_SIZE_BITS = $clog2(DEFAULT_CACHE_LINE_SIZE); // Cache line offset bits

endpackage : riscv_config_pkg

`default_nettype wire 