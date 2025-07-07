//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V Core
//
// File: riscv_config_pkg.sv
//
// MODULE_NAME: riscv_config_pkg
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 2.1.0
// DATE: 2025-08-01
// DESCRIPTION: Contains all user-configurable parameters for the RISC-V system.
//              This package is the single source of truth for configuration.
//              This file is a result of merging the distributed configuration
//              packages into a single file.
// MODULE_TYPE: Package
//=============================================================================

package riscv_config_pkg;

    // -- Core Architecture --
    parameter int CONFIG_XLEN = 32;
    parameter int CONFIG_ADDR_WIDTH = 32;
    parameter int CONFIG_REG_COUNT = 32;
    parameter int CONFIG_REG_ADDR_WIDTH = $clog2(CONFIG_REG_COUNT);
    parameter int CONFIG_NUM_CORES = 4;
    parameter logic [CONFIG_ADDR_WIDTH-1:0] CONFIG_RESET_VECTOR = 32'h80000000;
    parameter int CONFIG_PIPELINE_STAGES = 5;         // IF, ID, EX, MEM, WB

    // -- Execution Mode --
    parameter string CONFIG_EXECUTION_MODE = "IN_ORDER"; // "IN_ORDER" or "OUT_OF_ORDER"

    // -- Optional Features --
    parameter bit CONFIG_ENABLE_MMU = 1'b1;
    parameter bit CONFIG_ENABLE_FPU = 1'b1;
    parameter bit CONFIG_ENABLE_VPU = 1'b0;
    parameter bit CONFIG_ENABLE_ML_INFERENCE = 1'b0;
    parameter bit CONFIG_ENABLE_BUS_WATCHDOG = 1'b1;
    parameter bit CONFIG_ENABLE_PMU = 1'b1;
    parameter bit CONFIG_ENABLE_L2_CACHE = 1'b1;
    parameter bit CONFIG_ENABLE_L3_CACHE = 1'b1;

    // -- Branch Predictor --
    parameter string CONFIG_BRANCH_PREDICTOR_TYPE = "GSHARE"; // "STATIC", "DYNAMIC", "GSHARE", "TOURNAMENT"
    parameter int CONFIG_BTB_ENTRIES = 512;
    parameter int CONFIG_BHT_ENTRIES = 1024;
    parameter int CONFIG_PHT_ENTRIES = 256;
    parameter int CONFIG_SELECTOR_ENTRIES = 512;
    parameter int CONFIG_GLOBAL_HISTORY_WIDTH = 8;
    parameter int CONFIG_RSB_ENTRIES = 16;
    parameter int CONFIG_NUM_BP_PREDICTORS = 4;
    parameter int CONFIG_BTB_COUNTER_WIDTH = 2;
    parameter int CONFIG_BHT_COUNTER_WIDTH = 2;
    parameter int CONFIG_PHT_COUNTER_WIDTH = 2;
    parameter int CONFIG_SELECTOR_COUNTER_WIDTH = 2;
    parameter int CONFIG_CONFIDENCE_WIDTH = 8;

    // -- Caches --
    parameter int CONFIG_L1_ICACHE_SIZE = 16 * 1024;
    parameter int CONFIG_L1_DCACHE_SIZE = 16 * 1024;
    parameter int CONFIG_L2_CACHE_SIZE = 256 * 1024;
    parameter int CONFIG_L3_CACHE_SIZE = 2 * 1024 * 1024;
    parameter int CONFIG_L1_ICACHE_WAYS = 2;
    parameter int CONFIG_L1_DCACHE_WAYS = 2;
    parameter int CONFIG_L2_CACHE_WAYS = 8;
    parameter int CONFIG_L3_CACHE_WAYS = 16;
    parameter int CONFIG_CACHE_LINE_SIZE = 64;
    parameter int CONFIG_NUM_CACHE_LEVELS = 3;

    // -- Out-of-Order Engine --
    parameter int CONFIG_ROB_SIZE = 32;
    parameter int CONFIG_RS_SIZE = 16;
    parameter int CONFIG_PHYS_REGS = 64;
    parameter int CONFIG_NUM_ALU_UNITS = 2;
    parameter int CONFIG_NUM_MULT_UNITS = 1;
    parameter int CONFIG_NUM_DIV_UNITS = 1;
    parameter int CONFIG_DIV_LATENCY = 32;
    parameter int CONFIG_MULT_LATENCY = 3;

    // -- Out-of-Order Engine Presets --
    parameter int CONFIG_SMALL_ROB_SIZE = 16;
    parameter int CONFIG_SMALL_RS_SIZE = 8;
    parameter int CONFIG_LARGE_ROB_SIZE = 64;
    parameter int CONFIG_LARGE_RS_SIZE = 32;

    // -- Branch Predictor Presets --
    parameter int CONFIG_SMALL_BTB_ENTRIES = 128;
    parameter int CONFIG_SMALL_BHT_ENTRIES = 256;
    parameter int CONFIG_LARGE_BTB_ENTRIES = 1024;
    parameter int CONFIG_LARGE_BHT_ENTRIES = 2048;

    // -- Default Values for Core Components --
    parameter int CONFIG_DEFAULT_PHYS_REGS = 64;
    parameter int CONFIG_DEFAULT_NUM_ALU_UNITS = 2;
    parameter int CONFIG_DEFAULT_NUM_MULT_UNITS = 1;
    parameter int CONFIG_DEFAULT_NUM_DIV_UNITS = 1;
    parameter int CONFIG_DEFAULT_DIV_LATENCY = 32;
    parameter int CONFIG_DEFAULT_PHT_ENTRIES = 256;
    parameter int CONFIG_DEFAULT_SELECTOR_ENTRIES = 512;
    parameter int CONFIG_DEFAULT_GLOBAL_HISTORY_WIDTH = 8;
    parameter int CONFIG_DEFAULT_RSB_ENTRIES = 16;
    parameter int CONFIG_DEFAULT_NUM_CORES = 4;
    parameter string CONFIG_DEFAULT_EXECUTION_MODE = "IN_ORDER";
    parameter string CONFIG_DEFAULT_BRANCH_PREDICTOR_TYPE = "GSHARE";
    parameter string CONFIG_DEFAULT_MEMORY_PROTOCOL = "AXI4";
    parameter int CONFIG_DEFAULT_L1_ICACHE_SIZE = 16 * 1024;
    parameter int CONFIG_DEFAULT_L1_DCACHE_SIZE = 16 * 1024;
    parameter int CONFIG_DEFAULT_L2_CACHE_SIZE = 256 * 1024;
    parameter int CONFIG_DEFAULT_L3_CACHE_SIZE = 2 * 1024 * 1024;
    parameter int CONFIG_DEFAULT_MSG_WIDTH = 32;
    parameter int CONFIG_DEFAULT_NUM_BARRIERS = 8;
    parameter int CONFIG_DEFAULT_AXI4_MAX_OUTSTANDING = 16;
    parameter bit CONFIG_DEFAULT_ENABLE_L2_CACHE = 1'b1;
    parameter bit CONFIG_DEFAULT_ENABLE_L3_CACHE = 1'b1;
    parameter logic [31:0] CONFIG_DEFAULT_RESET_VECTOR = 32'h80000000;
    parameter int CONFIG_DEFAULT_QOS_REQUEST_LEVELS = 8;
    parameter int CONFIG_DEFAULT_VALIDATION_DEPTH = 10;
    parameter int CONFIG_DEFAULT_OPTIMIZATION_WINDOW = 2048;
    parameter int CONFIG_DEFAULT_PERF_MON_MEASUREMENT_WINDOW = 1024;
    parameter int CONFIG_DEFAULT_PERF_MON_IPC_PRECISION = 1000;
    parameter int CONFIG_DEFAULT_MEM_LATENCY = 50;
    parameter int CONFIG_DEFAULT_MEM_BANDWIDTH = 80;
    parameter int CONFIG_DEFAULT_MAX_MSG_QUEUE_DEPTH = 16;
    parameter int CONFIG_DEFAULT_MAX_ATOMIC_OPS = 8;
    parameter int CONFIG_DEFAULT_SYNC_TIMEOUT = 1000;
    parameter int CONFIG_DEFAULT_NETWORK_PACKET_SIZE = 64;
    parameter int CONFIG_DEFAULT_STARVATION_THRESHOLD = 1000;
    parameter int CONFIG_DEFAULT_QOS_URGENCY_BONUS = 100;
    parameter int CONFIG_DEFAULT_QOS_REAL_TIME_BONUS = 200;
    parameter int CONFIG_DEFAULT_CACHE_TOPOLOGY = "UNIFIED";
    parameter int CONFIG_DEFAULT_L2_PREFETCH_DEPTH = 2;
    parameter int CONFIG_DEFAULT_L2_STRIDE_TABLE_SIZE = 16;
    parameter int CONFIG_DEFAULT_L2_PREFETCH_CONFIDENCE_THRESHOLD = 3;
    parameter int CONFIG_DEFAULT_SIM_BRANCH_PREDICTION_ACCURACY = 85;
    parameter int CONFIG_DEFAULT_SIM_PIPELINE_STALL_PENALTY = 3;
    parameter int CONFIG_DEFAULT_SIM_MEMORY_STALL_PENALTY = 10;
    parameter int CONFIG_DEFAULT_SIM_QOS_SATISFACTION_RATE = 85;
    parameter int CONFIG_DEFAULT_ASSERT_MIN_CYCLES_FOR_IPC = 10000;
    parameter int CONFIG_DEFAULT_ASSERT_TARGET_IPC = 800;
    parameter int CONFIG_DEFAULT_ASSERT_MIN_L1_CACHE_HIT_RATE = 700;
    parameter int CONFIG_DEFAULT_ASSERT_MAX_POWER_ESTIMATE = 5000;

    // -- Memory System --
    parameter int CONFIG_STRIDE_TABLE_SIZE = 64;
    parameter int CONFIG_PREFETCH_DISTANCE = 4;
    parameter string CONFIG_MEMORY_PROTOCOL = "AXI4"; // "AXI4", "CHI", "TILELINK"
    parameter int CONFIG_MAX_CACHE_CLUSTERS = 4;
    parameter int CONFIG_MAX_L2_INSTANCES = 4;
    parameter int CONFIG_MAX_L3_INSTANCES = 2;
    parameter int CONFIG_MAX_MEMORY_CONTROLLERS = 2;

    // -- Memory Protocols --
    // AXI4
    parameter int CONFIG_AXI4_ID_WIDTH = 4;
    parameter int CONFIG_AXI4_ADDR_WIDTH = 32;
    parameter int CONFIG_AXI4_DATA_WIDTH = 32;
    parameter int CONFIG_AXI4_USER_WIDTH = 1;
    parameter int CONFIG_AXI4_MAX_OUTSTANDING = 16;
    // CHI
    parameter int CONFIG_CHI_DATA_WIDTH = 128;
    parameter int CONFIG_CHI_ADDR_WIDTH = 48;
    parameter int CONFIG_CHI_NODEID_WIDTH = 7;
    parameter int CONFIG_CHI_TXNID_WIDTH = 8;
    // TileLink
    parameter int CONFIG_TL_DATA_WIDTH = 64;
    parameter int CONFIG_TL_ADDR_WIDTH = 32;
    parameter int CONFIG_TL_SOURCE_WIDTH = 4;
    parameter int CONFIG_TL_SINK_WIDTH = 4;
    parameter int CONFIG_TL_SIZE_WIDTH = 4;

    // -- Inter-core communication --
    parameter int CONFIG_MSG_WIDTH = 32;
    parameter int CONFIG_NUM_BARRIERS = 8;

    // -- SoC --
    parameter int CONFIG_MAX_CORES = 4;
    parameter int CONFIG_ECC_WIDTH = 8;
    parameter int CONFIG_PARITY_WIDTH = 1;
    // Debug
    parameter int CONFIG_DEBUG_REGISTERS = 8;
    parameter int CONFIG_BREAKPOINTS = 4;
    parameter int CONFIG_WATCHPOINTS = 4;
    parameter int CONFIG_DEBUG_CHANNELS = 16;
    // Power
    parameter int CONFIG_POWER_DOMAINS = 2;
    parameter int CONFIG_CLOCK_DOMAINS = 1;
    // QoS
    parameter int CONFIG_QOS_LEVELS = 8;

    // -- Verification --
    parameter int CONFIG_CLK_PERIOD = 10;
    parameter int CONFIG_TIMEOUT_CYCLES = 1000;
    parameter int CONFIG_BUS_TIMEOUT_CYCLES = 5000;
    parameter int CONFIG_MAX_TEST_ITERATIONS = 100;
    parameter int CONFIG_TARGET_FREQ_ASIC = 1000;
    parameter int CONFIG_TARGET_FREQ_FPGA = 100;
    parameter int CONFIG_PERF_MON_WINDOW   = 1024; // Cycles in measurement window
    parameter int CONFIG_PERF_COUNTER_WIDTH = 32;   // Width of performance counters
    parameter int CONFIG_IPC_PRECISION     = 1000; // IPC calculation precision multiplier
    parameter int CONFIG_OPT_WINDOW               = 2048; // Cycles for optimization window
    parameter int CONFIG_IPC_TARGET               = 85;   // Target IPC percentage
    parameter int CONFIG_CACHE_MISS_THRESHOLD     = 15;   // Cache miss rate threshold (percent)
    parameter int CONFIG_BRANCH_MISS_THRESHOLD    = 10;   // Branch misprediction rate threshold (percent)
    parameter int CONFIG_PIPELINE_STALL_THRESHOLD = 20;   // Pipeline stall rate threshold (percent)

    //---------------------------------------------------------------------------
    // Memory Address Map Configuration
    //---------------------------------------------------------------------------
    parameter logic [31:0] CONFIG_EXCEPTION_VECTOR_BASE = 32'h0000_0000;
    parameter logic [31:0] CONFIG_EXCEPTION_VECTOR_SIZE = 32'h0000_1000;    // 4KB exception vector space
    parameter logic [31:0] CONFIG_PERIPHERAL_BASE = 32'hF000_0000;
    parameter logic [31:0] CONFIG_PERIPHERAL_SIZE = 32'h1000_0000;          // 256MB peripheral space
    parameter logic [31:0] CONFIG_CACHE_WB_BASE = 32'hFFFF_FF00;
    parameter logic [31:0] CONFIG_CACHE_WB_SIZE = 32'h0000_0100;            // 256B cache writeback region
    parameter logic [31:0] CONFIG_MAIN_MEMORY_BASE = 32'h1000_0000;
    parameter logic [31:0] CONFIG_MAIN_MEMORY_SIZE = 32'hE000_0000;         // ~3.5GB main memory

    //---------------------------------------------------------------------------
    // CSR Address Configuration
    //---------------------------------------------------------------------------
    // QoS CSR address range (Custom CSR space)
    parameter logic [11:0] CONFIG_QOS_CSR_BASE = 12'hBC0;                  // Base address for QoS CSRs
    parameter logic [11:0] CONFIG_QOS_CSR_END = 12'hBDF;                   // End address for QoS CSRs
    // Individual QoS CSR addresses
    parameter logic [11:0] CONFIG_CSR_QOS_CONTROL = 12'hBC0;               // Global QoS control
    parameter logic [11:0] CONFIG_CSR_QOS_STATUS = 12'hBC1;                // QoS status register
    parameter logic [11:0] CONFIG_CSR_QOS_VIOLATIONS = 12'hBC2;            // QoS violation count
    parameter logic [11:0] CONFIG_CSR_QOS_REQUESTS = 12'hBC3;              // Total request count
    // Per-core QoS configuration CSRs (0xBC4-0xBC7)
    parameter logic [11:0] CONFIG_CSR_QOS_CORE0_CFG = 12'hBC4;             // Core 0 QoS config
    parameter logic [11:0] CONFIG_CSR_QOS_CORE1_CFG = 12'hBC5;             // Core 1 QoS config
    parameter logic [11:0] CONFIG_CSR_QOS_CORE2_CFG = 12'hBC6;             // Core 2 QoS config
    parameter logic [11:0] CONFIG_CSR_QOS_CORE3_CFG = 12'hBC7;             // Core 3 QoS config
    // QoS performance monitoring CSRs
    parameter logic [11:0] CONFIG_CSR_QOS_PERF_BASE = 12'hBC8;             // Base for performance CSRs
    // QoS bandwidth allocation CSRs (0xBD0-0xBD3)
    parameter logic [11:0] CONFIG_CSR_QOS_BW_CORE0 = 12'hBD0;              // Core 0 bandwidth
    parameter logic [11:0] CONFIG_CSR_QOS_BW_CORE1 = 12'hBD1;              // Core 1 bandwidth
    parameter logic [11:0] CONFIG_CSR_QOS_BW_CORE2 = 12'hBD2;              // Core 2 bandwidth
    parameter logic [11:0] CONFIG_CSR_QOS_BW_CORE3 = 12'hBD3;              // Core 3 bandwidth
    // QoS debug and monitoring CSRs
    parameter logic [11:0] CONFIG_CSR_QOS_DEBUG = 12'hBD4;                 // Debug control
    parameter logic [11:0] CONFIG_CSR_QOS_MONITOR = 12'hBD5;               // Monitoring control

    // PMU CSR addresses
    parameter logic [11:0] CONFIG_PMU_ENABLE_ADDR = 12'hF00;
    parameter logic [11:0] CONFIG_PMU_CONFIG_ADDR = 12'hF01;
    parameter logic [11:0] CONFIG_PMU_IDLE_TIMEOUT_ADDR = 12'hF02;
    parameter logic [11:0] CONFIG_PMU_SLEEP_TIMEOUT_ADDR = 12'hF03;

    //---------------------------------------------------------------------------
    // QoS Configuration
    //---------------------------------------------------------------------------
    parameter int CONFIG_QOS_WEIGHT_CRITICAL     = 100;
    parameter int CONFIG_QOS_WEIGHT_HIGH         = 50;
    parameter int CONFIG_QOS_WEIGHT_MEDIUM_HIGH  = 25;
    parameter int CONFIG_QOS_WEIGHT_MEDIUM       = 10;
    parameter int CONFIG_QOS_WEIGHT_LOW          = 1;
    parameter int CONFIG_QOS_INSTR_LATENCY_CRITICAL    = 10;
    parameter int CONFIG_QOS_INSTR_LATENCY_NORMAL      = 50;
    parameter int CONFIG_QOS_DATA_LATENCY_CRITICAL     = 10;
    parameter int CONFIG_QOS_DATA_STORE_LATENCY_NORMAL = 100;
    parameter int CONFIG_QOS_DATA_LOAD_LATENCY_NORMAL  = 60;
    parameter int CONFIG_QOS_INSTR_BW_PERCENT = 50; // Guaranteed bandwidth % for instructions
    parameter int CONFIG_QOS_DATA_BW_PERCENT  = 50; // Guaranteed bandwidth % for data
    parameter int CONFIG_QOS_INSTR_RETRY_LIMIT = 5;
    parameter int CONFIG_QOS_DATA_RETRY_LIMIT  = 5;

    parameter int CONFIG_QOS_DEBUG_LATENCY = 5;
    parameter int CONFIG_QOS_EXCEPTION_LATENCY = 10;
    parameter int CONFIG_QOS_ECALL_LATENCY = 15;
    parameter int CONFIG_QOS_DEFAULT_EXCEPTION_LATENCY = 20;

    // -- VPU --
    parameter int CONFIG_MAX_VECTOR_LENGTH = 8;

    //---------------------------------------------------------------------------
    // Power Management Configuration
    //---------------------------------------------------------------------------
    parameter logic [2:0] CONFIG_VOLTAGE_LEVEL_MIN = 3'b001;               // Minimum voltage
    parameter logic [2:0] CONFIG_VOLTAGE_LEVEL_LOW = 3'b010;               // Low voltage
    parameter logic [2:0] CONFIG_VOLTAGE_LEVEL_MID = 3'b100;               // Mid voltage (default)
    parameter logic [2:0] CONFIG_VOLTAGE_LEVEL_HIGH = 3'b110;              // High voltage
    parameter logic [2:0] CONFIG_VOLTAGE_LEVEL_MAX = 3'b111;               // Maximum voltage
    parameter logic [3:0] CONFIG_FREQUENCY_LEVEL_MIN = 4'h2;               // Minimum frequency
    parameter logic [3:0] CONFIG_FREQUENCY_LEVEL_LOW = 4'h4;               // Low frequency
    parameter logic [3:0] CONFIG_FREQUENCY_LEVEL_MID = 4'h8;               // Mid frequency (default)
    parameter logic [3:0] CONFIG_FREQUENCY_LEVEL_HIGH = 4'hC;              // High frequency
    parameter logic [3:0] CONFIG_FREQUENCY_LEVEL_MAX = 4'hF;               // Maximum frequency
    parameter int CONFIG_THERMAL_THROTTLE_PERFORMANCE = 32;            // Low performance for thermal safety
    parameter int CONFIG_HIGH_CACHE_MISS_PERFORMANCE = 224;            // High performance for memory-bound (0xE0)
    parameter int CONFIG_CACHE_MISS_THRESHOLD_PERCENT = 50;            // Cache miss threshold for performance scaling
    parameter int CONFIG_PERFORMANCE_DEMAND_MASK = 8'hF0;              // Mask for performance demand upper nibble
    parameter int CONFIG_L3_CACHE_GATING_THRESHOLD = 10;               // L3 cache miss rate threshold for gating

    //---------------------------------------------------------------------------
    // Configuration Validation Functions
    //---------------------------------------------------------------------------
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

    function automatic integer calc_cache_sets(
        input integer cache_size,
        input integer line_size,
        input integer ways
    );
        return cache_size / (line_size * ways);
    endfunction

endpackage