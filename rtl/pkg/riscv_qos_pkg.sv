//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: riscv_qos_pkg.sv
// Package: riscv_qos_pkg
//
// Project Name: RISC-V RV32IM QoS Management
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Production Ready
//
// Description:
//   Comprehensive Quality of Service (QoS) package for RISC-V multi-core
//   system. Defines QoS levels, arbitration policies, bandwidth allocation,
//   and latency guarantees for optimal system performance.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_qos_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    //---------------------------------------------------------------------------
    // 1. QoS Level Definitions
    //---------------------------------------------------------------------------
    
    // AXI4 QoS Levels (4-bit field allows 16 levels)
    parameter logic [3:0] QOS_LEVEL_CRITICAL    = 4'hF;  // Highest priority - Debug, Exceptions
    parameter logic [3:0] QOS_LEVEL_HIGH        = 4'hC;  // High priority - CPU instruction fetches
    parameter logic [3:0] QOS_LEVEL_MEDIUM_HIGH = 4'h8;  // Medium-high - CPU data access
    parameter logic [3:0] QOS_LEVEL_MEDIUM      = 4'h6;  // Medium - L2 cache operations  
    parameter logic [3:0] QOS_LEVEL_MEDIUM_LOW  = 4'h4;  // Medium-low - L3 cache operations
    parameter logic [3:0] QOS_LEVEL_LOW         = 4'h2;  // Low priority - Background operations
    parameter logic [3:0] QOS_LEVEL_BEST_EFFORT = 4'h1;  // Best effort - DMA, peripheral access
    parameter logic [3:0] QOS_LEVEL_NONE        = 4'h0;  // No QoS control
    
    //---------------------------------------------------------------------------
    // 2. QoS Transaction Types
    //---------------------------------------------------------------------------
    
    typedef enum logic [3:0] {
        QOS_TYPE_DEBUG          = 4'h0,  // Debug access - highest priority
        QOS_TYPE_EXCEPTION      = 4'h1,  // Exception handling - critical
        QOS_TYPE_INSTR_FETCH    = 4'h2,  // Instruction fetch - high priority
        QOS_TYPE_DATA_ACCESS    = 4'h3,  // Data access - medium-high priority  
        QOS_TYPE_CACHE_FILL     = 4'h4,  // Cache line fill - medium priority
        QOS_TYPE_CACHE_WB       = 4'h5,  // Cache writeback - medium-low priority
        QOS_TYPE_PREFETCH       = 4'h6,  // Prefetch operations - low priority
        QOS_TYPE_DMA            = 4'h7,  // DMA transfers - best effort
        QOS_TYPE_PERIPHERAL     = 4'h8,  // Peripheral access - best effort
        QOS_TYPE_MAINTENANCE    = 4'h9,  // Cache maintenance - low priority
        QOS_TYPE_BACKGROUND     = 4'hA,  // Background tasks - best effort
        QOS_TYPE_TEST           = 4'hB,  // Test/verification - configurable
        QOS_TYPE_RESERVED_C     = 4'hC,  // Reserved for future use
        QOS_TYPE_RESERVED_D     = 4'hD,  // Reserved for future use
        QOS_TYPE_RESERVED_E     = 4'hE,  // Reserved for future use
        QOS_TYPE_USER_DEFINED   = 4'hF   // User-defined QoS type
    } qos_transaction_type_e;

    //---------------------------------------------------------------------------
    // 3. QoS Arbitration Policies
    //---------------------------------------------------------------------------
    
    typedef enum logic [2:0] {
        QOS_ARBITER_ROUND_ROBIN    = 3'h0,  // Round-robin arbitration
        QOS_ARBITER_STRICT_PRIO    = 3'h1,  // Strict priority arbitration
        QOS_ARBITER_WEIGHTED_RR    = 3'h2,  // Weighted round-robin
        QOS_ARBITER_LOTTERY        = 3'h3,  // Lottery-based arbitration
        QOS_ARBITER_FAIR_QUEUING   = 3'h4,  // Fair queuing arbitration
        QOS_ARBITER_DEFICIT_RR     = 3'h5,  // Deficit round-robin
        QOS_ARBITER_PRIORITY_RR    = 3'h6,  // Priority + round-robin hybrid
        QOS_ARBITER_ADAPTIVE       = 3'h7   // Adaptive arbitration
    } qos_arbiter_policy_e;

    //---------------------------------------------------------------------------
    // 4. QoS Configuration Structure
    //---------------------------------------------------------------------------
    
    typedef struct packed {
        logic [3:0]              qos_level;           // QoS priority level (0-15)
        qos_transaction_type_e   transaction_type;    // Type of transaction
        logic                    urgent;              // Urgent flag for critical transactions
        logic                    guaranteed_bw;       // Guaranteed bandwidth allocation
        logic [7:0]              weight;              // Weight for weighted arbitration (0-255)
        logic [15:0]             max_latency_cycles;  // Maximum allowed latency (cycles)
        logic [7:0]              bandwidth_percent;   // Allocated bandwidth percentage (0-100)
        logic [3:0]              core_id;             // Originating core ID
        logic                    preemptable;         // Can be preempted by higher priority
        logic                    real_time;           // Real-time transaction
        logic [2:0]              retry_limit;         // Maximum retry attempts
        logic                    ordered;             // Must maintain ordering
    } qos_config_t;

    //---------------------------------------------------------------------------
    // 5. QoS Performance Monitoring
    //---------------------------------------------------------------------------
    
    typedef struct packed {
        logic [31:0]             transaction_count;   // Total transactions for this QoS level
        logic [31:0]             bytes_transferred;   // Total bytes transferred
        logic [31:0]             avg_latency;         // Average latency (cycles)
        logic [31:0]             max_latency;         // Maximum observed latency
        logic [31:0]             min_latency;         // Minimum observed latency
        logic [31:0]             violation_count;     // QoS violations (latency exceeded)
        logic [31:0]             bandwidth_utilization; // Bandwidth utilization percentage
        logic [31:0]             preemption_count;    // Times preempted by higher priority
        logic [31:0]             starvation_cycles;   // Cycles spent waiting due to starvation
        logic [31:0]             deadline_misses;     // Deadline miss count
    } qos_performance_t;

    //---------------------------------------------------------------------------
    // 6. QoS Transaction Request Structure
    //---------------------------------------------------------------------------
    
    typedef struct packed {
        logic                    valid;               // Request valid
        qos_config_t             qos_config;          // QoS configuration
        logic [ADDR_WIDTH-1:0]   address;             // Transaction address
        logic [XLEN-1:0]         data;                // Transaction data
        logic [XLEN/8-1:0]       strobe;              // Byte strobe
        logic                    write;               // Write transaction
        logic [2:0]              size;                // Transaction size
        logic [15:0]             transaction_id;      // Unique transaction ID
        logic [31:0]             timestamp;           // Request timestamp
        logic [15:0]             deadline;            // Deadline (relative cycles)
        logic [7:0]              burst_length;        // Burst length
        logic                    cacheable;           // Cacheable transaction
        logic [2:0]              prot;                // Protection attributes
    } qos_request_t;

    //---------------------------------------------------------------------------
    // 7. QoS Arbitration State
    //---------------------------------------------------------------------------
    
    typedef struct packed {
        qos_arbiter_policy_e     policy;              // Current arbitration policy
        logic [3:0]              current_winner;      // Current winning QoS level
        logic [7:0]              round_robin_ptr;     // Round-robin pointer
        logic [31:0]             deficit_counters [16]; // Deficit counters for DRR
        logic [15:0]             weights [16];        // Weights for each QoS level
        logic [31:0]             bandwidth_allocated [16]; // Allocated bandwidth per level
        logic [31:0]             bandwidth_used [16]; // Used bandwidth per level
        logic [15:0]             active_mask;         // Mask of active QoS levels
        logic [31:0]             arbitration_cycle;   // Current arbitration cycle
        logic                    emergency_mode;      // Emergency arbitration mode
    } qos_arbiter_state_t;

    //---------------------------------------------------------------------------
    // 8. QoS Configuration Registers
    //---------------------------------------------------------------------------
    
    // QoS Control Register
    typedef struct packed {
        logic [15:0]             reserved;            // Reserved bits [31:16]
        logic [3:0]              max_qos_level;       // Maximum QoS level supported [15:12]
        qos_arbiter_policy_e     arbiter_policy;      // Arbitration policy [11:9]
        logic                    qos_enable;          // Global QoS enable [8]
        logic                    emergency_enable;    // Emergency mode enable [7]
        logic                    monitoring_enable;   // Performance monitoring enable [6]
        logic                    bandwidth_control;   // Bandwidth control enable [5]
        logic                    latency_control;     // Latency control enable [4]
        logic                    preemption_enable;   // Preemption enable [3]
        logic                    real_time_mode;      // Real-time mode enable [2]
        logic                    starvation_prevent;  // Starvation prevention [1]
        logic                    reset_counters;      // Reset performance counters [0]
    } qos_control_reg_t;

    //---------------------------------------------------------------------------
    // 9. Default QoS Configurations
    //---------------------------------------------------------------------------
    
    // QoS level mapping for transaction types (commonly used function)
    function automatic logic [3:0] get_qos_level(qos_transaction_type_e txn_type);
        return get_default_qos_level(txn_type);
    endfunction
    
    // Default QoS mapping for different transaction types
    function automatic logic [3:0] get_default_qos_level(qos_transaction_type_e txn_type);
        case (txn_type)
            QOS_TYPE_DEBUG:         return QOS_LEVEL_CRITICAL;
            QOS_TYPE_EXCEPTION:     return QOS_LEVEL_CRITICAL;
            QOS_TYPE_INSTR_FETCH:   return QOS_LEVEL_HIGH;
            QOS_TYPE_DATA_ACCESS:   return QOS_LEVEL_MEDIUM_HIGH;
            QOS_TYPE_CACHE_FILL:    return QOS_LEVEL_MEDIUM;
            QOS_TYPE_CACHE_WB:      return QOS_LEVEL_MEDIUM_LOW;
            QOS_TYPE_PREFETCH:      return QOS_LEVEL_LOW;
            QOS_TYPE_DMA:           return QOS_LEVEL_BEST_EFFORT;
            QOS_TYPE_PERIPHERAL:    return QOS_LEVEL_BEST_EFFORT;
            QOS_TYPE_MAINTENANCE:   return QOS_LEVEL_LOW;
            QOS_TYPE_BACKGROUND:    return QOS_LEVEL_BEST_EFFORT;
            QOS_TYPE_TEST:          return QOS_LEVEL_MEDIUM;
            default:                return QOS_LEVEL_NONE;
        endcase
    endfunction

    // Default bandwidth allocation percentages
    function automatic logic [7:0] get_default_bandwidth_percent(logic [3:0] qos_level);
        case (qos_level)
            QOS_LEVEL_CRITICAL:     return 8'd30;  // 30% for critical
            QOS_LEVEL_HIGH:         return 8'd25;  // 25% for high priority
            QOS_LEVEL_MEDIUM_HIGH:  return 8'd20;  // 20% for medium-high
            QOS_LEVEL_MEDIUM:       return 8'd15;  // 15% for medium
            QOS_LEVEL_MEDIUM_LOW:   return 8'd5;   // 5% for medium-low
            QOS_LEVEL_LOW:          return 8'd3;   // 3% for low priority
            QOS_LEVEL_BEST_EFFORT:  return 8'd2;   // 2% for best effort
            default:                return 8'd0;   // 0% for no QoS
        endcase
    endfunction

    // Default maximum latency in cycles
    function automatic logic [15:0] get_default_max_latency(logic [3:0] qos_level);
        case (qos_level)
            QOS_LEVEL_CRITICAL:     return 16'd10;   // 10 cycles for critical
            QOS_LEVEL_HIGH:         return 16'd25;   // 25 cycles for high priority
            QOS_LEVEL_MEDIUM_HIGH:  return 16'd50;   // 50 cycles for medium-high
            QOS_LEVEL_MEDIUM:       return 16'd100;  // 100 cycles for medium
            QOS_LEVEL_MEDIUM_LOW:   return 16'd200;  // 200 cycles for medium-low
            QOS_LEVEL_LOW:          return 16'd500;  // 500 cycles for low priority
            QOS_LEVEL_BEST_EFFORT:  return 16'd1000; // 1000 cycles for best effort
            default:                return 16'd65535; // No limit for no QoS
        endcase
    endfunction

    //---------------------------------------------------------------------------
    // 10. QoS Configuration Parameters
    //---------------------------------------------------------------------------
    
    // Global QoS configuration
    parameter logic QOS_ENABLE_DEFAULT              = CONFIG_QOS_ENABLE_DEFAULT;      // Enable QoS by default
    parameter qos_arbiter_policy_e QOS_DEFAULT_POLICY = CONFIG_QOS_DEFAULT_POLICY; // Default policy
    parameter integer QOS_MAX_LEVELS               = CONFIG_QOS_MAX_LEVELS;        // Maximum QoS levels
    parameter integer QOS_PERFORMANCE_HISTORY      = CONFIG_QOS_PERFORMANCE_HISTORY;        // Performance history depth
    parameter integer QOS_BANDWIDTH_UPDATE_CYCLES  = CONFIG_QOS_BANDWIDTH_UPDATE_CYCLES;      // Bandwidth measurement period
    parameter integer QOS_LATENCY_MONITOR_DEPTH    = CONFIG_QOS_LATENCY_MONITOR_DEPTH;        // Latency monitoring depth
    parameter integer QOS_STARVATION_THRESHOLD     = CONFIG_QOS_STARVATION_THRESHOLD;     // Starvation prevention threshold
    parameter integer QOS_EMERGENCY_THRESHOLD      = CONFIG_QOS_EMERGENCY_THRESHOLD;        // Emergency mode threshold (% violations)
    
    // QoS arbitration weights (higher = more bandwidth)
    parameter logic [7:0] QOS_WEIGHT_CRITICAL       = CONFIG_QOS_WEIGHT_CRITICAL;   // Maximum weight
    parameter logic [7:0] QOS_WEIGHT_HIGH           = CONFIG_QOS_WEIGHT_HIGH;   // High weight
    parameter logic [7:0] QOS_WEIGHT_MEDIUM_HIGH    = CONFIG_QOS_WEIGHT_MEDIUM_HIGH;   // Medium-high weight
    parameter logic [7:0] QOS_WEIGHT_MEDIUM         = CONFIG_QOS_WEIGHT_MEDIUM;   // Medium weight
    parameter logic [7:0] QOS_WEIGHT_MEDIUM_LOW     = CONFIG_QOS_WEIGHT_MEDIUM_LOW;    // Medium-low weight
    parameter logic [7:0] QOS_WEIGHT_LOW            = CONFIG_QOS_WEIGHT_LOW;    // Low weight
    parameter logic [7:0] QOS_WEIGHT_BEST_EFFORT    = CONFIG_QOS_WEIGHT_BEST_EFFORT;    // Minimum weight
    parameter logic [7:0] QOS_WEIGHT_NONE           = CONFIG_QOS_WEIGHT_NONE;     // Minimal weight

    parameter qos_arbiter_policy_e DEFAULT_QOS_ARBITER_POLICY = CONFIG_DEFAULT_QOS_ARBITER_POLICY;
    parameter logic [3:0] DEFAULT_QOS_LEVEL_MEDIUM_HIGH = QOS_LEVEL_MEDIUM_HIGH;
    parameter logic [7:0] DEFAULT_QOS_WEIGHT = CONFIG_QOS_WEIGHT_MEDIUM_HIGH;
    parameter logic [15:0] DEFAULT_QOS_LATENCY_LIMIT = CONFIG_QOS_DATA_LOAD_LATENCY_NORMAL;
    parameter logic [7:0] DEFAULT_QOS_BW_ALLOC = 8'd25;

    parameter logic [15:0] QOS_INSTR_LATENCY_CRITICAL = CONFIG_QOS_INSTR_LATENCY_CRITICAL;
    parameter logic [15:0] QOS_INSTR_LATENCY_NORMAL = CONFIG_QOS_INSTR_LATENCY_NORMAL;
    parameter logic [7:0] QOS_INSTR_BW_PERCENT = CONFIG_QOS_INSTR_BW_PERCENT;
    parameter logic [2:0] QOS_INSTR_RETRY_LIMIT = CONFIG_QOS_INSTR_RETRY_LIMIT;

    parameter logic [15:0] QOS_DATA_LATENCY_CRITICAL = CONFIG_QOS_DATA_LATENCY_CRITICAL;
    parameter logic [15:0] QOS_DATA_STORE_LATENCY_NORMAL = CONFIG_QOS_DATA_STORE_LATENCY_NORMAL;
    parameter logic [15:0] QOS_DATA_LOAD_LATENCY_NORMAL = CONFIG_QOS_DATA_LOAD_LATENCY_NORMAL;
    parameter logic [7:0] QOS_DATA_BW_PERCENT = CONFIG_QOS_DATA_BW_PERCENT;
    parameter logic [2:0] QOS_DATA_RETRY_LIMIT = CONFIG_QOS_DATA_RETRY_LIMIT;

    //---------------------------------------------------------------------------
    // 11. QoS Helper Functions
    //---------------------------------------------------------------------------
    
    // Check if QoS level is real-time
    function automatic logic is_real_time_qos(logic [3:0] qos_level);
        return (qos_level >= QOS_LEVEL_MEDIUM_HIGH);
    endfunction
    
    // Check if QoS level allows preemption
    function automatic logic is_preemptable_qos(logic [3:0] qos_level);
        return (qos_level < QOS_LEVEL_HIGH);
    endfunction
    
    // Get arbitration weight for QoS level
    function automatic logic [7:0] get_qos_weight(logic [3:0] qos_level);
        case (qos_level)
            QOS_LEVEL_CRITICAL:     return QOS_WEIGHT_CRITICAL;
            QOS_LEVEL_HIGH:         return QOS_WEIGHT_HIGH;
            QOS_LEVEL_MEDIUM_HIGH:  return QOS_WEIGHT_MEDIUM_HIGH;
            QOS_LEVEL_MEDIUM:       return QOS_WEIGHT_MEDIUM;
            QOS_LEVEL_MEDIUM_LOW:   return QOS_WEIGHT_MEDIUM_LOW;
            QOS_LEVEL_LOW:          return QOS_WEIGHT_LOW;
            QOS_LEVEL_BEST_EFFORT:  return QOS_WEIGHT_BEST_EFFORT;
            default:                return QOS_WEIGHT_NONE;
        endcase
    endfunction
    
    // Calculate priority score for arbitration
    function automatic logic [31:0] calculate_priority_score(
        logic [3:0] qos_level,
        logic [31:0] wait_time,
        logic [7:0] weight,
        logic urgent
    );
        logic [31:0] base_priority;
        logic [31:0] urgency_bonus;
        logic [31:0] aging_bonus;
        
        base_priority = {28'h0, qos_level} * 1000000; // Base priority from QoS level
        urgency_bonus = urgent ? 500000 : 0;          // Urgent transaction bonus
        aging_bonus = wait_time * weight;             // Anti-starvation aging
        
        return base_priority + urgency_bonus + aging_bonus;
    endfunction

endpackage : riscv_qos_pkg

//=============================================================================
// Usage Examples:
//
// import riscv_qos_pkg::*;
//
// // Configure QoS for instruction fetch
// qos_config_t instr_qos;
// instr_qos.qos_level = QOS_LEVEL_HIGH;
// instr_qos.transaction_type = QOS_TYPE_INSTR_FETCH;
// instr_qos.urgent = 1'b0;
// instr_qos.weight = QOS_WEIGHT_HIGH;
// instr_qos.max_latency_cycles = get_default_max_latency(QOS_LEVEL_HIGH);
//
// // Set AXI4 QoS based on configuration
// assign axi_if.awqos = instr_qos.qos_level;
// assign axi_if.arqos = instr_qos.qos_level;
//
//=============================================================================

`default_nettype wire 