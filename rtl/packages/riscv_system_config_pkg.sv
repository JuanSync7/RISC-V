//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: riscv_system_config_pkg.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: riscv_system_config_pkg
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-28
// DESCRIPTION: Top-level system configuration package with profile selection.
// PRIMARY_PURPOSE: Provide unified configuration interface for the entire system.
// ROLE_IN_SYSTEM: Central configuration hub that selects and validates profiles.
// PROBLEM_SOLVED: Enables easy switching between different system configurations.
// MODULE_TYPE: Package
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V RV32IM
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

package riscv_system_config_pkg;

    import riscv_base_pkg::*;
    import riscv_cache_config_pkg::*;

    //-------------------------------------------------------------------------
    // Profile Selection
    //-------------------------------------------------------------------------
    // AI_TAG: FEATURE - Centralized profile selection mechanism
    
    // Select profile via compile-time define or parameter
    `ifdef PROFILE_SMALL
        import riscv_profile_small::*;
        localparam string SELECTED_PROFILE = "SMALL";
    `elsif PROFILE_LARGE
        import riscv_profile_large::*;
        localparam string SELECTED_PROFILE = "LARGE";
    `elsif PROFILE_CUSTOM
        import riscv_profile_custom::*;
        localparam string SELECTED_PROFILE = "CUSTOM";
    `else
        // Default to medium profile
        import riscv_profile_medium::*;
        localparam string SELECTED_PROFILE = "MEDIUM";
    `endif
    
    //-------------------------------------------------------------------------
    // System-Wide Type Definitions
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - Core configuration structure
    typedef struct packed {
        logic [31:0] core_id;
        logic [31:0] reset_vector;
        logic [7:0]  num_cores;
        logic [2:0]  execution_mode;  // IN_ORDER, OUT_OF_ORDER
        logic        m_extension;
        logic        c_extension;
        logic        f_extension;
    } core_config_t;
    
    // AI_TAG: PARAM_DESC - Memory system configuration structure  
    typedef struct packed {
        cache_config_t    l1_icache;
        cache_config_t    l1_dcache;
        cache_config_t    l2_cache;
        cache_config_t    l3_cache;
        coherency_config_t coherency;
        logic             l2_enable;
        logic             l3_enable;
    } memory_config_t;
    
    // AI_TAG: PARAM_DESC - System configuration structure
    typedef struct packed {
        core_config_t   core;
        memory_config_t memory;
        logic [2:0]     memory_protocol;  // AXI4, CHI, TILELINK
        logic [31:0]    target_frequency;
        logic           debug_enable;
        logic           trace_enable;
    } system_config_t;
    
    //-------------------------------------------------------------------------
    // Execution Mode Encoding
    //-------------------------------------------------------------------------
    typedef enum logic [2:0] {
        EXEC_MODE_IN_ORDER     = 3'b000,
        EXEC_MODE_OUT_OF_ORDER = 3'b001,
        EXEC_MODE_SUPERSCALAR  = 3'b010,  // Future
        EXEC_MODE_VLIW         = 3'b011   // Future
    } execution_mode_e;
    
    // Memory protocol encoding
    typedef enum logic [2:0] {
        MEM_PROTOCOL_AXI4      = 3'b000,
        MEM_PROTOCOL_AXI4_LITE = 3'b001,
        MEM_PROTOCOL_CHI       = 3'b010,
        MEM_PROTOCOL_TILELINK  = 3'b011,
        MEM_PROTOCOL_CUSTOM    = 3'b100
    } memory_protocol_e;
    
    //-------------------------------------------------------------------------
    // Build System Configuration from Selected Profile
    //-------------------------------------------------------------------------
    // AI_TAG: PARAM_DESC - System configuration built from selected profile
    
    // Convert string execution mode to enum
    function automatic execution_mode_e get_execution_mode();
        case (CONFIG_EXECUTION_MODE)
            "IN_ORDER":      return EXEC_MODE_IN_ORDER;
            "OUT_OF_ORDER":  return EXEC_MODE_OUT_OF_ORDER;
            default:         return EXEC_MODE_IN_ORDER;
        endcase
    endfunction
    
    // Convert string memory protocol to enum
    function automatic memory_protocol_e get_memory_protocol();
        case (CONFIG_MEMORY_PROTOCOL)
            "AXI4":      return MEM_PROTOCOL_AXI4;
            "AXI4_LITE": return MEM_PROTOCOL_AXI4_LITE;
            "CHI":       return MEM_PROTOCOL_CHI;
            "TILELINK":  return MEM_PROTOCOL_TILELINK;
            default:     return MEM_PROTOCOL_AXI4;
        endcase
    endfunction
    
    // Build core configuration
    parameter core_config_t DEFAULT_CORE_CONFIG = '{
        core_id:        0,
        reset_vector:   CONFIG_RESET_VECTOR,
        num_cores:      CONFIG_NUM_CORES,
        execution_mode: get_execution_mode(),
        m_extension:    CONFIG_M_EXTENSION,
        c_extension:    CONFIG_C_EXTENSION,
        f_extension:    CONFIG_F_EXTENSION
    };
    
    // Build memory configuration
    parameter memory_config_t DEFAULT_MEMORY_CONFIG = '{
        l1_icache:  CONFIG_L1_ICACHE,
        l1_dcache:  CONFIG_L1_DCACHE,
        l2_cache:   CONFIG_L2_CACHE,
        l3_cache:   CONFIG_L3_CACHE,
        coherency:  CONFIG_COHERENCY,
        l2_enable:  CONFIG_L2_ENABLE,
        l3_enable:  CONFIG_L3_ENABLE
    };
    
    // Build complete system configuration
    parameter system_config_t DEFAULT_SYSTEM_CONFIG = '{
        core:             DEFAULT_CORE_CONFIG,
        memory:           DEFAULT_MEMORY_CONFIG,
        memory_protocol:  get_memory_protocol(),
        target_frequency: CONFIG_TARGET_FREQUENCY_MHZ * 1_000_000,
        debug_enable:     CONFIG_DEBUG_ENABLE,
        trace_enable:     CONFIG_TRACE_ENABLE
    };
    
    //-------------------------------------------------------------------------
    // Configuration Override Mechanism
    //-------------------------------------------------------------------------
    // AI_TAG: FEATURE - Allow parameter overrides while maintaining defaults
    
    // Override examples (can be set at instantiation):
    // parameter system_config_t MY_CONFIG = DEFAULT_SYSTEM_CONFIG;
    // MY_CONFIG.core.num_cores = 2;
    // MY_CONFIG.memory.l1_icache.size = 16*1024;
    
    //-------------------------------------------------------------------------
    // Configuration Validation
    //-------------------------------------------------------------------------
    // AI_TAG: FUNCTION - Comprehensive system configuration validation
    function automatic logic validate_system_config(
        input system_config_t config
    );
        logic valid;
        valid = 1'b1;
        
        // Validate cache configurations
        if (!validate_cache_config(config.memory.l1_icache)) begin
            $error("Invalid L1 I-cache configuration");
            valid = 1'b0;
        end
        
        if (!validate_cache_config(config.memory.l1_dcache)) begin
            $error("Invalid L1 D-cache configuration");
            valid = 1'b0;
        end
        
        if (config.memory.l2_enable && !validate_cache_config(config.memory.l2_cache)) begin
            $error("Invalid L2 cache configuration");
            valid = 1'b0;
        end
        
        if (config.memory.l3_enable && !validate_cache_config(config.memory.l3_cache)) begin
            $error("Invalid L3 cache configuration");
            valid = 1'b0;
        end
        
        // Validate core configuration
        if (config.core.num_cores == 0 || config.core.num_cores > 8) begin
            $error("Invalid number of cores: %0d", config.core.num_cores);
            valid = 1'b0;
        end
        
        // Validate memory hierarchy
        if (config.memory.l3_enable && !config.memory.l2_enable) begin
            $error("L3 cache requires L2 cache to be enabled");
            valid = 1'b0;
        end
        
        // Validate coherency requirements
        if (config.core.num_cores > 1 && config.memory.coherency.protocol == COHERENCY_NONE) begin
            $error("Multi-core system requires cache coherency");
            valid = 1'b0;
        end
        
        return valid;
    endfunction
    
    //-------------------------------------------------------------------------
    // Configuration Information Functions
    //-------------------------------------------------------------------------
    // AI_TAG: FUNCTION - Calculate total cache size
    function automatic integer get_total_cache_size(
        input system_config_t config
    );
        integer total_size;
        total_size = 0;
        
        // L1 caches (per core)
        total_size += config.memory.l1_icache.size * config.core.num_cores;
        total_size += config.memory.l1_dcache.size * config.core.num_cores;
        
        // L2 cache (shared)
        if (config.memory.l2_enable) begin
            total_size += config.memory.l2_cache.size;
        end
        
        // L3 cache (shared)
        if (config.memory.l3_enable) begin
            total_size += config.memory.l3_cache.size;
        end
        
        return total_size;
    endfunction
    
    // AI_TAG: FUNCTION - Get configuration summary string
    function automatic string get_config_summary(
        input system_config_t config
    );
        string summary;
        summary = $sformatf("Profile: %s, Cores: %0d, Execution: %s, Total Cache: %0dKB",
                           SELECTED_PROFILE,
                           config.core.num_cores,
                           CONFIG_EXECUTION_MODE,
                           get_total_cache_size(config) / 1024);
        return summary;
    endfunction
    
    //-------------------------------------------------------------------------
    // Compile-Time Configuration Display
    //-------------------------------------------------------------------------
    // Display configuration at compile time
    initial begin
        $display("=================================================================");
        $display("RISC-V System Configuration");
        $display("=================================================================");
        $display("Selected Profile: %s", SELECTED_PROFILE);
        $display("Configuration Summary: %s", get_config_summary(DEFAULT_SYSTEM_CONFIG));
        $display("=================================================================");
        
        // Validate configuration
        assert(validate_system_config(DEFAULT_SYSTEM_CONFIG))
            else $fatal("System configuration validation failed");
    end
    
    //-------------------------------------------------------------------------
    // Export Key Parameters for Backward Compatibility
    //-------------------------------------------------------------------------
    // These parameters maintain compatibility with existing code
    parameter integer XLEN = CONFIG_XLEN;
    parameter integer ADDR_WIDTH = CONFIG_ADDR_WIDTH;
    parameter integer NUM_CORES = CONFIG_NUM_CORES;
    parameter string EXECUTION_MODE = CONFIG_EXECUTION_MODE;
    parameter string BRANCH_PREDICTOR_TYPE = CONFIG_BRANCH_PREDICTOR_TYPE;
    
    // Cache sizes for direct use
    parameter integer L1_CACHE_SIZE = CONFIG_L1_ICACHE.size;
    parameter integer L2_CACHE_SIZE = CONFIG_L2_CACHE.size;
    parameter integer L3_CACHE_SIZE = CONFIG_L3_CACHE.size;

endpackage : riscv_system_config_pkg

//=============================================================================
// Dependencies: riscv_base_pkg, riscv_cache_config_pkg, selected profile package
//
// Instantiated In:
//   - All system modules requiring configuration
//   - Top-level system instantiation
//
// Performance:
//   - Critical Path: N/A (package only)
//   - Max Frequency: As per selected profile
//   - Area: As per selected profile
//
// Verification Coverage:
//   - Code Coverage: N/A
//   - Functional Coverage: N/A
//   - Branch Coverage: N/A
//
// Synthesis:
//   - Target Technology: As per selected profile
//   - Synthesis Tool: N/A
//   - Clock Domains: N/A
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: N/A
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author         | Description
//=============================================================================
// 1.0.0   | 2025-01-28 | DesignAI      | Initial release
//=============================================================================