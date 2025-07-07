//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_core.sv
// Module: riscv_core
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Top-level module for the configurable RV32IM RISC-V core.
//   Supports single-core, multi-core, in-order, and out-of-order execution
//   modes through parameterization. This is the integrated top-level for Phase 2.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
module riscv_core
#(
    // Core Configuration
    parameter string CORE_MODE = "MULTI_CORE",      // "SINGLE_CORE" or "MULTI_CORE"
    parameter string EXECUTION_MODE = DEFAULT_EXECUTION_MODE, // "IN_ORDER" or "OUT_OF_ORDER"
    parameter int unsigned NUM_CORES = DEFAULT_NUM_CORES,

    // Architectural Parameters
    parameter addr_t RESET_VECTOR = DEFAULT_RESET_VECTOR,

    // Feature Parameters
    parameter bit ENABLE_BUS_WATCHDOG = DEFAULT_ENABLE_BUS_WATCHDOG,
    parameter bit ENABLE_PMU = DEFAULT_ENABLE_PMU,
    parameter string BRANCH_PREDICTOR_TYPE = DEFAULT_BRANCH_PREDICTOR_TYPE,
    parameter integer BTB_ENTRIES = DEFAULT_BTB_ENTRIES,
    parameter integer BHT_ENTRIES = DEFAULT_BHT_ENTRIES,
    parameter integer PHT_ENTRIES = DEFAULT_PHT_ENTRIES,
    parameter integer SELECTOR_ENTRIES = DEFAULT_SELECTOR_ENTRIES,
    parameter integer GLOBAL_HISTORY_WIDTH = DEFAULT_GLOBAL_HISTORY_WIDTH,
    parameter integer RAS_ENTRIES = DEFAULT_RAS_ENTRIES,

    // Cache parameters
    parameter int unsigned L1_CACHE_SIZE = DEFAULT_L1_CACHE_SIZE,
    parameter int unsigned L2_CACHE_SIZE = DEFAULT_L2_CACHE_SIZE,
    parameter int unsigned L3_CACHE_SIZE = DEFAULT_L3_CACHE_SIZE
)
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // Unified Memory Interface (from L3 or Memory Wrapper)
    memory_req_rsp_if.master mem_if,

    // Interrupt Interface (per core)
    input  logic [NUM_CORES-1:0] m_software_interrupt_i,
    input  logic [NUM_CORES-1:0] m_timer_interrupt_i,
    input  logic [NUM_CORES-1:0] m_external_interrupt_i,
    output logic bus_watchdog_irq_o
);

    //---------------------------------------------------------------------------
    // Generate Core and Memory System based on CORE_MODE
    //---------------------------------------------------------------------------
    generate
        if (CORE_MODE == "MULTI_CORE") begin: gen_multicore_system
            //------------------------------------------------
            // Multi-Core Infrastructure
            //------------------------------------------------
            cache_coherency_if #( .NUM_CORES(NUM_CORES) ) cache_if( .clk(clk_i), .rst_n(rst_ni) );
            inter_core_comm_if #( .NUM_CORES(NUM_CORES) ) comm_if( .clk(clk_i), .rst_n(rst_ni) );
            sync_primitives_if #( .NUM_CORES(NUM_CORES) ) sync_if( .clk(clk_i), .rst_n(rst_ni) );

            // Interface between L2 and L3 Caches
            memory_req_rsp_if l2_l3_if();

            // Per-core L1 instruction and data cache interfaces
            memory_req_rsp_if l1_icache_if [NUM_CORES] ();
            memory_req_rsp_if l1_dcache_if [NUM_CORES] ();

            //------------------------------------------------
            // Multi-Core Memory Hierarchy
            //------------------------------------------------
            l2_cache #(
                .L2_CACHE_SIZE(L2_CACHE_SIZE),
                .NUM_CORES(NUM_CORES*2) // Each core has I-cache and D-cache
            ) u_l2_cache (
                .clk_i,
                .rst_ni,
                // Combine I-cache and D-cache requests into one array for L2
                .l1_if('{l1_dcache_if, l1_icache_if}), 
                .l3_if(l2_l3_if.master),
                .coherency_if(cache_if.l2_cache_port)
            );

            l3_cache #(
                .L3_CACHE_SIZE(L3_CACHE_SIZE)
            ) u_l3_cache (
                .clk_i,
                .rst_ni,
                .l2_if(l2_l3_if.slave),
                .mem_if(mem_if)
            );

            cache_coherency_controller #(
                .NUM_CORES(NUM_CORES)
            ) u_coherency_controller (
                .clk_i,
                .rst_ni,
                .coherency_if(cache_if.coherency_controller_port)
                // Snoops L2 requests directly from the l1_if bus
            );
            
            prefetch_unit u_prefetch_unit(
                .clk_i,
                .rst_ni,
                .mem_if(l2_l3_if.master) // Connect to L2->L3 bus
            );

            //------------------------------------------------
            // Core Manager
            //------------------------------------------------
            core_manager #(
                .NUM_CORES(NUM_CORES)
            ) u_core_manager (
                .clk_i,
                .rst_ni,
                .comm_if(comm_if.manager_port),
                .sync_if(sync_if.manager_port)
            );

            //------------------------------------------------
            // Core Generation Loop (Multi-Core)
            //------------------------------------------------
            genvar i;
            for (i = 0; i < NUM_CORES; i++) begin: gen_core
                // Instantiate a full core with its L1 caches
                core_subsystem #(
                    .CORE_ID(i),
                    .EXECUTION_MODE(EXECUTION_MODE),
                    .BRANCH_PREDICTOR_TYPE(BRANCH_PREDICTOR_TYPE),
                    .BTB_ENTRIES(BTB_ENTRIES),
                    .BHT_ENTRIES(BHT_ENTRIES),
                    .PHT_ENTRIES(PHT_ENTRIES),
                    .SELECTOR_ENTRIES(SELECTOR_ENTRIES),
                    .GLOBAL_HISTORY_WIDTH(GLOBAL_HISTORY_WIDTH),
                    .RAS_ENTRIES(RAS_ENTRIES),
                    .L1_CACHE_SIZE(L1_CACHE_SIZE),
                    .RESET_VECTOR(RESET_VECTOR),
                    .ENABLE_MMU(riscv_config_pkg::CONFIG_ENABLE_MMU), // Pass ENABLE_MMU parameter
                    .ENABLE_QOS(riscv_config_pkg::CONFIG_ENABLE_QOS) // Pass ENABLE_QOS parameter
                ) u_core_subsystem (
                    .clk_i,
                    .rst_ni,
                    .icache_if(l1_icache_if[i].master),
                    .dcache_if(l1_dcache_if[i].master),
                    .comm_if(comm_if.core_port[i]),
                    .sync_if(sync_if.core_port[i]),
                    .m_software_interrupt_i(m_software_interrupt_i[i]),
                    .m_timer_interrupt_i(m_timer_interrupt_i[i]),
                    .m_external_interrupt_i(m_external_interrupt_i[i])
                );
            end

        end else begin: gen_single_core_system
            //------------------------------------------------
            // Single-Core System (Phase 1 compatible)
            //------------------------------------------------
            memory_req_rsp_if icache_if();
            memory_req_rsp_if dcache_if();
            
            // In single core mode, no L2/L3 cache, connect L1s to a simple wrapper
            memory_wrapper u_mem_wrapper (
                .clk_i,
                .rst_ni,
                .icache_if(icache_if.slave),
                .dcache_if(dcache_if.slave),
                .mem_if(mem_if)
            );

            // Instantiate a single core subsystem
            core_subsystem #(
                .CORE_ID(0),
                .EXECUTION_MODE(EXECUTION_MODE),
                .BRANCH_PREDICTOR_TYPE(BRANCH_PREDICTOR_TYPE),
                .BTB_ENTRIES(BTB_ENTRIES),
                .BHT_ENTRIES(BHT_ENTRIES),
                .PHT_ENTRIES(PHT_ENTRIES),
                .SELECTOR_ENTRIES(SELECTOR_ENTRIES),
                .GLOBAL_HISTORY_WIDTH(GLOBAL_HISTORY_WIDTH),
                .RAS_ENTRIES(RAS_ENTRIES),
                .L1_CACHE_SIZE(L1_CACHE_SIZE),
                .RESET_VECTOR(RESET_VECTOR)
            ) u_core_subsystem (
                .clk_i,
                .rst_ni,
                .icache_if(icache_if.master),
                .dcache_if(dcache_if.master),
                // Tie off multi-core interfaces
                .comm_if('0),
                .sync_if('0),
                .m_software_interrupt_i(m_software_interrupt_i[0]),
                .m_timer_interrupt_i(m_timer_interrupt_i[0]),
                .m_external_interrupt_i(m_external_interrupt_i[0])
            );
        end
    endgenerate

    // AI_TAG: ASSERTION - Reset vector should be aligned
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - riscv_core_coverage.reset_vector_alignment_cp
    ResetVectorAlignment: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (RESET_VECTOR[1:0] == 2'b00));

    // AI_TAG: ASSERTION - Core ID should be within valid range
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - riscv_core_coverage.core_id_range_cp
    CoreIDRange: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (i >= 0 && i < NUM_CORES));

    // AI_TAG: ASSERTION - Memory request should be valid when ready
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - riscv_core_coverage.mem_req_valid_cp
    MemReqValid: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (mem_if.req_valid && mem_if.req_ready |-> mem_if.req_addr[1:0] == 2'b00));

    // Instantiate the Bus Watchdog
    bus_watchdog #(
        .ENABLE_WATCHDOG(ENABLE_BUS_WATCHDOG)
    ) u_bus_watchdog (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        // Connect to a CSR bus interface if available
        .csr_addr_i('0),
        .csr_wdata_i('0),
        .csr_write_en_i('0),
        .csr_rdata_o(),
        // Connect to the main memory bus
        .bus_addr_i(mem_if.req_addr),
        .bus_req_i(mem_if.req_valid),
        .bus_gnt_i(mem_if.req_ready),
        .watchdog_irq_o(bus_watchdog_irq_o)
    );

    // Instantiate the Power Management Unit
    if (CONFIG_ENABLE_PMU) begin: gen_pmu
        power_management_unit #(
            .NUM_CORES(NUM_CORES)
        ) u_pmu (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            // TODO: Connect to a real CSR bus
            .csr_access_i(1'b0),
            .csr_addr_i('0),
            .csr_write_i(1'b0),
            .csr_wdata_i('0),
            .csr_rdata_o(),

            // TODO: Connect to core and cache activity signals
            .core_active_i('0),
            .core_idle_i('0),
            .core_utilization_i('0),
            .cache_active_i(1'b0),
            .cache_miss_rate_i('0),
            .thermal_alert_i(1'b0),

            // Power Management Outputs
            .core_clk_en_o(),
            .l2_cache_clk_en_o(),
            .l3_cache_clk_en_o(),
            .interconnect_clk_en_o(),
            .voltage_level_o(),
            .frequency_level_o(),
            .dvfs_update_o(),
            .power_domain_en_o(),
            .retention_mode_o(),
            .throttling_event_count_o()
        );
    end

endmodule : riscv_core

//=============================================================================
// Dependencies: All core modules (fetch_stage.sv, decode_stage.sv, execute_stage.sv, 
//               mem_stage.sv, writeback_stage.sv, reg_file.sv, csr_regfile.sv, 
//               hazard_unit.sv, alu.sv, mult_unit.sv, div_unit.sv, exception_handler.sv,
//               branch_predictor.sv, icache.sv, memory_wrapper.sv, axi4_adapter.sv)
//
// Performance:
//   - Critical Path: Pipeline stage to stage
//   - Max Frequency: TBD
//   - Area: TBD
//
// Verification Coverage:
//   - Code Coverage: Not measured
//   - Functional Coverage: Not measured
//   - Branch Coverage: Not measured
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)
//
// Testing:
//   - Testbench: TBD
//   - Test Vectors: TBD
//   - Simulation Time: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.1.0   | 2025-06-28 | DesignAI           | Integrated all units, including mult_unit stall path and CSR file. Updated hazard unit connections for full functionality.
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//=============================================================================