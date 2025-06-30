//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: core_subsystem.sv
// Module: core_subsystem
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Core subsystem that integrates the fetch, decode, execute, memory, and
//   writeback stages of the RISC-V pipeline. Manages pipeline control,
//   hazard detection, and exception handling with configurable reset vector.
//   Uses proper SystemVerilog interfaces for all connections.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_config_pkg::*;

module core_subsystem #(
    parameter addr_t RESET_VECTOR = DEFAULT_RESET_VECTOR,
    parameter integer CORE_ID = 0,
    parameter string EXECUTION_MODE = DEFAULT_EXECUTION_MODE,
    parameter string BRANCH_PREDICTOR_TYPE = DEFAULT_BRANCH_PREDICTOR_TYPE,
    parameter int unsigned L1_ICACHE_SIZE = DEFAULT_L1_ICACHE_SIZE,
    parameter int unsigned L1_DCACHE_SIZE = DEFAULT_L1_DCACHE_SIZE
) (
    // Clock and Reset
    input  logic        clk_i,
    input  logic        rst_ni,

    // Memory Interfaces - PROPER INTERFACE USAGE with QoS
    memory_req_rsp_if.master icache_if,
    memory_req_rsp_if.master dcache_if,

    // Inter-Core Communication Interfaces (for multi-core)
    inter_core_comm_if.core comm_if,
    sync_primitives_if.core sync_if,

    // Interrupt Interface
    input  logic        m_software_interrupt_i,
    input  logic        m_timer_interrupt_i,
    input  logic        m_external_interrupt_i,
    
    // QoS Configuration Interface
    input  qos_config_t         core_qos_config_i,     // Base QoS config for this core
    input  logic                qos_enable_i,          // Global QoS enable
    output logic [31:0]         qos_violations_o,      // QoS violations from this core
    
    // QoS-Enhanced Memory Request Outputs (for multi-core arbitration)
    output logic                mem_req_valid_o,       // Memory request valid
    output memory_req_t         mem_req_o,             // Memory request
    output qos_config_t         mem_qos_config_o,      // QoS config for memory request
    input  logic                mem_req_ready_i,       // Memory request ready
    
    input  logic                mem_rsp_valid_i,       // Memory response valid
    input  memory_rsp_t         mem_rsp_i,             // Memory response
    output logic                mem_rsp_ready_o,       // Memory response ready

    // Performance monitoring outputs
    output logic                pipeline_stall_o,
    output logic                branch_mispredicted_o,
    output logic                instruction_retired_o,
    output logic                core_active_o
);

    // AI_TAG: INTERNAL_BLOCK - Pipeline register interfaces between stages
    // AI_TAG: FEATURE - 5-stage RISC-V pipeline with hazard detection

    //------------------------------------------------------------------------- 
    // Pipeline Stage Interfaces
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Pipeline stage structured interfaces
    
    // Structured pipeline register types (imported from core package)
    if_id_reg_t         if_id_reg;
    id_ex_reg_t         id_ex_reg;
    ex_mem_reg_t        ex_mem_reg;
    mem_wb_reg_t        mem_wb_reg;
    
    // Additional pipeline signals
    addr_t              pc_f;
    branch_prediction_t bp_prediction;
    
    // Exception information from pipeline stages
    exception_info_t    fetch_exception;
    exception_info_t    execute_exception;
    exception_info_t    memory_exception;

    //------------------------------------------------------------------------- 
    // Control and Hazard Signals
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERNAL_LOGIC - Hazard detection and control signals
    logic        data_hazard_detected;
    logic        control_hazard_detected;
    logic        structural_hazard_detected;
    logic        pipeline_stall;
    logic        pipeline_flush;

    // Register file interface signals
    logic [4:0]  reg_file_rs1_addr;
    logic [4:0]  reg_file_rs2_addr;
    logic [4:0]  reg_file_rd_addr;
    word_t       reg_file_rs1_data;
    word_t       reg_file_rs2_data;
    word_t       reg_file_rd_data;
    logic        reg_file_write_en;

    // Branch resolution signals
    logic        ex_mem_branch_taken;
    addr_t       ex_mem_branch_target;
    
    // Branch predictor update interface
    branch_update_t bp_update;

    //------------------------------------------------------------------------- 
    // Exception and Interrupt Handling
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERNAL_LOGIC - Exception handling signals
    logic        interrupt_pending;
    logic [31:0] exception_cause;
    addr_t       exception_pc;

    // Performance counters
    logic        instruction_retired;

    //---------------------------------------------------------------------------
    // QoS Configuration and Management
    //---------------------------------------------------------------------------
    
    // QoS configurations for different request types
    qos_config_t instr_qos_config;
    qos_config_t data_qos_config;
    logic [31:0] qos_violation_counter;
    
    // Current pipeline state for QoS determination
    logic exception_pending;
    logic debug_access_pending;
    logic critical_access_pending;
    
    assign exception_pending = fetch_exception.valid || execute_exception.valid || memory_exception.valid;
    assign debug_access_pending = 1'b0; // Connect to debug interface when available
    assign critical_access_pending = exception_pending || debug_access_pending;
    
    // Generate QoS configuration for instruction fetches
    function automatic qos_config_t get_instruction_qos_config();
        qos_config_t qos_config;
        
        qos_config.qos_level = exception_pending ? riscv_config_pkg::QOS_LEVEL_CRITICAL : riscv_config_pkg::QOS_LEVEL_HIGH;
        qos_config.transaction_type = riscv_config_pkg::QOS_TYPE_INSTR_FETCH;
        qos_config.urgent = exception_pending;
        qos_config.guaranteed_bw = 1'b1;
        qos_config.weight = exception_pending ? riscv_config_pkg::QOS_WEIGHT_CRITICAL : riscv_config_pkg::QOS_WEIGHT_HIGH;
        qos_config.max_latency_cycles = exception_pending ? riscv_config_pkg::QOS_INSTR_LATENCY_CRITICAL : riscv_config_pkg::QOS_INSTR_LATENCY_NORMAL;
        qos_config.bandwidth_percent = riscv_config_pkg::QOS_INSTR_BW_PERCENT;
        qos_config.core_id = CORE_ID[3:0];
        qos_config.preemptable = ~exception_pending;
        qos_config.real_time = exception_pending;
        qos_config.retry_limit = riscv_config_pkg::QOS_INSTR_RETRY_LIMIT;
        qos_config.ordered = 1'b1;
        
        return qos_config;
    endfunction
    
    // Generate QoS configuration for data accesses
    function automatic qos_config_t get_data_qos_config(
        input logic is_store,
        input logic is_critical
    );
        qos_config_t qos_config;
        
        if (is_critical || exception_pending) begin
            qos_config.qos_level = riscv_config_pkg::QOS_LEVEL_CRITICAL;
            qos_config.weight = riscv_config_pkg::QOS_WEIGHT_CRITICAL;
            qos_config.max_latency_cycles = riscv_config_pkg::QOS_DATA_LATENCY_CRITICAL;
            qos_config.urgent = 1'b1;
            qos_config.real_time = 1'b1;
            qos_config.preemptable = 1'b0;
        end else begin
            qos_config.qos_level = is_store ? riscv_config_pkg::QOS_LEVEL_MEDIUM : riscv_config_pkg::QOS_LEVEL_MEDIUM_HIGH;
            qos_config.weight = is_store ? riscv_config_pkg::QOS_WEIGHT_MEDIUM : riscv_config_pkg::QOS_WEIGHT_MEDIUM_HIGH;
            qos_config.max_latency_cycles = is_store ? riscv_config_pkg::QOS_DATA_STORE_LATENCY_NORMAL : riscv_config_pkg::QOS_DATA_LOAD_LATENCY_NORMAL;
            qos_config.urgent = 1'b0;
            qos_config.real_time = 1'b0;
            qos_config.preemptable = 1'b1;
        end
        
        qos_config.transaction_type = riscv_config_pkg::QOS_TYPE_DATA_ACCESS;
        qos_config.guaranteed_bw = is_critical || exception_pending;
        qos_config.bandwidth_percent = riscv_config_pkg::QOS_DATA_BW_PERCENT;
        qos_config.core_id = CORE_ID[3:0];
        qos_config.retry_limit = riscv_config_pkg::QOS_DATA_RETRY_LIMIT;
        qos_config.ordered = 1'b1;
        
        return qos_config;
    endfunction
    
    // QoS configuration assignment
    always_comb begin : proc_qos_config_assignment
        instr_qos_config = get_instruction_qos_config();
        data_qos_config = get_data_qos_config(1'b0, critical_access_pending); // Default to load config
    end
    
    //---------------------------------------------------------------------------
    // Memory Request Arbitration with QoS
    //---------------------------------------------------------------------------
    
    // Internal memory request signals
    logic icache_req_pending;
    logic dcache_req_pending;
    logic priority_to_icache;
    
    assign icache_req_pending = icache_if.req_valid && qos_enable_i;
    assign dcache_req_pending = dcache_if.req_valid && qos_enable_i;
    
    // Arbitration between I-cache and D-cache based on QoS
    always_comb begin : proc_cache_arbitration
        priority_to_icache = 1'b0;
        
        if (icache_req_pending && dcache_req_pending) begin
            // Both caches have requests - arbitrate based on QoS
            if (instr_qos_config.qos_level > data_qos_config.qos_level) begin
                priority_to_icache = 1'b1;
            end else if (instr_qos_config.qos_level == data_qos_config.qos_level) begin
                // Same QoS level - prioritize based on urgency
                priority_to_icache = instr_qos_config.urgent && !data_qos_config.urgent;
            end
            // Otherwise, D-cache gets priority (default to data access)
        end else if (icache_req_pending) begin
            priority_to_icache = 1'b1;
        end
        // else D-cache gets priority or no requests
    end
    
    // Memory interface outputs for multi-core arbitration
    always_comb begin : proc_memory_interface_output
        if (qos_enable_i) begin
            if (priority_to_icache && icache_req_pending) begin
                // Forward I-cache request
                mem_req_valid_o = icache_if.req_valid;
                mem_req_o = icache_if.req;
                mem_qos_config_o = instr_qos_config;
                icache_if.req_ready = mem_req_ready_i;
                dcache_if.req_ready = 1'b0; // Block D-cache
            end else if (dcache_req_pending) begin
                // Forward D-cache request
                mem_req_valid_o = dcache_if.req_valid;
                mem_req_o = dcache_if.req;
                mem_qos_config_o = data_qos_config;
                dcache_if.req_ready = mem_req_ready_i;
                icache_if.req_ready = 1'b0; // Block I-cache
            end else begin
                // No requests or QoS disabled
                mem_req_valid_o = 1'b0;
                mem_req_o = '0;
                mem_qos_config_o = '0;
                icache_if.req_ready = 1'b1;
                dcache_if.req_ready = 1'b1;
            end
        end else begin
            // QoS disabled - simple passthrough to first available interface
            mem_req_valid_o = icache_if.req_valid || dcache_if.req_valid;
            mem_req_o = icache_if.req_valid ? icache_if.req : dcache_if.req;
            mem_qos_config_o = core_qos_config_i; // Use base core config
            icache_if.req_ready = mem_req_ready_i && icache_if.req_valid;
            dcache_if.req_ready = mem_req_ready_i && !icache_if.req_valid;
        end
    end
    
    // Route responses back to appropriate cache based on transaction ID
    always_comb begin : proc_response_assignment
        if (mem_rsp_valid_i) begin
            // ID 0 is for I-cache, all others are for D-cache
            if (mem_rsp_i.id == 4'h0) begin
                icache_if.rsp_valid = 1'b1;
                icache_if.rsp = mem_rsp_i;
                dcache_if.rsp_valid = 1'b0;
                dcache_if.rsp = '0;
                mem_rsp_ready_o = icache_if.rsp_ready;
            end else begin
                dcache_if.rsp_valid = 1'b1;
                dcache_if.rsp = mem_rsp_i;
                icache_if.rsp_valid = 1'b0;
                icache_if.rsp = '0;
                mem_rsp_ready_o = dcache_if.rsp_ready;
            end
        end else begin
            icache_if.rsp_valid = 1'b0;
            dcache_if.rsp_valid = 1'b0;
            icache_if.rsp = '0;
            dcache_if.rsp = '0;
            mem_rsp_ready_o = 1'b1;
        end
    end
    
    //---------------------------------------------------------------------------
    // QoS Violation Monitoring
    //---------------------------------------------------------------------------
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_qos_monitoring
        if (!rst_ni) begin
            qos_violation_counter <= 0;
        end else begin
            // Monitor for QoS violations
            if (mem_req_valid_o && !mem_req_ready_i && qos_enable_i) begin
                // Memory not ready when we have a request - potential violation
                qos_violation_counter <= qos_violation_counter + 1;
            end
            
            // Additional violation monitoring can be added here
            // e.g., latency deadline misses, bandwidth violations
        end
    end
    
    assign qos_violations_o = qos_violation_counter;

    //------------------------------------------------------------------------- 
    // Pipeline Stage Instantiations
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERNAL_BLOCK - Fetch stage with branch prediction
    fetch_stage #(
        .RESET_VECTOR(RESET_VECTOR),
        .BTB_ENTRIES(DEFAULT_BTB_ENTRIES),
        .BHT_ENTRIES(DEFAULT_BHT_ENTRIES)
    ) u_fetch_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Control signals - use proper port names
        .stall_f_i(pipeline_stall),
        .stall_d_i(pipeline_stall),
        .flush_f_i(pipeline_flush),
        
        // PC redirect interface 
        .pc_redirect_en_i(ex_mem_branch_taken),
        .pc_redirect_target_i(ex_mem_branch_target),
        
        // Branch predictor update interface
        .bp_update_i(bp_update),
        
        // Memory interface - connect to instruction cache interface
        .instr_req_valid_o(icache_if.req_valid),
        .instr_req_ready_i(icache_if.req_ready),
        .instr_req_addr_o(icache_if.req.addr),
        .instr_rsp_valid_i(icache_if.rsp_valid),
        .instr_rsp_ready_o(icache_if.rsp_ready),
        .instr_rsp_data_i(icache_if.rsp.data),
        .instr_rsp_error_i(icache_if.rsp.error),
        
        // Pipeline outputs - structured interface
        .if_id_reg_o(if_id_reg),
        .pc_f_o(pc_f),
        .bp_prediction_o(bp_prediction),
        .exception_o(fetch_exception),
        
        // Performance counters
        .perf_hit_count_o(),
        .perf_miss_count_o(),
        .perf_flush_count_o(),
        .perf_total_requests_o(),
        .perf_hit_rate_o(),
        .perf_counter_reset_i(1'b0)
    );

    // AI_TAG: INTERNAL_BLOCK - Decode stage with register file interface
    decode_stage u_decode_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Control signals
        .stall_e_i(pipeline_stall),
        .flush_d_i(pipeline_flush),
        
        // Pipeline input from IF/ID - structured interface
        .if_id_reg_i(if_id_reg),
        
        // Register file interface
        .rs1_addr_o(reg_file_rs1_addr),
        .rs2_addr_o(reg_file_rs2_addr),
        .rs1_data_i(reg_file_rs1_data),
        .rs2_data_i(reg_file_rs2_data),
        
        // Pipeline output to ID/EX - structured interface
        .id_ex_reg_o(id_ex_reg)
    );

    // AI_TAG: INTERNAL_BLOCK - Execute stage with ALU and branch resolution
    execute_stage u_execute_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Control signals
        .stall_m_i(pipeline_stall),
        .flush_e_i(pipeline_flush),
        
        // Pipeline input from ID/EX - structured interface
        .id_ex_reg_i(id_ex_reg),
        
        // Pipeline output to EX/MEM - structured interface
        .ex_mem_reg_o(ex_mem_reg),
        
        // Branch resolution outputs
        .branch_taken_o(ex_mem_branch_taken),
        .branch_target_o(ex_mem_branch_target),
        
        // Exception interface
        .exception_o(execute_exception)
    );

    // AI_TAG: INTERNAL_BLOCK - Memory stage with data cache interface
    mem_stage u_mem_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Control signals
        .stall_w_i(pipeline_stall),
        .flush_m_i(pipeline_flush),
        
        // Pipeline input from EX/MEM - structured interface
        .ex_mem_reg_i(ex_mem_reg),
        
        // Data cache interface - connect to data cache interface
        .data_req_valid_o(dcache_if.req_valid),
        .data_req_ready_i(dcache_if.req_ready),
        .data_req_addr_o(dcache_if.req.addr),
        .data_req_write_o(dcache_if.req.write),
        .data_req_strb_o(dcache_if.req.strb),
        .data_req_data_o(dcache_if.req.data),
        .data_rsp_valid_i(dcache_if.rsp_valid),
        .data_rsp_ready_o(dcache_if.rsp_ready),
        .data_rsp_data_i(dcache_if.rsp.data),
        .data_rsp_error_i(dcache_if.rsp.error),
        
        // Pipeline output to MEM/WB - structured interface  
        .mem_wb_reg_o(mem_wb_reg),
        
        // Exception interface
        .exception_o(memory_exception)
    );

    // AI_TAG: INTERNAL_BLOCK - Writeback stage with register file interface
    writeback_stage u_writeback_stage (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Pipeline input from MEM/WB - structured interface
        .mem_wb_reg_i(mem_wb_reg),
        
        // Register file write interface
        .reg_file_write_en_o(reg_file_write_en),
        .reg_file_rd_addr_o(reg_file_rd_addr),
        .reg_file_rd_data_o(reg_file_rd_data),
        .instruction_retired_o(instruction_retired)
    );

    //------------------------------------------------------------------------- 
    // Register File Instance
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERNAL_BLOCK - Register file with dual read ports
    reg_file u_reg_file (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Read ports
        .rs1_addr_i(reg_file_rs1_addr),
        .rs2_addr_i(reg_file_rs2_addr),
        .rs1_data_o(reg_file_rs1_data),
        .rs2_data_o(reg_file_rs2_data),
        
        // Write port
        .rd_addr_i(reg_file_rd_addr),
        .rd_data_i(reg_file_rd_data),
        .rd_write_en_i(reg_file_write_en)
    );

    //------------------------------------------------------------------------- 
    // Hazard Detection Unit
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERNAL_BLOCK - Hazard detection for pipeline control
    hazard_unit u_hazard_unit (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Pipeline stage inputs for hazard detection
        .if_id_reg_i(if_id_reg),
        .id_ex_reg_i(id_ex_reg),
        .ex_mem_reg_i(ex_mem_reg),
        .mem_wb_reg_i(mem_wb_reg),
        
        // Hazard detection outputs
        .data_hazard_o(data_hazard_detected),
        .control_hazard_o(control_hazard_detected),
        .structural_hazard_o(structural_hazard_detected)
    );

    //------------------------------------------------------------------------- 
    // Exception Handler
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERNAL_BLOCK - Exception and interrupt handling
    exception_handler #(
        .CORE_ID(CORE_ID)
    ) u_exception_handler (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Exception inputs from pipeline stages
        .fetch_exception_i(fetch_exception),
        .execute_exception_i(execute_exception),
        .memory_exception_i(memory_exception),
        
        // Interrupt inputs
        .m_software_interrupt_i(m_software_interrupt_i),
        .m_timer_interrupt_i(m_timer_interrupt_i),
        .m_external_interrupt_i(m_external_interrupt_i),
        
        // Exception handling outputs
        .interrupt_pending_o(interrupt_pending),
        .exception_pc_o(exception_pc),
        .exception_cause_o(exception_cause)
    );

    //------------------------------------------------------------------------- 
    // Pipeline Control Logic
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERNAL_LOGIC - Pipeline control and hazard handling
    assign pipeline_stall = data_hazard_detected || structural_hazard_detected;
    assign pipeline_flush = control_hazard_detected || exception_pending || interrupt_pending;

    // Connect to performance monitoring outputs
    assign pipeline_stall_o = pipeline_stall;
    assign branch_mispredicted_o = control_hazard_detected;
    assign instruction_retired_o = instruction_retired;
    assign core_active_o = |if_id_reg.valid; // Core is active if there is a valid instruction in pipeline

    //------------------------------------------------------------------------- 
    // Branch Prediction (if enabled)
    //-------------------------------------------------------------------------
    
    generate
        if (BRANCH_PREDICTOR_TYPE != "STATIC") begin : gen_branch_predictor
            // AI_TAG: INTERNAL_BLOCK - Dynamic branch predictor
            branch_predictor #(
                .PREDICTOR_TYPE(BRANCH_PREDICTOR_TYPE),
                .BTB_ENTRIES(DEFAULT_BTB_ENTRIES),
                .BHT_ENTRIES(DEFAULT_BHT_ENTRIES)
            ) u_branch_predictor (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .req_valid_i(bp_req_valid),
                .req_pc_i(bp_req_pc),
                .rsp_valid_o(bp_rsp_valid),
                .rsp_data_o(bp_rsp_data),
                .update_valid_i(ex_mem_valid),
                .update_pc_i(ex_mem_pc),
                .update_taken_i(ex_mem_branch_taken),
                .update_target_i(ex_mem_branch_target)
            );
        end else begin : gen_static_prediction
            // Static prediction - always not taken
            assign bp_rsp_valid = bp_req_valid;
            assign bp_rsp_data = '0; // Not taken
        end
    endgenerate

    //------------------------------------------------------------------------- 
    // Branch Update Signal Generation
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERNAL_LOGIC - Generate branch predictor update from execute stage
    always_comb begin : proc_branch_update
        bp_update.update_valid = ex_mem_reg.valid && ex_mem_reg.ctrl.is_branch;
        bp_update.update_pc = ex_mem_reg.pc;
        bp_update.actual_taken = ex_mem_branch_taken;
        bp_update.actual_target = ex_mem_branch_target;
        bp_update.is_branch = ex_mem_reg.ctrl.is_branch;
    end

    //------------------------------------------------------------------------- 
    // Memory Interface Signal Connections
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERNAL_LOGIC - Memory interface signal routing
    // Instruction cache interface additional signals
    assign icache_if.clk = clk_i;
    assign icache_if.rst_n = rst_ni;
    assign icache_if.req.write = 1'b0;  // Instruction fetches are always reads
    assign icache_if.req.strb = 4'hF;   // Full word access
    assign icache_if.req.data = '0;     // No write data for instruction fetches
    assign icache_if.req.id = 4'h0;     // Single outstanding request
    assign icache_if.req.burst_len = 3'h0; // Single beat
    
    // Data cache interface additional signals
    assign dcache_if.clk = clk_i;
    assign dcache_if.rst_n = rst_ni;
    assign dcache_if.req.id = 4'h1;     // Different ID from instruction cache
    assign dcache_if.req.burst_len = 3'h0; // Single beat

    //------------------------------------------------------------------------- 
    // Assertions for Verification
    //-------------------------------------------------------------------------
    
    // AI_TAG: ASSERTION - Reset vector alignment check
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    // AI_TAG: ASSERTION_COVERAGE_LINK - core_subsystem_coverage.reset_vector_alignment_cp
    ResetVectorAlignment: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (RESET_VECTOR[1:0] == 2'b00))
    else $error("Reset vector must be 4-byte aligned");

    // AI_TAG: ASSERTION - Core ID validity check
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    CoreIdValidity: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (CORE_ID < DEFAULT_MAX_CORES))
    else $error("Core ID exceeds maximum allowed cores");

    // AI_TAG: ASSERTION - Pipeline integrity check
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Warning
    PipelineIntegrity: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (!(pipeline_stall && pipeline_flush)))
    else $warning("Pipeline stall and flush should not occur simultaneously");

endmodule : core_subsystem

`default_nettype wire

//=============================================================================
// Dependencies: riscv_config_pkg, riscv_types_pkg, riscv_core_pkg
//
// Performance:
//   - Critical Path: Through the entire pipeline
//   - Max Frequency: Limited by the slowest pipeline stage
//   - Area: Significant - includes all pipeline stages and control logic
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
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//============================================================================= 