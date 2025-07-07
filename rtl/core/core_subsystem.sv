//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: core_subsystem.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: core_subsystem
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-07-07
// DESCRIPTION: Core subsystem integrating RISC-V pipeline stages.
// PRIMARY_PURPOSE: Integrates fetch, decode, execute, memory, and writeback stages.
// ROLE_IN_SYSTEM: Central processing unit within the RISC-V core.
// PROBLEM_SOLVED: Provides a configurable and extensible RISC-V pipeline.
// MODULE_TYPE: RTL
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V ISA Specification
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================

`timescale 1ns/1ps
`default_nettype none


import riscv_types_pkg::*;
import riscv_core_pkg::*;
import riscv_ooo_types_pkg::*;
import mmu_pkg::*;
import qos_pkg::*;
import ooo_pkg::*;

module core_subsystem #(
    parameter addr_t RESET_VECTOR = DEFAULT_RESET_VECTOR,
    parameter integer CORE_ID = 0,
    parameter string EXECUTION_MODE = DEFAULT_EXECUTION_MODE,
    parameter string BRANCH_PREDICTOR_TYPE = DEFAULT_BRANCH_PREDICTOR_TYPE,
    parameter int unsigned L1_CACHE_SIZE = DEFAULT_L1_CACHE_SIZE,
    
    parameter logic ENABLE_FPU = DEFAULT_ENABLE_FPU,
    parameter logic ENABLE_VPU = DEFAULT_ENABLE_VPU,
    parameter logic ENABLE_ML_INFERENCE = DEFAULT_ENABLE_ML_INFERENCE,
    parameter logic ENABLE_MMU = DEFAULT_ENABLE_MMU, // New: Enable Memory Management Unit
    parameter logic ENABLE_QOS = DEFAULT_ENABLE_QOS, // New: Enable Quality of Service Unit
    parameter logic ENABLE_OOO = (EXECUTION_MODE == "OUT_OF_ORDER"), // New: Enable Out-of-Order Execution
    parameter logic ENABLE_DATA_ACCELERATOR = DEFAULT_ENABLE_DATA_ACCELERATOR
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

    // New QoS-related inputs
    input  logic        debug_access_pending_i,
    input  logic        is_store_i, // From execute stage for data accesses
    input  logic        is_critical_data_access_i, // From execute stage for data accesses

    // Reset Synchronizer
    logic rst_ni_sync1, rst_ni_sync2;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            rst_ni_sync1 <= 1'b0;
            rst_ni_sync2 <= 1'b0;
        end else begin
            rst_ni_sync1 <= 1'b1;
            rst_ni_sync2 <= rst_ni_sync1;
        }
    end

    // QoS Configuration Interface
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
    output logic                core_active_o,

    // Data Processing Unit Interface (Optional)
    output dpu_req_t            dpu_req_o,
    input  dpu_rsp_t            dpu_rsp_i,
    output logic                dpu_busy_o,
    output logic                dpu_error_o,
    output exception_info_t    exception_o,

    

    // CSR Interface (from Execute Stage)
    input  logic        csr_read_en_i,
    input  logic [11:0] csr_addr_i,
    output logic [31:0] csr_rdata_o,
    input  logic        csr_write_en_i,
    input  logic [11:0] csr_addr_w_i,
    input  logic [31:0] csr_wdata_i;

    // Internal signals for MMU connections
    mmu_request_t  mmu_instr_req;
    mmu_response_t mmu_instr_resp;
    logic          mmu_instr_req_valid;
    logic          mmu_instr_req_ready;
    logic          mmu_instr_resp_valid;
    logic          mmu_instr_resp_ready;

    mmu_request_t  mmu_data_req;
    mmu_response_t mmu_data_resp;
    logic          mmu_data_req_valid;
    logic          mmu_data_req_ready;
    logic          mmu_data_resp_valid;
    logic          mmu_data_resp_ready;

    // Internal signals for CSR connections (to MMU and CSR Regfile)
    logic        csr_read_en_internal;
    logic [11:0] csr_addr_internal;
    logic [31:0] csr_rdata_internal;
    logic        csr_write_en_internal;
    logic [11:0] csr_addr_w_internal;
    logic [31:0] csr_wdata_internal;

    // Internal signal for CSR read data from csr_regfile
    logic [31:0] csr_rdata_from_csr_regfile;

    // Internal signals for QoS
    logic [1:0]  qos_req_valid; // [0]: instr, [1]: data
    logic [1:0]  qos_req_ready; // [0]: instr, [1]: data
    logic [1:0]  qos_granted_req;
    qos_config_t qos_granted_config;

    // Internal signals for OOO connections
    ooo_dispatch_t decode_dispatch_o;
    ooo_commit_t   ooo_commit_i;
    logic          ooo_flush_i;
    logic          decode_ready_o; // From OOO engine to decode stage

    // Internal signals for pipeline stages
    if_id_reg_t         if_id_reg;
    id_ex_reg_t         id_ex_reg;
    ex_mem_reg_t        ex_mem_reg;
    mem_wb_reg_t        mem_wb_reg;
    
    addr_t              pc_f;
    branch_prediction_t bp_prediction;
    branch_update_t     bp_update;

    exception_info_t    fetch_exception;
    exception_info_t    execute_exception;
    exception_info_t    memory_exception;

    logic        data_hazard_detected;
    logic        control_hazard_detected;
    logic        structural_hazard_detected;
    logic        pipeline_stall;
    logic        pipeline_flush;

    reg_addr_t   reg_file_rs1_addr;
    reg_addr_t   reg_file_rs2_addr;
    reg_addr_t   reg_file_rd_addr;
    word_t       reg_file_rs1_data;
    word_t       reg_file_rs2_data;
    word_t       reg_file_rd_data;
    logic        reg_file_write_en;

    logic        ex_mem_branch_taken;
    addr_t       ex_mem_branch_target;

    logic        interrupt_pending;
    addr_t       exception_pc;
    word_t       exception_cause;
    logic        instruction_retired;

    // Intermediate signals for CSR connections from pipeline wrapper
    logic        pipeline_csr_op_i;
    logic        pipeline_trap_en_i;
    addr_t       pipeline_mepc_i;
    word_t       pipeline_mcause_i;
    word_t       pipeline_mtval_i;
    logic        pipeline_stall_i;
    logic        pipeline_instruction_retired_i;

    // Assign CSR inputs to internal signals
    assign csr_read_en_internal = csr_read_en_i;
    assign csr_addr_internal = csr_addr_i;
    assign csr_write_en_internal = csr_write_en_i;
    assign csr_addr_w_internal = csr_addr_w_i;
    assign csr_wdata_internal = csr_wdata_i;

    // AI_TAG: INTERNAL_BLOCK - Pipeline register interfaces between stages
    // AI_TAG: FEATURE - 5-stage RISC-V pipeline with hazard detection

    //------------------------------------------------------------------------- 
    // Pipeline Stage Interfaces
    //------------------------------------------------------------------------- 
    // AI_TAG: INTERNAL_LOGIC - Pipeline stage structured interfaces
    
    // Structured pipeline register types (imported from core package)
    
    
    // Additional pipeline signals
    

    //------------------------------------------------------------------------- 
    // Control and Hazard Signals
    //------------------------------------------------------------------------- 
    
    // AI_TAG: INTERNAL_LOGIC - Hazard detection and control signals
    

    // Assign CSR inputs to internal signals
    assign csr_read_en_internal = csr_read_en_i;
    assign csr_addr_internal = csr_addr_i;
    assign csr_write_en_internal = csr_write_en_i;
    assign csr_addr_w_internal = csr_addr_w_i;
    assign csr_wdata_internal = csr_wdata_i;
    

    

    

    //---------------------------------------------------------------------------
    // QoS Configuration and Management
    //---------------------------------------------------------------------------
    generate if (ENABLE_QOS) begin : gen_qos_unit
        qos_management_unit #(
            .CORE_ID(CORE_ID),
            .NUM_REQUESTERS(2) // Instruction and Data requests
        ) u_qos_management_unit (
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            .qos_enable_i(qos_enable_i),
            .exception_pending_i(exception_o.valid), // Assuming exception_o.valid is the signal
            .debug_access_pending_i(debug_access_pending_i),
            .is_store_i(is_store_i),
            .is_critical_data_access_i(is_critical_data_access_i),
            .req_qos_config_i({u_qos_management_unit.data_qos_config_o, u_qos_management_unit.instr_qos_config_o}), // Order: data, instr
            .req_valid_i(qos_req_valid),
            .req_ready_o(qos_req_ready),
            .mem_req_valid_i(mem_req_valid_o), // Overall memory request valid from arbiter
            .mem_req_ready_i(mem_req_ready_i), // Overall memory request ready from external memory
            .granted_req_o(qos_granted_req),
            .granted_qos_config_o(qos_granted_config),
            .qos_violations_o(qos_violations_o)
        );
    end else begin : gen_no_qos_unit
        // Tie off QoS related outputs if not enabled
        assign qos_violations_o = '0;
        assign qos_req_ready = '0;
        assign qos_granted_req = '0;
        assign qos_granted_config = '0;
    end
    endgenerate

    // Connect QoS request valid/ready signals to cache interfaces
    assign qos_req_valid[0] = icache_if.req_valid; // Instruction fetch request
    assign qos_req_valid[1] = dcache_if.req_valid; // Data access request

    assign icache_if.req_ready = qos_req_ready[0];
    assign dcache_if.req_ready = qos_req_ready[1];

    // Connect granted QoS config to memory request outputs
    assign mem_req_valid_o = |qos_granted_req; // If any request is granted, memory request is valid
    assign mem_qos_config_o = qos_granted_config;

    // Mux memory request based on granted request
    always_comb begin
        mem_req_o = '0;
        if (qos_granted_req[0]) begin // Instruction fetch granted
            mem_req_o = icache_if.req;
        end else if (qos_granted_req[1]) begin // Data access granted
            mem_req_o = dcache_if.req;
        end
    end

    // Internal signals for OOO connections
    ooo_dispatch_t decode_dispatch_o;
    ooo_commit_t   ooo_commit_i;
    logic          ooo_flush_i;

    //------------------------------------------------------------------------- 
    // Instantiate OOO Engine
    //------------------------------------------------------------------------- 
    generate
        if (ENABLE_OOO) begin : gen_ooo_engine
            ooo_engine # (
                .DATA_WIDTH    (DATA_WIDTH),
                .PC_WIDTH      (PC_WIDTH),
                .REG_ADDR_WIDTH(REG_ADDR_WIDTH),
                .RS_SIZE       (RS_SIZE),
                .ROB_SIZE      (ROB_SIZE)
            ) u_ooo_engine (
                .clk_i             (clk_i),
                .rst_ni            (rst_ni),
                .flush_i           (ooo_flush_i),
                .decode_dispatch_i (decode_dispatch_o),
                .decode_ready_o    (decode_ready_o), // This will be connected to the decode stage's ready signal
                .commit_o          (ooo_commit_i),
                .commit_ready_i    (commit_ready_i) // This will be connected to the writeback stage's ready signal
            );
        end
    endgenerate

    //------------------------------------------------------------------------- 
    // Instantiate MMU
    //------------------------------------------------------------------------- 
    if (ENABLE_MMU) begin: gen_mmu
        mmu #(
            .VADDR_WIDTH(32),
            .PADDR_WIDTH(32)
        ) u_mmu (
            .clk(clk_i),
            .rst_n(rst_ni),
            .mmu_req_i(mmu_req_o),
            .mmu_req_valid_i(mmu_req_valid_o),
            .mmu_req_ready_o(mmu_req_ready_i),
            .mmu_resp_o(mmu_resp_i),
            .mmu_resp_valid_o(mmu_resp_valid_i),
            .mmu_resp_ready_i(mmu_resp_ready_o),
            .mem_arvalid_o(mem_req_valid_o), // MMU's memory requests go to main memory bus
            .mem_arready_i(mem_req_ready_i),
            .mem_araddr_o(mem_req_o.addr),
            .mem_rdata_i(mem_rsp_i.data),
            .mem_rvalid_i(mem_rsp_i.valid),
            .mem_rready_o(mem_rsp_ready_o),
            .mem_rresp_i(mem_rsp_i.resp),
            .csr_read_en_i(csr_read_en_internal),
            .csr_addr_i(csr_addr_internal),
            .csr_rdata_o(csr_rdata_internal),
            .csr_write_en_i(csr_write_en_internal),
            .csr_addr_w_i(csr_addr_w_internal),
            .csr_wdata_i(csr_wdata_internal)
        );
    end

    //------------------------------------------------------------------------- 
    // Instantiate CSR Regfile
    //------------------------------------------------------------------------- 
    csr_regfile #(
        .HART_ID(CORE_ID),
        .ENABLE_MMU(ENABLE_MMU),
        .ENABLE_QOS(ENABLE_QOS)
    ) u_csr_regfile (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .instruction_retired_i(pipeline_instruction_retired_i),
        .csr_addr_i(csr_addr_internal),
        .csr_op_i(pipeline_csr_op_i),
        .write_en_i(csr_write_en_internal),
        .rs1_data_i(csr_wdata_internal),
        .read_data_o(csr_rdata_from_csr_regfile),
        .trap_en_i(pipeline_trap_en_i),
        .mret_en_i(1'b0), // TODO: Connect to mret signal
        .mepc_i(pipeline_mepc_i),
        .mcause_i(pipeline_mcause_i),
        .mtval_i(pipeline_mtval_i),
        .mepc_o(),
        .mtvec_o(),
        .mstatus_o(),
        .mie_o(),
        .mip_o(),
        .mcause_o(),
        .mtval_o(),
        .mstatus_mie_o(),
        .mtvec_base_o(),
        .l1_icache_hit_i(1'b0), // TODO: Connect to actual cache hit signals
        .pipeline_stall_i(pipeline_stall_i)
    );

    // Mux CSR read data: prioritize MMU CSRs if MMU is enabled and address matches
    assign csr_rdata_internal = (ENABLE_MMU && (csr_addr_internal == SATP_CSR_ADDR)) ? u_mmu.csr_rdata_o : csr_rdata_from_csr_regfile;

    // Internal signal for CSR read data from csr_regfile
    logic [31:0] csr_rdata_from_csr_regfile;

    //------------------------------------------------------------------------- 
    // Pipeline Stage Instantiations
    //------------------------------------------------------------------------- 
        core_pipeline_wrapper #(
        .RESET_VECTOR(RESET_VECTOR),
        .EXECUTION_MODE(EXECUTION_MODE),
        .BRANCH_PREDICTOR_TYPE(BRANCH_PREDICTOR_TYPE),
        .ENABLE_FPU(ENABLE_FPU),
        .ENABLE_VPU(ENABLE_VPU),
        .ENABLE_ML_INFERENCE(ENABLE_ML_INFERENCE),
        .ENABLE_MMU(ENABLE_MMU),
        .ENABLE_QOS(ENABLE_QOS),
                .ENABLE_OOO(ENABLE_OOO), // Pass ENABLE_OOO parameter
        .ooo_dispatch_o(decode_dispatch_o), // Connect OOO dispatch output
        .ooo_commit_i(ooo_commit_i),       // Connect OOO commit input
        .ooo_decode_ready_i(decode_ready_o), // Connect OOO decode ready input
        .ooo_flush_i(ooo_flush_i)         // Connect OOO flush input
    ) u_core_pipeline_wrapper (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .rst_ni_sync2(rst_ni_sync2),
        .pipeline_stall_o(pipeline_stall),
        .pipeline_flush_o(pipeline_flush),
        .pc_f_o(pc_f),
        .bp_prediction_o(bp_prediction),
        .bp_update_i(bp_update),
        .icache_if(icache_if),
        .dcache_if(dcache_if),
        .fetch_exception_o(fetch_exception),
        .execute_exception_o(execute_exception),
        .memory_exception_o(memory_exception),
        .reg_file_rs1_addr_o(reg_file_rs1_addr),
        .reg_file_rs2_addr_o(reg_file_rs2_addr),
        .reg_file_rd_addr_o(reg_file_rd_addr),
        .reg_file_rs1_data_i(reg_file_rs1_data),
        .reg_file_rs2_data_i(reg_file_rs2_data),
        .reg_file_rd_data_i(reg_file_rd_data),
        .reg_file_write_en_o(reg_file_write_en),
        .instruction_retired_o(instruction_retired),
        .data_hazard_detected_o(data_hazard_detected),
        .control_hazard_detected_o(control_hazard_detected),
        .structural_hazard_detected_o(structural_hazard_detected),
        .ex_mem_branch_taken_o(ex_mem_branch_taken),
        .ex_mem_branch_target_o(ex_mem_branch_target),
        .interrupt_pending_o(interrupt_pending),
        .exception_pc_o(exception_pc),
        .exception_cause_o(exception_cause),
        .exception_o(exception_o),
        .dpu_req_o(dpu_req_o),
        .dpu_rsp_i(dpu_rsp_i),
        .dpu_busy_o(dpu_busy_o),
        .dpu_error_o(dpu_error_o),
        .mmu_instr_req_o(mmu_instr_req),
        .mmu_instr_req_valid_o(mmu_instr_req_valid),
        .mmu_instr_req_ready_i(mmu_instr_req_ready),
        .mmu_instr_resp_i(mmu_instr_resp),
        .mmu_instr_resp_valid_i(mmu_instr_resp_valid),
        .mmu_instr_resp_ready_o(mmu_instr_resp_ready),
        .mmu_data_req_o(mmu_data_req),
        .mmu_data_req_valid_o(mmu_data_req_valid),
        .mmu_data_req_ready_i(mmu_data_req_ready),
        .mmu_data_resp_i(mmu_data_resp),
        .mmu_data_resp_valid_i(mmu_data_resp_valid),
        .mmu_data_resp_ready_o(mmu_data_resp_ready),
        

    

    // Connect to performance monitoring outputs
    assign pipeline_stall_o = pipeline_stall;
    assign branch_mispredicted_o = control_hazard_detected;
    assign instruction_retired_o = instruction_retired;
    assign core_active_o = instruction_retired_o;

    

    

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
        (CORE_ID < MAX_CORES))
    else $error("Core ID exceeds maximum allowed cores");

    // AI_TAG: ASSERTION - Pipeline integrity check
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Warning
    PipelineIntegrity: assert property (@(posedge clk_i) disable iff (!rst_ni) 
        (!(pipeline_stall && pipeline_flush)))
    else $warning("Pipeline stall and flush should not occur simultaneously");

    //------------------------------------------------------------------------- 
    // Data Processing Unit (DPU) Instance (Optional)
    //------------------------------------------------------------------------- 
    generate
        if (ENABLE_DATA_ACCELERATOR) begin : gen_data_accelerator
            // AI_TAG: INTERNAL_BLOCK - Data Processing Unit
            dpu_subsystem #(
                .DPU_ID(CORE_ID),
                .ENABLE_FPU(ENABLE_FPU),
                .ENABLE_VPU(ENABLE_VPU),
                .ENABLE_ML_INFERENCE(ENABLE_ML_INFERENCE)
            ) u_dpu_subsystem (
                .clk_i(clk_i),
                .rst_ni(rst_ni_sync2),
                .dpu_req_i(dpu_req_o),
                .dpu_req_ready_o(dpu_req_o.ready),
                .dpu_rsp_o(dpu_rsp_i),
                .dpu_busy_o(dpu_busy_o),
                .dpu_error_o(dpu_error_o)
            );
        end else begin : gen_no_data_accelerator
            // Tie off DPU interface if not enabled
            assign dpu_req_o = '0;
            assign dpu_rsp_i = '0;
            assign dpu_busy_o = 1'b0;
            assign dpu_error_o = 1'b0;
        end
    endgenerate

endmodule : core_subsystem



//=============================================================================
// Dependencies: riscv_config_pkg, riscv_types_pkg, riscv_core_pkg, mmu_pkg, qos_pkg, ooo_pkg
//
// Instantiated In:
//   - rtl/core/riscv_core.sv
//
// Performance:
//   - Critical Path: Through the entire pipeline
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
//   - Constraints File: TBD
//
// Testing:
//   - Testbench: TBD
//   - Test Vectors: TBD
//
//-----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-07-07 | DesignAI           | Initial release
//============================================================================= 