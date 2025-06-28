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
//   Top-level module for the 5-stage pipelined RV32IM RISC-V core. This
//   module instantiates and connects all pipeline stages (Fetch, Decode,
//   Execute, Memory, Write-back) and control units (Register File, CSR
//   File, Hazard Unit) to form the complete processor.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module riscv_core
    import riscv_core_pkg::*;
#(
    parameter addr_t RESET_VECTOR = 32'h0000_0000,
    // AI_TAG: PARAM_DESC - PROTOCOL_TYPE - Memory protocol type for the memory wrapper.
    parameter string PROTOCOL_TYPE = "AXI4"
)
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- AXI4 Instruction Memory Interface (Master) ---
    output logic        i_arvalid_o,
    input  logic        i_arready_i,
    output addr_t       i_araddr_o,
    output logic [2:0]  i_arprot_o,
    output logic [3:0]  i_arcache_o,
    output logic [1:0]  i_arsize_o,
    input  word_t       i_rdata_i,
    input  logic        i_rvalid_i,
    output logic        i_rready_o,

    // --- AXI4 Data Memory Interface (Master) ---
    output logic        d_awvalid_o,
    input  logic        d_awready_i,
    output addr_t       d_awaddr_o,
    output logic [2:0]  d_awprot_o,
    output logic        d_wvalid_o,
    input  logic        d_wready_i,
    output word_t       d_wdata_o,
    output logic [3:0]  d_wstrb_o,
    input  logic        d_bvalid_i,
    output logic        d_bready_o,
    output logic        d_arvalid_o,
    input  logic        d_arready_i,
    output addr_t       d_araddr_o,
    output logic [2:0]  d_arprot_o,
    input  logic        d_rvalid_i,
    output logic        d_rready_o,
    input  word_t       d_rdata_i,

    // --- Performance Counters Interface ---
    // AI_TAG: PORT_DESC - perf_hit_count_o - Total number of cache hits.
    output logic [31:0] perf_hit_count_o,
    // AI_TAG: PORT_DESC - perf_miss_count_o - Total number of cache misses.
    output logic [31:0] perf_miss_count_o,
    // AI_TAG: PORT_DESC - perf_flush_count_o - Total number of cache flushes.
    output logic [31:0] perf_flush_count_o,
    // AI_TAG: PORT_DESC - perf_total_requests_o - Total number of cache requests.
    output logic [31:0] perf_total_requests_o,
    // AI_TAG: PORT_DESC - perf_hit_rate_o - Cache hit rate (0-100, scaled by 100).
    output logic [31:0] perf_hit_rate_o,
    // AI_TAG: PORT_DESC - perf_counter_reset_i - Reset all performance counters.
    input  logic        perf_counter_reset_i,

    // --- Interrupt Interface ---
    // AI_TAG: PORT_DESC - m_software_interrupt_i - Machine software interrupt
    input  logic        m_software_interrupt_i,
    // AI_TAG: PORT_DESC - m_timer_interrupt_i - Machine timer interrupt
    input  logic        m_timer_interrupt_i,
    // AI_TAG: PORT_DESC - m_external_interrupt_i - Machine external interrupt
    input  logic        m_external_interrupt_i
);

    // AI_TAG: INTERNAL_WIRE - Pipeline register signals
    if_id_reg_t  if_id_reg;
    id_ex_reg_t  id_ex_reg;
    ex_mem_reg_t ex_mem_reg;
    mem_wb_reg_t mem_wb_reg;

    // AI_TAG: INTERNAL_WIRE - Register file interface signals
    reg_addr_t rs1_addr, rs2_addr;
    word_t     rs1_data, rs2_data;
    logic      rf_write_en;
    reg_addr_t rf_rd_addr;
    word_t     rf_rd_data;

    // AI_TAG: INTERNAL_WIRE - Forwarding and hazard control signals
    logic [1:0] forward_a_sel, forward_b_sel;
    logic       stall_f, stall_d, stall_m, stall_w;
    logic       flush_f, flush_d, flush_e;
    logic       pc_redirect;
    addr_t      pc_redirect_target;
    logic       exec_stall_req;

    // AI_TAG: INTERNAL_WIRE - Write-back forwarding signals
    word_t     wb_data_fwd;
    reg_addr_t rd_addr_fwd;
    logic      reg_write_en_fwd;

    // AI_TAG: INTERNAL_WIRE - Branch prediction signals
    branch_update_t bp_update;

    // AI_TAG: INTERNAL_WIRE - CSR interface signals
    word_t csr_read_data;

    // AI_TAG: INTERNAL_WIRE - Exception handling signals
    exception_info_t fetch_exception;
    exception_info_t execute_exception;
    exception_info_t memory_exception;
    exception_info_t writeback_exception;
    logic exception_valid;
    exception_info_t exception_info;
    addr_t trap_vector;
    logic pipeline_flush;
    interrupt_info_t interrupt_info;

    // AI_TAG: INTERNAL_WIRE - Enhanced CSR output signals
    word_t mie_out, mip_out, mcause_out, mtval_out;
    logic mstatus_mie_out;
    logic [1:0] mtvec_mode_out;
    addr_t mtvec_base_out;

    // AI_TAG: INTERNAL_WIRE - Exception PC redirect signals
    logic pc_redirect_exception;
    addr_t pc_redirect_target_exception;
    logic pc_redirect_combined;
    addr_t pc_redirect_target_combined;

    // AI_TAG: INTERNAL_WIRE - Memory Wrapper Interface
    logic        instr_req_valid;
    logic        instr_req_ready;
    addr_t       instr_req_addr;
    logic        instr_rsp_valid;
    logic        instr_rsp_ready;
    word_t       instr_rsp_data;
    logic        instr_rsp_error;
    
    logic        data_req_valid;
    logic        data_req_ready;
    addr_t       data_req_addr;
    logic        data_req_write;
    logic [2:0]  data_req_size;
    word_t       data_req_data;
    logic [3:0]  data_req_strb;
    logic        data_rsp_valid;
    logic        data_rsp_ready;
    word_t       data_rsp_data;
    logic        data_rsp_error;

    //==========================================================================
    // 1. Memory Wrapper Instantiation
    //==========================================================================

    memory_wrapper #(
        .PROTOCOL_TYPE(PROTOCOL_TYPE)
    ) u_memory_wrapper (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        
        // Instruction memory interface
        .instr_req_valid_i(instr_req_valid),
        .instr_req_ready_o(instr_req_ready),
        .instr_req_addr_i(instr_req_addr),
        .instr_rsp_valid_o(instr_rsp_valid),
        .instr_rsp_ready_i(instr_rsp_ready),
        .instr_rsp_data_o(instr_rsp_data),
        .instr_rsp_error_o(instr_rsp_error),
        
        // Data memory interface
        .data_req_valid_i(data_req_valid),
        .data_req_ready_o(data_req_ready),
        .data_req_addr_i(data_req_addr),
        .data_req_write_i(data_req_write),
        .data_req_size_i(data_req_size),
        .data_req_data_i(data_req_data),
        .data_req_strb_i(data_req_strb),
        .data_rsp_valid_o(data_rsp_valid),
        .data_rsp_ready_i(data_rsp_ready),
        .data_rsp_data_o(data_rsp_data),
        .data_rsp_error_o(data_rsp_error),
        
        // AXI4 interface (for backward compatibility)
        .i_arvalid_o(i_arvalid_o),
        .i_arready_i(i_arready_i),
        .i_araddr_o(i_araddr_o),
        .i_arprot_o(i_arprot_o),
        .i_arcache_o(i_arcache_o),
        .i_arsize_o(i_arsize_o),
        .i_rdata_i(i_rdata_i),
        .i_rvalid_i(i_rvalid_i),
        .i_rready_o(i_rready_o),
        .d_awvalid_o(d_awvalid_o),
        .d_awready_i(d_awready_i),
        .d_awaddr_o(d_awaddr_o),
        .d_awprot_o(d_awprot_o),
        .d_wvalid_o(d_wvalid_o),
        .d_wready_i(d_wready_i),
        .d_wdata_o(d_wdata_o),
        .d_wstrb_o(d_wstrb_o),
        .d_bvalid_i(d_bvalid_i),
        .d_bready_o(d_bready_o),
        .d_arvalid_o(d_arvalid_o),
        .d_arready_i(d_arready_i),
        .d_araddr_o(d_araddr_o),
        .d_arprot_o(d_arprot_o),
        .d_rvalid_i(d_rvalid_i),
        .d_rready_o(d_rready_o),
        .d_rdata_i(d_rdata_i)
    );

    //==========================================================================
    // 2. Pipeline Stages Instantiation
    //==========================================================================

    fetch_stage #(.RESET_VECTOR(RESET_VECTOR)) u_fetch_stage (
        .clk_i                ( clk_i                ),
        .rst_ni               ( rst_ni               ),
        .stall_f_i            ( stall_f              ),
        .stall_d_i            ( stall_d              ),
        .flush_f_i            ( flush_f              ),
        .pc_redirect_en_i     ( pc_redirect          ),
        .pc_redirect_target_i ( pc_redirect_target   ),
        .bp_update_i          ( bp_update            ),
        .instr_req_valid_o    ( instr_req_valid      ),
        .instr_req_ready_i    ( instr_req_ready      ),
        .instr_req_addr_o     ( instr_req_addr       ),
        .instr_rsp_valid_i    ( instr_rsp_valid      ),
        .instr_rsp_ready_o    ( instr_rsp_ready      ),
        .instr_rsp_data_i     ( instr_rsp_data       ),
        .instr_rsp_error_i    ( instr_rsp_error      ),
        .if_id_reg_o          ( if_id_reg            ),
        .pc_f_o               ( /* unused */         ),
        .bp_prediction_o      ( /* unused - available for monitoring */ ),
        .exception_o          ( fetch_exception      ),
        // --- Performance Counters Interface ---
        // AI_TAG: PORT_DESC - perf_hit_count_o - Total number of cache hits.
        .perf_hit_count_o     ( perf_hit_count_o     ),
        // AI_TAG: PORT_DESC - perf_miss_count_o - Total number of cache misses.
        .perf_miss_count_o    ( perf_miss_count_o    ),
        // AI_TAG: PORT_DESC - perf_flush_count_o - Total number of cache flushes.
        .perf_flush_count_o   ( perf_flush_count_o   ),
        // AI_TAG: PORT_DESC - perf_total_requests_o - Total number of cache requests.
        .perf_total_requests_o( perf_total_requests_o),
        // AI_TAG: PORT_DESC - perf_hit_rate_o - Cache hit rate (0-100, scaled by 100).
        .perf_hit_rate_o      ( perf_hit_rate_o      ),
        // AI_TAG: PORT_DESC - perf_counter_reset_i - Reset all performance counters.
        .perf_counter_reset_i ( perf_counter_reset_i  )
    );

    decode_stage u_decode_stage (
        .clk_i        ( clk_i        ),
        .rst_ni       ( rst_ni       ),
        .stall_e_i    ( stall_d      ), // Stall on ID/EX register is controlled by stall_d
        .flush_d_i    ( flush_d      ),
        .if_id_reg_i  ( if_id_reg    ),
        .rs1_addr_o   ( rs1_addr     ),
        .rs2_addr_o   ( rs2_addr     ),
        .rs1_data_i   ( rs1_data     ),
        .rs2_data_i   ( rs2_data     ),
        .id_ex_reg_o  ( id_ex_reg    )
    );

    execute_stage u_execute_stage (
        .clk_i                ( clk_i                ),
        .rst_ni               ( rst_ni               ),
        .stall_m_i            ( stall_m              ),
        .flush_e_i            ( flush_e              ), // AI_TAG: UPDATE - Now driven by dedicated flush_e signal
        .forward_a_sel_i      ( forward_a_sel        ),
        .forward_b_sel_i      ( forward_b_sel        ),
        .id_ex_reg_i          ( id_ex_reg            ),
        .ex_mem_reg_m_i       ( ex_mem_reg           ),
        .wb_data_w_i          ( wb_data_fwd          ),
        .pc_redirect_o        ( pc_redirect          ),
        .pc_redirect_target_o ( pc_redirect_target   ),
        .exec_stall_req_o     ( exec_stall_req       ), // AI_TAG: UPDATE - New stall request connection
        .ex_mem_reg_o         ( ex_mem_reg           ),
        .overflow_o           ( /* unused - available for exception handling */ ),
        .bp_update_o          ( bp_update            ),
        .exception_o          ( execute_exception    )
    );

    mem_stage u_mem_stage (
        .clk_i        ( clk_i        ),
        .rst_ni       ( rst_ni       ),
        .stall_w_i    ( stall_w      ),
        .flush_m_i    ( /* unused */ ),
        .ex_mem_reg_i ( ex_mem_reg   ),
        // Memory wrapper data interface
        .data_req_valid_o ( data_req_valid ),
        .data_req_ready_i ( data_req_ready ),
        .data_req_addr_o  ( data_req_addr  ),
        .data_req_write_o ( data_req_write ),
        .data_req_size_o  ( data_req_size  ),
        .data_req_data_o  ( data_req_data  ),
        .data_req_strb_o  ( data_req_strb  ),
        .data_rsp_valid_i ( data_rsp_valid ),
        .data_rsp_ready_o ( data_rsp_ready ),
        .data_rsp_data_i  ( data_rsp_data  ),
        .data_rsp_error_i ( data_rsp_error ),
        .mem_wb_reg_o ( mem_wb_reg   ),
        .exception_o ( memory_exception )
    );

    writeback_stage u_writeback_stage (
        .clk_i              ( clk_i              ),
        .rst_ni             ( rst_ni             ),
        .mem_wb_reg_i       ( mem_wb_reg         ),
        .write_en_o         ( rf_write_en        ),
        .rd_addr_o          ( rf_rd_addr         ),
        .rd_data_o          ( rf_rd_data         ),
        .wb_data_fwd_o      ( wb_data_fwd        ),
        .rd_addr_fwd_o      ( rd_addr_fwd        ),
        .reg_write_en_fwd_o ( reg_write_en_fwd   )
    );

    //==========================================================================
    // 3. Core Units Instantiation
    //==========================================================================

    reg_file u_reg_file ( .clk_i(clk_i), .rst_ni(rst_ni), .write_en_i(rf_write_en), .rd_addr_i(rf_rd_addr), .rd_data_i(rf_rd_data), .rs1_addr_i(rs1_addr), .rs1_data_o(rs1_data), .rs2_addr_i(rs2_addr), .rs2_data_o(rs2_data) );

    csr_regfile u_csr_regfile (
        .clk_i          ( clk_i                    ),
        .rst_ni         ( rst_ni                   ),
        .csr_addr_i     ( id_ex_reg.immediate[11:0]), // Address comes from immediate field
        .csr_op_i       ( id_ex_reg.ctrl.funct3    ),
        .write_en_i     ( id_ex_reg.ctrl.csr_cmd_en),
        .rs1_data_i     ( id_ex_reg.rs1_data       ),
        .read_data_o    ( csr_read_data            ),
        .trap_en_i      ( trap_en                  ),
        .mret_en_i      ( mret_en                  ),
        .mepc_i         ( id_ex_reg.pc             ),
        .mcause_i       ( mcause_in                ),
        .mtval_i        ( mtval_in                 ),
        .mepc_o         ( mepc_out                 ),
        .mtvec_o        ( mtvec_out                ),
        .mstatus_o      ( mstatus_out              ),
        .mie_o          ( mie_out                  ),
        .mip_o          ( mip_out                  ),
        .mcause_o       ( mcause_out               ),
        .mtval_o        ( mtval_out                ),
        .mstatus_mie_o  ( mstatus_mie_out          ),
        .mtvec_mode_o   ( mtvec_mode_out           ),
        .mtvec_base_o   ( mtvec_base_out           )
    );

    // AI_TAG: NEW_MODULE - Exception Handler Instantiation
    exception_handler u_exception_handler (
        .clk_i                    ( clk_i                    ),
        .rst_ni                   ( rst_ni                   ),
        .fetch_exception_i        ( fetch_exception          ),
        .execute_exception_i      ( execute_exception        ),
        .memory_exception_i       ( memory_exception         ),
        .writeback_exception_i    ( writeback_exception      ),
        .m_software_interrupt_i   ( m_software_interrupt_i   ),
        .m_timer_interrupt_i      ( m_timer_interrupt_i      ),
        .m_external_interrupt_i   ( m_external_interrupt_i   ),
        .mstatus_mie_i            ( mstatus_mie_out          ),
        .mie_msie_i               ( mie_out[3]               ),
        .mie_mtie_i               ( mie_out[7]               ),
        .mie_meie_i               ( mie_out[11]              ),
        .mip_msip_i               ( mip_out[3]               ),
        .mip_mtip_i               ( mip_out[7]               ),
        .mip_meip_i               ( mip_out[11]              ),
        .mtvec_base_i             ( mtvec_base_out           ),
        .mtvec_mode_i             ( mtvec_mode_out           ),
        .exception_valid_o        ( exception_valid          ),
        .exception_info_o         ( exception_info           ),
        .trap_vector_o            ( trap_vector              ),
        .pipeline_flush_o         ( pipeline_flush           ),
        .interrupt_info_o         ( interrupt_info           )
    );

    //==========================================================================
    // 4. Control Logic Instantiation
    //==========================================================================

    // AI_TAG: UPDATE - Hazard unit instantiation now fully connected for stalls.
    hazard_unit u_hazard_unit (
        .rs1_addr_d_i     ( rs1_addr             ),
        .rs2_addr_d_i     ( rs2_addr             ),
        .id_ex_reg_i      ( id_ex_reg            ),
        .ex_mem_reg_i     ( ex_mem_reg           ),
        .mem_wb_reg_i     ( mem_wb_reg           ),
        .pc_redirect_e_i  ( pc_redirect          ),
        .exec_stall_req_i ( exec_stall_req       ),
        .i_arvalid_i      ( instr_req_valid      ), // From fetch stage via memory wrapper
        .i_arready_i      ( instr_req_ready      ), // From memory wrapper
        .d_mem_req_i      ( data_req_valid       ), // From memory stage via memory wrapper
        .d_mem_ready_i    ( data_req_ready       ), // From memory wrapper
        .stall_f_o        ( stall_f              ),
        .stall_d_o        ( stall_d              ),
        .stall_m_o        ( stall_m              ),
        .stall_w_o        ( stall_w              ),
        .flush_f_o        ( flush_f              ),
        .flush_d_o        ( flush_d              ),
        .flush_e_o        ( flush_e              ),
        .forward_a_sel_o  ( forward_a_sel        ),
        .forward_b_sel_o  ( forward_b_sel        )
    );

    // AI_TAG: INTERNAL_LOGIC - Enhanced Exception and Trap Logic
    // Use the exception handler output for trap detection and handling
    assign trap_en = exception_valid;
    assign mret_en = id_ex_reg.ctrl.csr_cmd_en && (id_ex_reg.immediate[11:0] == 12'h302); // MRET
    assign mcause_in = exception_info.cause;
    assign mtval_in = exception_info.tval;

    // AI_TAG: INTERNAL_LOGIC - PC Redirect for Exceptions
    // Override normal PC redirect when exception is taken
    assign pc_redirect_exception = exception_valid;
    assign pc_redirect_target_exception = trap_vector;
    
    // Combine normal PC redirect with exception redirect
    assign pc_redirect_combined = pc_redirect || pc_redirect_exception;
    assign pc_redirect_target_combined = pc_redirect_exception ? pc_redirect_target_exception : pc_redirect_target;
    
    // Update fetch stage connections
    assign pc_redirect = pc_redirect_combined;
    assign pc_redirect_target = pc_redirect_target_combined;

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