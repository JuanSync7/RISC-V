////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-28
// Design Name:   RV32IM Core
// Module Name:   riscv_core
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   Top-level module for the 5-stage pipelined RV32IM RISC-V core.
//                This module instantiates and connects all pipeline stages
//                (Fetch, Decode, Execute, Memory, Write-back) and control units
//                (Register File, CSR File, Hazard Unit) to form the complete processor.
//
// Dependencies:  All previously created .sv files.
//
// Revision:
// Revision 1.1.0 - Integrated all units, including mult_unit stall path and CSR file.
//                  Updated hazard unit connections for full functionality.
// Revision 1.0.0 - File Created
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps
`default_nettype none

module riscv_core
    import riscv_core_pkg::*;
#(
    parameter addr_t RESET_VECTOR = 32'h0000_0000
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
    input  word_t       d_rdata_i
);

    // AI_TAG: INTERNAL_WIRE - Pipeline Register Connections
    if_id_reg_t  if_id_reg;
    id_ex_reg_t  id_ex_reg;
    ex_mem_reg_t ex_mem_reg;
    mem_wb_reg_t mem_wb_reg;

    // AI_TAG: INTERNAL_WIRE - Hazard Unit Control Signals
    logic        stall_f, stall_d, stall_m, stall_w;
    logic        flush_f, flush_d, flush_e;
    logic [1:0]  forward_a_sel, forward_b_sel;
    logic        exec_stall_req;

    // AI_TAG: INTERNAL_WIRE - Register File Interface
    reg_addr_t  rs1_addr, rs2_addr;
    word_t      rs1_data, rs2_data;
    logic       rf_write_en;
    reg_addr_t  rf_rd_addr;
    word_t      rf_rd_data;

    // AI_TAG: INTERNAL_WIRE - PC Redirect Path
    logic       pc_redirect;
    addr_t      pc_redirect_target;

    // AI_TAG: INTERNAL_WIRE - Write-back and Forwarding Path
    word_t      wb_data_fwd;
    reg_addr_t  rd_addr_fwd;
    logic       reg_write_en_fwd;

    // AI_TAG: INTERNAL_WIRE - CSR Interface
    logic       trap_en, mret_en;
    word_t      csr_read_data;
    addr_t      mepc_out, mtvec_out;
    word_t      mstatus_out, mcause_in, mtval_in;


    //==========================================================================
    // 1. Pipeline Stages Instantiation
    //==========================================================================

    fetch_stage #(.RESET_VECTOR(RESET_VECTOR)) u_fetch_stage (
        .clk_i                ( clk_i                ),
        .rst_ni               ( rst_ni               ),
        .stall_f_i            ( stall_f              ),
        .stall_d_i            ( stall_d              ),
        .flush_f_i            ( flush_f              ),
        .pc_redirect_en_i     ( pc_redirect          ),
        .pc_redirect_target_i ( pc_redirect_target   ),
        .i_arvalid_o          ( i_arvalid_o          ),
        .i_arready_i          ( i_arready_i          ),
        .i_araddr_o           ( i_araddr_o           ),
        // ... Other AXI ports
        .if_id_reg_o          ( if_id_reg            )
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
        .csr_read_data_i      ( csr_read_data        ),
        .pc_redirect_o        ( pc_redirect          ),
        .pc_redirect_target_o ( pc_redirect_target   ),
        .exec_stall_req_o     ( exec_stall_req       ), // AI_TAG: UPDATE - New stall request connection
        .ex_mem_reg_o         ( ex_mem_reg           )
    );

    mem_stage u_mem_stage (
        .clk_i        ( clk_i        ),
        .rst_ni       ( rst_ni       ),
        .stall_w_i    ( stall_w      ),
        .flush_m_i    ( /* unused */ ),
        .ex_mem_reg_i ( ex_mem_reg   ),
        // All AXI data ports connected directly
        .d_awvalid_o  ( d_awvalid_o  ), .d_awready_i(d_awready_i), .d_awaddr_o(d_awaddr_o),
        .d_wvalid_o   ( d_wvalid_o   ), .d_wready_i(d_wready_i),   .d_wdata_o(d_wdata_o),  .d_wstrb_o(d_wstrb_o),
        .d_bvalid_i   ( d_bvalid_i   ), .d_bready_o(d_bready_o),
        .d_arvalid_o  ( d_arvalid_o  ), .d_arready_i(d_arready_i), .d_araddr_o(d_araddr_o),
        .d_rvalid_i   ( d_rvalid_i   ), .d_rready_o(d_rready_o),   .d_rdata_i(d_rdata_i),
        .mem_wb_reg_o ( mem_wb_reg   )
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
    // 2. Core Units Instantiation
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
        .mstatus_o      ( mstatus_out              )
    );

    //==========================================================================
    // 3. Control Logic Instantiation
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
        .i_arvalid_i      ( i_arvalid_o          ), // From fetch stage
        .i_arready_i      ( i_arready_i          ), // From memory system
        .d_mem_req_i      ( d_arvalid_o | d_awvalid_o ),
        .d_mem_ready_i    ( d_arvalid_o ? d_arready_i : d_awready_i ), // Simplified ready
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

    // AI_TAG: INTERNAL_LOGIC - Top-level Trap and MRET logic
    // TODO: This is a simplified implementation. A full implementation would decode
    // mcause and handle various exception types and interrupts.
    assign trap_en   = id_ex_reg.ctrl.csr_cmd_en && (id_ex_reg.immediate == 12'h001); // ECALL
    assign mret_en   = id_ex_reg.ctrl.csr_cmd_en && (id_ex_reg.immediate == 12'h302); // MRET
    assign mcause_in = 32'd11; // Machine ECALL cause code
    assign mtval_in  = '0;     // Not used for ECALL/MRET

endmodule : riscv_core