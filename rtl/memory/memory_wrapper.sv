//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: memory_wrapper.sv
// Module: memory_wrapper
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Memory wrapper that abstracts protocol details from pipeline stages.
//   Provides a clean interface for instruction and data memory access,
//   internally using protocol-agnostic memory_req_rsp_if.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module memory_wrapper #(
    // AI_TAG: PARAM_DESC - PROTOCOL_TYPE - Memory protocol type.
    // AI_TAG: PARAM_USAGE - Determines which protocol adapter to use.
    // AI_TAG: PARAM_CONSTRAINTS - Must be "AXI4", "CHI", or "TILELINK".
    parameter string PROTOCOL_TYPE = "AXI4",
    
    // AI_TAG: PARAM_DESC - ID_WIDTH - Width of transaction ID.
    parameter integer ID_WIDTH = 4,
    
    // AI_TAG: PARAM_DESC - ADDR_WIDTH - Width of address signals.
    parameter integer ADDR_WIDTH = 32,
    
    // AI_TAG: PARAM_DESC - DATA_WIDTH - Width of data signals.
    parameter integer DATA_WIDTH = 32
) (
    // AI_TAG: PORT_DESC - clk_i - System clock.
    input  logic        clk_i,
    
    // AI_TAG: PORT_DESC - rst_ni - Asynchronous active-low reset.
    input  logic        rst_ni,

    // --- Instruction Memory Interface (for Fetch Stage) ---
    // AI_TAG: PORT_DESC - instr_req_valid_i - Instruction request valid.
    input  logic        instr_req_valid_i,
    
    // AI_TAG: PORT_DESC - instr_req_ready_o - Instruction request ready.
    output logic        instr_req_ready_o,
    
    // AI_TAG: PORT_DESC - instr_req_addr_i - Instruction request address.
    input  addr_t       instr_req_addr_i,
    
    // AI_TAG: PORT_DESC - instr_rsp_valid_o - Instruction response valid.
    output logic        instr_rsp_valid_o,
    
    // AI_TAG: PORT_DESC - instr_rsp_ready_i - Instruction response ready.
    input  logic        instr_rsp_ready_i,
    
    // AI_TAG: PORT_DESC - instr_rsp_data_o - Instruction response data.
    output word_t       instr_rsp_data_o,
    
    // AI_TAG: PORT_DESC - instr_rsp_error_o - Instruction response error.
    output logic        instr_rsp_error_o,

    // --- Data Memory Interface (for Memory Stage) ---
    // AI_TAG: PORT_DESC - data_req_valid_i - Data request valid.
    input  logic        data_req_valid_i,
    
    // AI_TAG: PORT_DESC - data_req_ready_o - Data request ready.
    output logic        data_req_ready_o,
    
    // AI_TAG: PORT_DESC - data_req_addr_i - Data request address.
    input  addr_t       data_req_addr_i,
    
    // AI_TAG: PORT_DESC - data_req_write_i - Data request write flag.
    input  logic        data_req_write_i,
    
    // AI_TAG: PORT_DESC - data_req_size_i - Data request size.
    input  logic [2:0]  data_req_size_i,
    
    // AI_TAG: PORT_DESC - data_req_data_i - Data request write data.
    input  word_t       data_req_data_i,
    
    // AI_TAG: PORT_DESC - data_req_strb_i - Data request write strobes.
    input  logic [3:0]  data_req_strb_i,
    
    // AI_TAG: PORT_DESC - data_rsp_valid_o - Data response valid.
    output logic        data_rsp_valid_o,
    
    // AI_TAG: PORT_DESC - data_rsp_ready_i - Data response ready.
    input  logic        data_rsp_ready_i,
    
    // AI_TAG: PORT_DESC - data_rsp_data_o - Data response data.
    output word_t       data_rsp_data_o,
    
    // AI_TAG: PORT_DESC - data_rsp_error_o - Data response error.
    output logic        data_rsp_error_o,

    // --- AXI4 Interface (for backward compatibility) ---
    // Instruction Memory AXI4
    output logic                    i_arvalid_o,
    input  logic                    i_arready_i,
    output addr_t                   i_araddr_o,
    output logic [2:0]              i_arprot_o,
    output logic [3:0]              i_arcache_o,
    output logic [1:0]              i_arsize_o,
    input  word_t                   i_rdata_i,
    input  logic                    i_rvalid_i,
    output logic                    i_rready_o,
    
    // Data Memory AXI4
    output logic                    d_awvalid_o,
    input  logic                    d_awready_i,
    output addr_t                   d_awaddr_o,
    output logic [2:0]              d_awprot_o,
    output logic                    d_wvalid_o,
    input  logic                    d_wready_i,
    output word_t                   d_wdata_o,
    output logic [3:0]              d_wstrb_o,
    input  logic                    d_bvalid_i,
    output logic                    d_bready_o,
    output logic                    d_arvalid_o,
    input  logic                    d_arready_i,
    output addr_t                   d_araddr_o,
    output logic [2:0]              d_arprot_o,
    input  logic                    d_rvalid_i,
    output logic                    d_rready_o,
    input  word_t                   d_rdata_i,

    // --- CHI Interface (enabled when PROTOCOL_TYPE == "CHI") ---
    chi_if.rn                       chi_instr_if,
    chi_if.rn                       chi_data_if,

    // --- TileLink Interface (enabled when PROTOCOL_TYPE == "TILELINK") ---
    tilelink_if.master              tl_instr_if,
    tilelink_if.master              tl_data_if,

    // --- Status and Performance Monitoring ---
    output logic [31:0]             protocol_latency_o,
    output logic [31:0]             protocol_throughput_o,
    output logic [15:0]             protocol_error_count_o
);

    // AI_TAG: INTERNAL_LOGIC - Memory interfaces for protocol adapters
    memory_req_rsp_if instr_mem_if();
    memory_req_rsp_if dcache_cpu_if(); // Interface between memory_wrapper and D-Cache (CPU side)
    memory_req_rsp_if dcache_mem_if(); // Interface between D-Cache and protocol adapter (Memory side)
    
    // AI_TAG: INTERNAL_LOGIC - Transaction ID counters
    logic [ID_WIDTH-1:0] instr_id_counter;
    logic [ID_WIDTH-1:0] data_id_counter;
    
    // AI_TAG: INTERNAL_LOGIC - Request tracking
    logic [ID_WIDTH-1:0] pending_instr_id;
    logic [ID_WIDTH-1:0] pending_data_id;
    logic pending_instr_valid;
    logic pending_data_valid;

    // AI_TAG: INTERNAL_LOGIC - Bus watchdog timers
    logic instr_timeout;
    logic data_timeout;

    bus_watchdog #(
        .TIMEOUT_CYCLES(riscv_verification_config_pkg::BUS_TIMEOUT_CYCLES)
    ) instr_watchdog (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .enable_i(pending_instr_valid),
        .timeout_o(instr_timeout)
    );

    bus_watchdog #(
        .TIMEOUT_CYCLES(riscv_verification_config_pkg::BUS_TIMEOUT_CYCLES)
    ) data_watchdog (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .enable_i(pending_data_valid),
        .timeout_o(data_timeout)
    );

    // AI_TAG: INTERNAL_LOGIC - Performance monitoring
    logic [31:0] cycle_counter;
    logic [31:0] transaction_counter;
    logic [15:0] error_counter;
    logic [31:0] latency_accumulator;
    logic [31:0] latency_counter;
    
    // AI_TAG: INTERNAL_LOGIC - Connect clock and reset to interfaces
    assign instr_mem_if.clk = clk_i;
    assign instr_mem_if.rst_n = rst_ni;
    assign data_mem_if.clk = clk_i;
    assign data_mem_if.rst_n = rst_ni;
    
    // AI_TAG: INTERNAL_LOGIC - Instruction memory interface control
    always_comb begin
        // Request side
        instr_mem_if.req_valid = instr_req_valid_i;
        instr_mem_if.req.addr = instr_req_addr_i;
        instr_mem_if.req.size = 3'b010; // 4 bytes for instructions
        instr_mem_if.req.write = 1'b0;  // Instructions are read-only
        instr_mem_if.req.data = '0;
        instr_mem_if.req.strb = 4'b1111;
        instr_mem_if.req.id = instr_id_counter;
        instr_mem_if.req.cacheable = 1'b1;
        instr_mem_if.req.prot = 2'b10; // Privileged, secure
        
        instr_req_ready_o = instr_mem_if.req_ready;
        
        // Response side
        instr_rsp_valid_o = instr_mem_if.rsp_valid;
        instr_rsp_data_o = instr_mem_if.rsp.data;
        instr_rsp_error_o = instr_mem_if.rsp.error || instr_timeout;
        instr_mem_if.rsp_ready = instr_rsp_ready_i;
    end
    
    // AI_TAG: INTERNAL_LOGIC - Data memory interface control (CPU side to D-Cache)
    always_comb begin
        // Request side
        dcache_cpu_if.req_valid = data_req_valid_i;
        dcache_cpu_if.req.addr = data_req_addr_i;
        dcache_cpu_if.req.size = data_req_size_i;
        dcache_cpu_if.req.write = data_req_write_i;
        dcache_cpu_if.req.data = data_req_data_i;
        dcache_cpu_if.req.strb = data_req_strb_i;
        dcache_cpu_if.req.id = data_id_counter;
        dcache_cpu_if.req.cacheable = 1'b1;
        dcache_cpu_if.req.prot = 2'b10; // Privileged, secure
        
        data_req_ready_o = dcache_cpu_if.req_ready;
        
        // Response side
        data_rsp_valid_o = dcache_cpu_if.rsp_valid;
        data_rsp_data_o = dcache_cpu_if.rsp.data;
        data_rsp_error_o = dcache_cpu_if.rsp.error || data_timeout;
        dcache_cpu_if.rsp_ready = data_rsp_ready_i;
    end

    // AI_TAG: INTERNAL_LOGIC - D-Cache instantiation
    dcache #(
        .DCACHE_SIZE(DEFAULT_L1_DCACHE_SIZE),
        .DCACHE_LINE_SIZE(DEFAULT_L1_DCACHE_LINE_SIZE),
        .DCACHE_WAYS(DEFAULT_L1_DCACHE_WAYS)
    ) u_dcache (
        .clk_i(clk_i),
        .rst_ni(rst_ni),

        // CPU Interface
        .req_valid_i(dcache_cpu_if.req_valid),
        .req_ready_o(dcache_cpu_if.req_ready),
        .req_addr_i(dcache_cpu_if.req.addr),
        .req_write_i(dcache_cpu_if.req.write),
        .req_wdata_i(dcache_cpu_if.req.data),
        .req_wstrb_i(dcache_cpu_if.req.strb),
        .rsp_valid_o(dcache_cpu_if.rsp_valid),
        .rsp_ready_i(dcache_cpu_if.rsp_ready),
        .rsp_rdata_o(dcache_cpu_if.rsp.data),
        .rsp_error_o(dcache_cpu_if.rsp.error),

        // Memory Interface
        .mem_req_valid_o(dcache_mem_if.req_valid),
        .mem_req_ready_i(dcache_mem_if.req_ready),
        .mem_req_o(dcache_mem_if.req),
        .mem_rsp_valid_i(dcache_mem_if.rsp_valid),
        .mem_rsp_ready_o(dcache_mem_if.rsp_ready),
        .mem_rsp_i(dcache_mem_if.rsp)
    );
    
    // AI_TAG: INTERNAL_LOGIC - Transaction ID counters
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            instr_id_counter <= '0;
            data_id_counter <= '0;
            pending_instr_valid <= 1'b0;
            pending_data_valid <= 1'b0;
            pending_instr_id <= '0;
            pending_data_id <= '0;
        end else begin
            if (instr_req_valid_i && instr_req_ready_o) begin
                instr_id_counter <= instr_id_counter + 1;
                pending_instr_valid <= 1'b1;
                pending_instr_id <= instr_id_counter;
            end
            if (data_req_valid_i && data_req_ready_o) begin
                data_id_counter <= data_id_counter + 1;
                pending_data_valid <= 1'b1;
                pending_data_id <= data_id_counter;
            end
            
            // Clear pending flags when responses are received
            if (instr_rsp_valid_o && instr_rsp_ready_i) begin
                pending_instr_valid <= 1'b0;
            end
            if (data_rsp_valid_o && data_rsp_ready_i) begin
                pending_data_valid <= 1'b0;
            end
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Performance monitoring counters
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            cycle_counter <= '0;
            transaction_counter <= '0;
            error_counter <= '0;
            latency_accumulator <= '0;
            latency_counter <= '0;
        end else begin
            cycle_counter <= cycle_counter + 1;
            
            // Count transactions
            if ((instr_req_valid_i && instr_req_ready_o) || (data_req_valid_i && data_req_ready_o)) begin
                transaction_counter <= transaction_counter + 1;
            end
            
            // Count errors
            if ((instr_rsp_valid_o && instr_rsp_error_o) || (data_rsp_valid_o && data_rsp_error_o)) begin
                error_counter <= error_counter + 1;
            end
            
            // Track latency (simplified)
            if (pending_instr_valid || pending_data_valid) begin
                latency_accumulator <= latency_accumulator + 1;
            end
            
            if ((instr_rsp_valid_o && instr_rsp_ready_i) || (data_rsp_valid_o && data_rsp_ready_i)) begin
                latency_counter <= latency_counter + 1;
            end
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Performance monitoring outputs
    assign protocol_latency_o = (latency_counter > 0) ? (latency_accumulator / latency_counter) : 32'h0;
    assign protocol_throughput_o = (cycle_counter > 0) ? (transaction_counter * 1000) / cycle_counter : 32'h0;
    assign protocol_error_count_o = error_counter;
    
    // AI_TAG: INTERNAL_LOGIC - Protocol adapter instantiation
    generate
        if (PROTOCOL_TYPE == "AXI4") begin : axi4_adapter_gen
            // AXI4 protocol adapter for instruction memory
            axi4_adapter #(
                .ID_WIDTH(ID_WIDTH),
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH)
            ) instr_axi4_adapter (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mem_if(instr_mem_if.slave),
                .m_axi_arvalid_o(i_arvalid_o),
                .m_axi_arready_i(i_arready_i),
                .m_axi_araddr_o(i_araddr_o),
                .m_axi_arprot_o(i_arprot_o),
                .m_axi_arcache_o(i_arcache_o),
                .m_axi_arsize_o(i_arsize_o),
                .m_axi_arlen_o(),
                .m_axi_arburst_o(),
                .m_axi_arid_o(),
                .m_axi_rvalid_i(i_rvalid_i),
                .m_axi_rready_o(i_rready_o),
                .m_axi_rdata_i(i_rdata_i),
                .m_axi_rresp_i(2'b00),
                .m_axi_rlast_i(1'b1),
                .m_axi_rid_i('0),
                .m_axi_awvalid_o(),
                .m_axi_awready_i(1'b1),
                .m_axi_awaddr_o(),
                .m_axi_awprot_o(),
                .m_axi_awcache_o(),
                .m_axi_awsize_o(),
                .m_axi_awlen_o(),
                .m_axi_awburst_o(),
                .m_axi_awid_o(),
                .m_axi_wvalid_o(),
                .m_axi_wready_i(1'b1),
                .m_axi_wdata_o(),
                .m_axi_wstrb_o(),
                .m_axi_wlast_o(),
                .m_axi_bvalid_i(1'b1),
                .m_axi_bready_o(),
                .m_axi_bresp_i(2'b00),
                .m_axi_bid_i('0)
            );
            
            // AXI4 protocol adapter for data memory
            axi4_adapter #(
                .ID_WIDTH(ID_WIDTH),
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH)
            ) data_axi4_adapter (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mem_if(dcache_mem_if.slave),
                .m_axi_arvalid_o(d_arvalid_o),
                .m_axi_arready_i(d_arready_i),
                .m_axi_araddr_o(d_araddr_o),
                .m_axi_arprot_o(d_arprot_o),
                .m_axi_arcache_o(),
                .m_axi_arsize_o(),
                .m_axi_arlen_o(),
                .m_axi_arburst_o(),
                .m_axi_arid_o(),
                .m_axi_rvalid_i(d_rvalid_i),
                .m_axi_rready_o(d_rready_o),
                .m_axi_rdata_i(d_rdata_i),
                .m_axi_rresp_i(2'b00),
                .m_axi_rlast_i(1'b1),
                .m_axi_rid_i('0),
                .m_axi_awvalid_o(d_awvalid_o),
                .m_axi_awready_i(d_awready_i),
                .m_axi_awaddr_o(d_awaddr_o),
                .m_axi_awprot_o(d_awprot_o),
                .m_axi_awcache_o(),
                .m_axi_awsize_o(),
                .m_axi_awlen_o(),
                .m_axi_awburst_o(),
                .m_axi_awid_o(),
                .m_axi_wvalid_o(d_wvalid_o),
                .m_axi_wready_i(d_wready_i),
                .m_axi_wdata_o(d_wdata_o),
                .m_axi_wstrb_o(d_wstrb_o),
                .m_axi_wlast_o(),
                .m_axi_bvalid_i(d_bvalid_i),
                .m_axi_bready_o(d_bready_o),
                .m_axi_bresp_i(2'b00),
                .m_axi_bid_i('0)
            );
            
            // Tie off unused interface signals
            assign chi_instr_if.reqflitv = 1'b0;
            assign chi_data_if.reqflitv = 1'b0;
            assign tl_instr_if.a_valid = 1'b0;
            assign tl_data_if.a_valid = 1'b0;
            
        end else if (PROTOCOL_TYPE == "CHI") begin : chi_adapter_gen
            // CHI protocol adapter for instruction and data memory
            chi_adapter #(
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .ID_WIDTH(ID_WIDTH)
            ) instr_chi_adapter (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mem_if(instr_mem_if.slave),
                .chi_if(chi_instr_if),
                .latency_count_o(/* connected to performance monitoring */)
            );
            
            chi_adapter #(
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .ID_WIDTH(ID_WIDTH)
            ) data_chi_adapter (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mem_if(data_mem_if.slave),
                .chi_if(chi_data_if),
                .latency_count_o(/* connected to performance monitoring */)
            );
            
            // Tie off unused AXI4 signals
            assign i_arvalid_o = 1'b0;
            assign d_awvalid_o = 1'b0;
            assign d_arvalid_o = 1'b0;
            assign tl_instr_if.a_valid = 1'b0;
            assign tl_data_if.a_valid = 1'b0;
            
        end else if (PROTOCOL_TYPE == "TILELINK") begin : tilelink_adapter_gen
            // TileLink protocol adapter for instruction and data memory
            tilelink_adapter #(
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .SOURCE_WIDTH(ID_WIDTH)
            ) instr_tl_adapter (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mem_if(instr_mem_if.slave),
                .tl_if(tl_instr_if),
                .transaction_count_o(/* connected to performance monitoring */)
            );
            
            tilelink_adapter #(
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .SOURCE_WIDTH(ID_WIDTH)
            ) data_tl_adapter (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mem_if(data_mem_if.slave),
                .tl_if(tl_data_if),
                .transaction_count_o(/* connected to performance monitoring */)
            );
            
            // Tie off unused AXI4 signals
            assign i_arvalid_o = 1'b0;
            assign d_awvalid_o = 1'b0;
            assign d_arvalid_o = 1'b0;
            assign chi_instr_if.reqflitv = 1'b0;
            assign chi_data_if.reqflitv = 1'b0;
            
        end else begin : invalid_protocol_gen
            $error("Invalid PROTOCOL_TYPE: %s. Must be AXI4, CHI, or TILELINK", PROTOCOL_TYPE);
        end
    endgenerate

endmodule : memory_wrapper

//=============================================================================
// Dependencies: riscv_core_pkg.sv, memory_req_rsp_if.sv, axi4_adapter.sv
//
// Performance:
//   - Critical Path: Memory request to response
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
// 1.0.0   | 2025-06-28 | DesignAI           | Initial release
//=============================================================================