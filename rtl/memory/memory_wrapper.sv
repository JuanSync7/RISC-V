////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-28
// Design Name:   RV32IM Core
// Module Name:   memory_wrapper
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   Memory wrapper that abstracts protocol details from pipeline stages.
//                Provides a clean interface for instruction and data memory access,
//                internally using protocol-agnostic memory_req_rsp_if.
//
// Dependencies:  riscv_core_pkg.sv, memory_req_rsp_if.sv
//
// Revision:
// Revision 1.0.0 - File Created
// Additional Comments:
//
////////////////////////////////////////////////////////////////////////////////

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
    input  word_t                   d_rdata_i
);

    // AI_TAG: INTERNAL_LOGIC - Memory interfaces for protocol adapters
    memory_req_rsp_if instr_mem_if();
    memory_req_rsp_if data_mem_if();
    
    // AI_TAG: INTERNAL_LOGIC - Transaction ID counters
    logic [ID_WIDTH-1:0] instr_id_counter;
    logic [ID_WIDTH-1:0] data_id_counter;
    
    // AI_TAG: INTERNAL_LOGIC - Request tracking
    logic [ID_WIDTH-1:0] pending_instr_id;
    logic [ID_WIDTH-1:0] pending_data_id;
    logic pending_instr_valid;
    logic pending_data_valid;
    
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
        instr_rsp_error_o = instr_mem_if.rsp.error;
        instr_mem_if.rsp_ready = instr_rsp_ready_i;
    end
    
    // AI_TAG: INTERNAL_LOGIC - Data memory interface control
    always_comb begin
        // Request side
        data_mem_if.req_valid = data_req_valid_i;
        data_mem_if.req.addr = data_req_addr_i;
        data_mem_if.req.size = data_req_size_i;
        data_mem_if.req.write = data_req_write_i;
        data_mem_if.req.data = data_req_data_i;
        data_mem_if.req.strb = data_req_strb_i;
        data_mem_if.req.id = data_id_counter;
        data_mem_if.req.cacheable = 1'b1;
        data_mem_if.req.prot = 2'b10; // Privileged, secure
        
        data_req_ready_o = data_mem_if.req_ready;
        
        // Response side
        data_rsp_valid_o = data_mem_if.rsp_valid;
        data_rsp_data_o = data_mem_if.rsp.data;
        data_rsp_error_o = data_mem_if.rsp.error;
        data_mem_if.rsp_ready = data_rsp_ready_i;
    end
    
    // AI_TAG: INTERNAL_LOGIC - Transaction ID counters
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            instr_id_counter <= '0;
            data_id_counter <= '0;
        end else begin
            if (instr_req_valid_i && instr_req_ready_o) begin
                instr_id_counter <= instr_id_counter + 1;
            end
            if (data_req_valid_i && data_req_ready_o) begin
                data_id_counter <= data_id_counter + 1;
            end
        end
    end
    
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
                .mem_if(data_mem_if.slave),
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
            
        end else if (PROTOCOL_TYPE == "CHI") begin : chi_adapter_gen
            // TODO: Add CHI protocol adapter when implemented
            $error("CHI protocol adapter not yet implemented");
            
        end else if (PROTOCOL_TYPE == "TILELINK") begin : tilelink_adapter_gen
            // TODO: Add TileLink protocol adapter when implemented
            $error("TileLink protocol adapter not yet implemented");
            
        end else begin : invalid_protocol_gen
            $error("Invalid PROTOCOL_TYPE: %s. Must be AXI4, CHI, or TILELINK", PROTOCOL_TYPE);
        end
    endgenerate

endmodule : memory_wrapper

`default_nettype wire 