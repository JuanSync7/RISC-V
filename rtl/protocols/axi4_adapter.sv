////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-28
// Design Name:   RV32IM Core
// Module Name:   axi4_adapter
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   AXI4 protocol adapter for protocol-agnostic memory interface.
//                Converts between memory_req_rsp_if and AXI4 signals,
//                maintaining backward compatibility with existing AXI4 systems.
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

module axi4_adapter #(
    // AI_TAG: PARAM_DESC - ID_WIDTH - Width of AXI4 ID signals.
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

    // --- Protocol-Agnostic Memory Interface ---
    // AI_TAG: PORT_DESC - mem_if - Protocol-agnostic memory interface.
    memory_req_rsp_if.master mem_if,

    // --- AXI4 Interface ---
    // Read Address Channel
    output logic                    m_axi_arvalid,
    input  logic                    m_axi_arready,
    output logic [ADDR_WIDTH-1:0]   m_axi_araddr,
    output logic [2:0]              m_axi_arprot,
    output logic [3:0]              m_axi_arcache,
    output logic [1:0]              m_axi_arsize,
    output logic [7:0]              m_axi_arlen,
    output logic [1:0]              m_axi_arburst,
    output logic [ID_WIDTH-1:0]     m_axi_arid,
    
    // Read Data Channel
    input  logic                    m_axi_rvalid,
    output logic                    m_axi_rready,
    input  logic [DATA_WIDTH-1:0]   m_axi_rdata,
    input  logic [1:0]              m_axi_rresp,
    input  logic                    m_axi_rlast,
    input  logic [ID_WIDTH-1:0]     m_axi_rid,
    
    // Write Address Channel
    output logic                    m_axi_awvalid,
    input  logic                    m_axi_awready,
    output logic [ADDR_WIDTH-1:0]   m_axi_awaddr,
    output logic [2:0]              m_axi_awprot,
    output logic [3:0]              m_axi_awcache,
    output logic [1:0]              m_axi_awsize,
    output logic [7:0]              m_axi_awlen,
    output logic [1:0]              m_axi_awburst,
    output logic [ID_WIDTH-1:0]     m_axi_awid,
    
    // Write Data Channel
    output logic                    m_axi_wvalid,
    input  logic                    m_axi_wready,
    output logic [DATA_WIDTH-1:0]   m_axi_wdata,
    output logic [DATA_WIDTH/8-1:0] m_axi_wstrb,
    output logic                    m_axi_wlast,
    
    // Write Response Channel
    input  logic                    m_axi_bvalid,
    output logic                    m_axi_bready,
    input  logic [1:0]              m_axi_bresp,
    input  logic [ID_WIDTH-1:0]     m_axi_bid
);

    // AI_TAG: INTERNAL_LOGIC - AXI4 state machine
    typedef enum logic [2:0] {
        IDLE,           // Waiting for request
        READ_ADDR,      // Sending read address
        READ_DATA,      // Receiving read data
        WRITE_ADDR,     // Sending write address
        WRITE_DATA,     // Sending write data
        WRITE_RESP      // Receiving write response
    } axi4_state_e;
    
    axi4_state_e state_r, state_next;
    
    // AI_TAG: INTERNAL_LOGIC - Request tracking
    logic [ID_WIDTH-1:0] pending_id_r;
    logic [ADDR_WIDTH-1:0] pending_addr_r;
    logic [2:0] pending_size_r;
    logic pending_write_r;
    word_t pending_data_r;
    logic [3:0] pending_strb_r;
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 signal assignments
    assign m_axi_arlen = 8'h00;    // Single beat transfers
    assign m_axi_awlen = 8'h00;    // Single beat transfers
    assign m_axi_arburst = 2'b01;  // INCR burst type
    assign m_axi_awburst = 2'b01;  // INCR burst type
    assign m_axi_wlast = 1'b1;     // Single beat transfers
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 state machine
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state_r <= IDLE;
            pending_id_r <= '0;
            pending_addr_r <= '0;
            pending_size_r <= '0;
            pending_write_r <= 1'b0;
            pending_data_r <= '0;
            pending_strb_r <= '0;
        end else begin
            state_r <= state_next;
            
            // Latch request when accepted
            if (mem_if.req_valid && mem_if.req_ready) begin
                pending_id_r <= mem_if.req.id;
                pending_addr_r <= mem_if.req.addr;
                pending_size_r <= mem_if.req.size;
                pending_write_r <= mem_if.req.write;
                pending_data_r <= mem_if.req.data;
                pending_strb_r <= mem_if.req.strb;
            end
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - State machine next state logic
    always_comb begin
        state_next = state_r;
        
        case (state_r)
            IDLE: begin
                if (mem_if.req_valid) begin
                    if (mem_if.req.write) begin
                        state_next = WRITE_ADDR;
                    end else begin
                        state_next = READ_ADDR;
                    end
                end
            end
            
            READ_ADDR: begin
                if (m_axi_arvalid && m_axi_arready) begin
                    state_next = READ_DATA;
                end
            end
            
            READ_DATA: begin
                if (m_axi_rvalid && m_axi_rready) begin
                    state_next = IDLE;
                end
            end
            
            WRITE_ADDR: begin
                if (m_axi_awvalid && m_axi_awready) begin
                    state_next = WRITE_DATA;
                end
            end
            
            WRITE_DATA: begin
                if (m_axi_wvalid && m_axi_wready) begin
                    state_next = WRITE_RESP;
                end
            end
            
            WRITE_RESP: begin
                if (m_axi_bvalid && m_axi_bready) begin
                    state_next = IDLE;
                end
            end
            
            default: begin
                state_next = IDLE;
            end
        endcase
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 read address channel
    always_comb begin
        m_axi_arvalid = (state_r == READ_ADDR);
        m_axi_araddr = pending_addr_r;
        m_axi_arprot = mem_if.req.prot;
        m_axi_arcache = mem_if.req.cacheable ? 4'b0010 : 4'b0000; // Normal Non-cacheable Bufferable
        m_axi_arsize = pending_size_r;
        m_axi_arid = pending_id_r;
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 read data channel
    always_comb begin
        m_axi_rready = (state_r == READ_DATA);
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 write address channel
    always_comb begin
        m_axi_awvalid = (state_r == WRITE_ADDR);
        m_axi_awaddr = pending_addr_r;
        m_axi_awprot = mem_if.req.prot;
        m_axi_awcache = mem_if.req.cacheable ? 4'b0010 : 4'b0000; // Normal Non-cacheable Bufferable
        m_axi_awsize = pending_size_r;
        m_axi_awid = pending_id_r;
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 write data channel
    always_comb begin
        m_axi_wvalid = (state_r == WRITE_DATA);
        m_axi_wdata = pending_data_r;
        m_axi_wstrb = pending_strb_r;
    end
    
    // AI_TAG: INTERNAL_LOGIC - AXI4 write response channel
    always_comb begin
        m_axi_bready = (state_r == WRITE_RESP);
    end
    
    // AI_TAG: INTERNAL_LOGIC - Memory interface control
    always_comb begin
        // Request ready when in IDLE state
        mem_if.req_ready = (state_r == IDLE);
        
        // Response valid and data
        mem_if.rsp_valid = 0;
        mem_if.rsp.data = '0;
        mem_if.rsp.id = '0;
        mem_if.rsp.error = 0;
        mem_if.rsp.last = 1'b1;
        
        if (state_r == READ_DATA && m_axi_rvalid) begin
            mem_if.rsp_valid = 1;
            mem_if.rsp.data = m_axi_rdata;
            mem_if.rsp.id = m_axi_rid;
            mem_if.rsp.error = (m_axi_rresp != 2'b00); // Check for error response
            mem_if.rsp.last = m_axi_rlast;
        end else if (state_r == WRITE_RESP && m_axi_bvalid) begin
            mem_if.rsp_valid = 1;
            mem_if.rsp.id = m_axi_bid;
            mem_if.rsp.error = (m_axi_bresp != 2'b00); // Check for error response
            mem_if.rsp.last = 1'b1;
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - Response ready (always ready to accept responses)
    assign mem_if.rsp_ready = 1'b1;

endmodule : axi4_adapter

`default_nettype wire 