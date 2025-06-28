////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-27
// Design Name:   RV32IM Core
// Module Name:   mem_stage
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   The Memory Stage (M) of the 5-stage RISC-V pipeline.
//                - Drives the AXI4 data memory interface for LOAD and STORE ops.
//                - Contains data alignment logic for byte and half-word accesses.
//                - For non-memory ops, passes the ALU result through to the next stage.
//                - Latches results into the MEM/WB pipeline register.
//
// Dependencies:  riscv_core_pkg.sv
//
// Revision:
// Revision 1.0.0 - File Created
// Additional Comments:
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps
`default_nettype none

module mem_stage
    import riscv_core_pkg::*;
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Control Signals from Hazard Unit ---
    // AI_TAG: PORT_DESC - stall_w_i - Stalls the MEM/WB pipeline register.
    input  logic        stall_w_i,
    // AI_TAG: PORT_DESC - flush_m_i - Injects a bubble into the MEM/WB register.
    input  logic        flush_m_i,

    // --- Input from Execute Stage ---
    // AI_TAG: PORT_DESC - ex_mem_reg_i - The EX/MEM pipeline register data.
    input  ex_mem_reg_t ex_mem_reg_i,

    // --- AXI4 Data Memory Interface (Master) ---
    // Write Address Channel
    output logic        d_awvalid_o,
    input  logic        d_awready_i,
    output addr_t       d_awaddr_o,
    output logic [2:0]  d_awprot_o,
    // Write Data Channel
    output logic        d_wvalid_o,
    input  logic        d_wready_i,
    output word_t       d_wdata_o,
    output logic [3:0]  d_wstrb_o,
    // Write Response Channel
    input  logic        d_bvalid_i,
    output logic        d_bready_o,
    // Read Address Channel
    output logic        d_arvalid_o,
    input  logic        d_arready_i,
    output addr_t       d_araddr_o,
    output logic [2:0]  d_arprot_o,
    // Read Data Channel
    input  logic        d_rvalid_i,
    output logic        d_rready_o,
    input  word_t       d_rdata_i,

    // --- Output to Write-back Stage ---
    // AI_TAG: PORT_DESC - mem_wb_reg_o - The MEM/WB pipeline register data.
    output mem_wb_reg_t mem_wb_reg_o
);

    // AI_TAG: INTERNAL_WIRE - Wires for data alignment and write-back data selection.
    word_t       write_data_aligned;
    logic [3:0]  write_strobes;
    word_t       read_data_aligned;
    word_t       wb_data_d;

    mem_wb_reg_t mem_wb_reg_q;

    // AI_TAG: INTERNAL_LOGIC - Write Data Alignment Logic
    // Description: For STORE instructions, this shifts the data to the correct byte lanes
    // and generates the appropriate write strobes based on address and access size (funct3).
    always_comb begin
        write_strobes      = 4'b0;
        write_data_aligned = ex_mem_reg_i.store_data; // Default for SW
        case (ex_mem_reg_i.ctrl.funct3)
            3'b000: begin // SB (Store Byte)
                write_strobes      = 4'b1 << ex_mem_reg_i.alu_result[1:0];
                write_data_aligned = ex_mem_reg_i.store_data << (ex_mem_reg_i.alu_result[1:0] * 8);
            end
            3'b001: begin // SH (Store Half-word)
                write_strobes      = 4'b11 << ex_mem_reg_i.alu_result[1:0];
                write_data_aligned = ex_mem_reg_i.store_data << (ex_mem_reg_i.alu_result[1:0] * 8);
            end
            3'b010: begin // SW (Store Word)
                write_strobes      = 4'b1111;
                write_data_aligned = ex_mem_reg_i.store_data;
            end
            default: ;
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Read Data Alignment Logic
    // Description: For LOAD instructions, this extracts the correct byte or half-word
    // from the 32-bit memory response and sign- or zero-extends it.
    always_comb begin
        logic [15:0] halfword;
        logic [7:0]  byte;
        logic [1:0]  addr_lsb = ex_mem_reg_i.alu_result[1:0];

        read_data_aligned = 'x;
        halfword = d_rdata_i[addr_lsb*8 +: 16];
        byte     = d_rdata_i[addr_lsb*8 +: 8];

        case (ex_mem_reg_i.ctrl.funct3)
            3'b000: read_data_aligned = {{24{byte[7]}}, byte};                // LB (Load Byte, sign-extended)
            3'b001: read_data_aligned = {{16{halfword[15]}}, halfword};       // LH (Load Half-word, sign-extended)
            3'b010: read_data_aligned = d_rdata_i;                            // LW (Load Word)
            3'b100: read_data_aligned = {24'b0, byte};                        // LBU (Load Byte, Unsigned)
            3'b101: read_data_aligned = {16'b0, halfword};                    // LHU (Load Half-word, Unsigned)
            default: read_data_aligned = d_rdata_i; // Should not happen for loads
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Write-back Data Selection Mux
    // Description: Selects the data source for the write-back stage. For LOADs, it's the
    // aligned data from memory. For all other instructions, it's the ALU result.
    assign wb_data_d = (ex_mem_reg_i.ctrl.mem_read_en) ? read_data_aligned : ex_mem_reg_i.alu_result;

    // AI_TAG: AXI4_LOGIC - Data Memory AXI Interface
    // Description: Drives the AXI signals based on control signals from the EX/MEM register.
    // The Hazard Unit is expected to stall this stage until the AXI handshake completes.
    assign d_awvalid_o = ex_mem_reg_i.ctrl.mem_write_en;
    assign d_awaddr_o  = ex_mem_reg_i.alu_result;
    assign d_wvalid_o  = ex_mem_reg_i.ctrl.mem_write_en;
    assign d_wdata_o   = write_data_aligned;
    assign d_wstrb_o   = write_strobes;
    assign d_bready_o  = 1'b1; // Always ready to accept write response

    assign d_arvalid_o = ex_mem_reg_i.ctrl.mem_read_en;
    assign d_araddr_o  = ex_mem_reg_i.alu_result;
    assign d_rready_o  = 1'b1; // Always ready to accept read data when requested

    // AXI constants for data access
    assign d_awprot_o = 3'b010; // Privileged, Secure, Data access
    assign d_arprot_o = 3'b010; // Privileged, Secure, Data access

    // AI_TAG: INTERNAL_LOGIC - MEM/WB Pipeline Register
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            mem_wb_reg_q.reg_write_en <= 1'b0; // Reset to a bubble
        end else if (!stall_w_i) begin
            if (flush_m_i) begin
                mem_wb_reg_q.reg_write_en <= 1'b0; // Flush to a bubble
            end else begin
                // AI_TAG: DESIGN_NOTE - The wb_data is only valid if the instruction was a non-memory
                // op OR it was a load and d_rvalid_i is asserted by the memory system.
                // The Hazard Unit must stall this stage until d_rvalid_i is high for loads.
                mem_wb_reg_q.wb_data      <= wb_data_d;
                mem_wb_reg_q.rd_addr      <= ex_mem_reg_i.rd_addr;
                mem_wb_reg_q.reg_write_en <= ex_mem_reg_i.ctrl.reg_write_en;
                mem_wb_reg_q.wb_mux_sel   <= ex_mem_reg_i.ctrl.wb_mux_sel;
            end
        end
        // If stall_w_i, register holds its value.
    end

    assign mem_wb_reg_o = mem_wb_reg_q;

endmodule : mem_stage

`default_nettype wire