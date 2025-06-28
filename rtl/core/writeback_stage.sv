////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-27
// Design Name:   RV32IM Core
// Module Name:   writeback_stage
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   The Write-back Stage (W) of the 5-stage RISC-V pipeline.
//                This is the final stage where the architectural state is
//                updated. This module is purely combinational. It takes the
//                result from the MEM/WB register and drives the signals for
//                the Register File's write port. It also provides these
//                signals for the forwarding unit.
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

module writeback_stage
    import riscv_core_pkg::*;
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Input from Memory Stage ---
    // AI_TAG: PORT_DESC - mem_wb_reg_i - The MEM/WB pipeline register data.
    input  mem_wb_reg_t mem_wb_reg_i,

    // --- Outputs to Register File Write Port ---
    // These signals will be connected to the reg_file instance at the top level.
    // AI_TAG: PORT_DESC - write_en_o - Final enable signal for the register file write operation.
    output logic        write_en_o,
    // AI_TAG: PORT_DESC - rd_addr_o - Final destination register address.
    output reg_addr_t   rd_addr_o,
    // AI_TAG: PORT_DESC - rd_data_o - Final data to be written to the register file.
    output word_t       rd_data_o,

    // --- Outputs for Forwarding Unit ---
    // These signals are fed back to the Execute stage to resolve RAW hazards.
    // AI_TAG: PORT_DESC - wb_data_fwd_o - Data value available for forwarding.
    output word_t       wb_data_fwd_o,
    // AI_TAG: PORT_DESC - rd_addr_fwd_o - Destination register address for forwarding logic to match against.
    output reg_addr_t   rd_addr_fwd_o,
    // AI_TAG: PORT_DESC - reg_write_en_fwd_o - Indicates if the forwarded data is valid (i.e., will be written).
    output logic        reg_write_en_fwd_o
);

    // AI_TAG: INTERNAL_LOGIC - Write-back to Register File
    // Description: These assignments drive the write port of the main register file.
    // The connection is made at the core's top level. This stage is purely a pass-through
    // of the values latched in the MEM/WB pipeline register.
    assign write_en_o = mem_wb_reg_i.reg_write_en;
    assign rd_addr_o  = mem_wb_reg_i.rd_addr;
    assign rd_data_o  = mem_wb_reg_i.wb_data;

    // AI_TAG: INTERNAL_LOGIC - Data Forwarding Path
    // Description: These assignments provide the necessary data for the W->E forwarding path.
    // The forwarding unit in the Execute stage uses these values to bypass the register file
    // for instructions that depend on a result that is just about to be written back.
    assign wb_data_fwd_o      = mem_wb_reg_i.wb_data;
    assign rd_addr_fwd_o      = mem_wb_reg_i.rd_addr;
    assign reg_write_en_fwd_o = mem_wb_reg_i.reg_write_en;

    // AI_TAG: SVA - Check for valid write-back mux selection.
    // Description: Ensures that if a register write is occurring, the mux selector
    // that chose the data in the previous stage is not an invalid or unexpected value.
`ifndef SYNTHESIS
    property p_valid_wb_sel_on_write;
        @(posedge clk_i)
        disable iff(!rst_ni)
        (mem_wb_reg_i.reg_write_en) |-> (mem_wb_reg_i.wb_mux_sel inside {WB_SEL_ALU, WB_SEL_MEM, WB_SEL_PC_P4, WB_SEL_CSR});
    endproperty

    a_valid_wb_sel_on_write: assert property (p_valid_wb_sel_on_write) else
        $error("Assertion failed: An invalid wb_mux_sel value was present during a register write enable.");
`endif


endmodule : writeback_stage

`default_nettype wire