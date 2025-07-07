//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: writeback_stage.sv
// Module: writeback_stage
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   The Write-back Stage (W) of the 5-stage RISC-V pipeline. This is the final
//   stage where the architectural state is updated. This module is purely
//   combinational. It takes the result from the MEM/WB register and drives
//   the signals for the Register File's write port. It also provides these
//   signals for the forwarding unit.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_types_pkg::*;
import ooo_pkg::*;

module writeback_stage #(
    parameter bit ENABLE_OOO = 0 // New: Enable Out-of-Order Execution
)
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Input from Memory Stage ---
    generate
        if (!ENABLE_OOO) begin : gen_inorder_input
            input  mem_wb_reg_t mem_wb_reg_i;
        end
    endgenerate

    // --- Outputs to Register File Write Port ---
    // These signals will be connected to the reg_file instance at the top level.
    // AI_TAG: PORT_DESC - write_en_o - Final enable signal for the register file write operation.
    output logic        write_en_o,
    // AI_TAG: PORT_DESC - rd_addr_o - Final destination register address.
    output reg_addr_t   rd_addr_o,
    // AI_TAG: PORT_DESC - rd_data_o - Final data to be written to the register file,
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
    generate
        if (ENABLE_OOO) begin : gen_ooo_writeback
            assign write_en_o = ooo_commit_i.valid && (ooo_commit_i.rd_addr != 0);
            assign rd_addr_o  = ooo_commit_i.rd_addr;
            assign rd_data_o  = ooo_commit_i.result;
        end else begin : gen_inorder_writeback
            assign write_en_o = mem_wb_reg_i.reg_write_en;
            assign rd_addr_o  = mem_wb_reg_i.rd_addr;
            assign rd_data_o  = mem_wb_reg_i.wb_data;
        end
    endgenerate

    // AI_TAG: INTERNAL_LOGIC - Data Forwarding Path
    // Description: These assignments provide the necessary data for the W->E forwarding path.
    // The forwarding unit in the Execute stage uses these values to bypass the register file
    // for instructions that depend on a result that is just about to be written back.
    generate
        if (ENABLE_OOO) begin : gen_ooo_forwarding
            assign wb_data_fwd_o      = ooo_commit_i.result;
            assign rd_addr_fwd_o      = ooo_commit_i.rd_addr;
            assign reg_write_en_fwd_o = ooo_commit_i.valid && (ooo_commit_i.rd_addr != 0);
        end else begin : gen_inorder_forwarding
            assign wb_data_fwd_o      = mem_wb_reg_i.wb_data;
            assign rd_addr_fwd_o      = mem_wb_reg_i.rd_addr;
            assign reg_write_en_fwd_o = mem_wb_reg_i.reg_write_en;
        end
    endgenerate

    // AI_TAG: SVA - Check for valid write-back mux selection.
    // Description: Ensures that if a register write is occurring, the mux selector
    // that chose the data in the previous stage is not an invalid or unexpected value.
`ifndef SYNTHESIS
    property p_valid_wb_sel_on_write;
        @(posedge clk_i)
        disable iff(!rst_ni)
        (write_en_o) |-> (ENABLE_OOO ? 1'b1 : mem_wb_reg_i.wb_mux_sel inside {WB_SEL_ALU, WB_SEL_MEM, WB_SEL_PC_P4, WB_SEL_CSR, WB_SEL_DPU});
    endproperty

    a_valid_wb_sel_on_write: assert property (p_valid_wb_sel_on_write) else
        $error("Assertion failed: An invalid wb_mux_sel value was present during a register write enable.");
`endif


endmodule : writeback_stage

//=============================================================================
// Dependencies: riscv_types_pkg.sv, reg_file.sv
//
// Performance:
//   - Critical Path: Result selection to register write
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
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//=============================================================================