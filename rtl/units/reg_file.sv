//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: reg_file.sv
// Module: reg_file
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   32-bit, 32-entry RISC-V register file. Implements two asynchronous read
//   ports (rs1, rs2) and one synchronous write port (rd). Adheres to the
//   RISC-V specification where register x0 is hardwired to zero; reads from
//   x0 always return 0 and writes to x0 are ignored.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;

module reg_file #(
    parameter integer DATA_WIDTH = XLEN,
    parameter integer REG_COUNT = REG_COUNT,
    parameter integer REG_ADDR_WIDTH = REG_ADDR_WIDTH
)
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // Write Port (from Write-back Stage)
    // AI_TAG: PORT_DESC - write_en_i - Enables writing a new value to the register file.
    input  logic        write_en_i,
    // AI_TAG: PORT_DESC - rd_addr_i - 5-bit address of the destination register to write.
    input  reg_addr_t   rd_addr_i,
    // AI_TAG: PORT_DESC - rd_data_i - 32-bit data to write into the destination register.
    input  word_t       rd_data_i,

    // Read Port 1 (for Decode Stage)
    // AI_TAG: PORT_DESC - rs1_addr_i - 5-bit address of the first source register to read.
    input  reg_addr_t   rs1_addr_i,
    // AI_TAG: PORT_DESC - rs1_data_o - 32-bit data read from the rs1 port.
    output word_t       rs1_data_o,

    // Read Port 2 (for Decode Stage)
    // AI_TAG: PORT_DESC - rs2_addr_i - 5-bit address of the second source register to read.
    input  reg_addr_t   rs2_addr_i,
    // AI_TAG: PORT_DESC - rs2_data_o - 32-bit data read from the rs2 port.
    output word_t       rs2_data_o
);

    // AI_TAG: FEATURE - Implements 32 x 32-bit general-purpose registers.
    // AI_TAG: FEATURE - Two asynchronous read ports, one synchronous write port.
    // AI_TAG: FEATURE - Register x0 is hardwired to zero.

    // AI_TAG: INTERNAL_STORAGE - Main register file storage array.
    // This declares an array of 32 registers, each 32 bits wide.
    word_t registers[REG_COUNT];

    // AI_TAG: INTERNAL_LOGIC - Synchronous Write Logic.
    // Description: Handles the write operation on the rising edge of the clock.
    // It includes an active-low synchronous reset to initialize all registers to zero.
    // Writes to register address 0 are explicitly ignored to enforce the zero-register constraint.
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // On reset, clear all registers.
            for (int i = 0; i < REG_COUNT; i++) begin
                registers[i] <= '0;
            end
        end else begin
            if (write_en_i && (rd_addr_i != '0)) begin
                registers[rd_addr_i] <= rd_data_i;
            end
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Asynchronous Read Port 1.
    // Description: Implements a combinational read port for rs1.
    // If the read address is 0, it returns 32'b0 directly. Otherwise, it
    // returns the value from the register array. This describes a
    // "read-before-write" memory structure, where a simultaneous read and write
    // to the same address will yield the old data.
    assign rs1_data_o = (rs1_addr_i == '0) ? '0 : registers[rs1_addr_i];

    // AI_TAG: INTERNAL_LOGIC - Asynchronous Read Port 2.
    // Description: Implements a combinational read port for rs2, with the
    // same behavior as the rs1 port.
    assign rs2_data_o = (rs2_addr_i == '0) ? '0 : registers[rs2_addr_i];


    // AI_TAG: SVA - Check for invalid write to x0
    // Description: This assertion ensures that the control logic never attempts to
    // issue a write enable for register x0, which is a design violation.
`ifndef SYNTHESIS
    property p_no_write_to_x0;
        @(posedge clk_i)
        disable iff(!rst_ni)
        !(write_en_i && (rd_addr_i == '0));
    endproperty

    a_no_write_to_x0: assert property(p_no_write_to_x0) else
        $error("Assertion failed: Attempted to write to register x0.");
`endif

endmodule : reg_file

//=============================================================================
// Dependencies: riscv_types_pkg.sv
//
// Performance:
//   - Critical Path: Register read to output
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