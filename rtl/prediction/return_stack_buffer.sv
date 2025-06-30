//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: return_stack_buffer.sv
// Module: return_stack_buffer
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   A simple Return Stack Buffer (RSB) to improve the prediction of return
//   instructions (e.g., JALR used for function returns). It acts as a small,
//   specialized stack for return addresses.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_types_pkg::*;
import riscv_config_pkg::*;

module return_stack_buffer #(
    parameter integer ADDR_WIDTH = ADDR_WIDTH,
    parameter integer STACK_DEPTH = DEFAULT_RSB_ENTRIES
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Push a return address onto the stack (on a 'call' instruction)
    input  logic                push_en_i,
    input  logic [ADDR_WIDTH-1:0] push_addr_i,   // The return address (e.g., PC+4)

    // Pop a return address from the stack (on a 'return' instruction)
    input  logic                pop_en_i,
    output logic [ADDR_WIDTH-1:0] pop_addr_o,
    output logic                pop_valid_o     // Indicates the popped address is valid
);

    localparam PTR_WIDTH = $clog2(STACK_DEPTH);

    logic [ADDR_WIDTH-1:0] stack [STACK_DEPTH-1:0];
    logic [PTR_WIDTH-1:0]  stack_ptr;
    logic [PTR_WIDTH:0]    num_entries; // Counter to track how many entries are in the stack

    //---------------------------------------------------------------------------
    // Combinational Logic
    //---------------------------------------------------------------------------
    logic is_empty;
    logic is_full;

    assign is_empty = (num_entries == 0);
    assign is_full  = (num_entries == STACK_DEPTH);

    // The stack pointer always points to the *next* free slot.
    // Therefore, the last pushed item is at `stack_ptr - 1`.
    assign pop_addr_o = stack[stack_ptr - 1];
    assign pop_valid_o = !is_empty; // The popped address is valid if the stack is not empty

    //---------------------------------------------------------------------------
    // Sequential Logic
    //---------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            stack_ptr   <= '0;
            num_entries <= '0;
        end else begin
            // Handle push and pop operations, including the simultaneous case
            case ({push_en_i && !is_full, pop_en_i && !is_empty})
                2'b11: begin // Simultaneous push and pop: net effect is a replace-at-top
                    stack[stack_ptr - 1] <= push_addr_i; // Overwrite the entry being popped
                    // Stack pointer and entry count remain unchanged
                end
                2'b10: begin // Push only
                    stack[stack_ptr] <= push_addr_i;
                    stack_ptr   <= stack_ptr + 1;
                    num_entries <= num_entries + 1;
                end
                2'b01: begin // Pop only
                    stack_ptr   <= stack_ptr - 1;
                    num_entries <= num_entries - 1;
                end
                default: begin
                    // No operation
                end
            endcase
        end
    end

endmodule : return_stack_buffer

`default_nettype wire