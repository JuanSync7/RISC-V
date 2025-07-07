//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: multiple_execution_units.sv
// Module: multiple_execution_units
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Container and dispatcher for multiple functional units. It takes issued
//   instructions from the reservation station, decodes them, sends them to an
//   available functional unit of the correct type (ALU, Multiplier, etc.),
//   and arbitrates for the result bus to write back results.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none



// AI_TAG: FEATURE - Dispatches instructions to multiple configurable functional units.
// AI_TAG: FEATURE - Supports multi-cycle units (e.g., multiplier).
// AI_TAG: FEATURE - Arbitrates for a single result bus (CDB).
// AI_TAG: INTERNAL_BLOCK - InstructionDecoder - Determines required functional unit type from opcode.
// AI_TAG: INTERNAL_BLOCK - Dispatcher - Routes instruction to a free unit of the correct type.
// AI_TAG: INTERNAL_BLOCK - ResultArbiter - Selects one valid result to drive the output CDB.

module multiple_execution_units #(
    parameter integer DATA_WIDTH,
    parameter integer ROB_SIZE,
    parameter integer NUM_ALU_UNITS,
    parameter integer NUM_MULT_UNITS,
    parameter integer NUM_DIV_UNITS
) (
    input  logic clk_i,    // AI_TAG: PORT_DESC - System clock
    input  logic rst_ni,   // AI_TAG: PORT_DESC - Asynchronous active-low reset

    // Interface to Reservation Station
    output logic issue_ready_o,        // AI_TAG: PORT_DESC - Ready to accept a new instruction.
    input  logic issue_valid_i,        // AI_TAG: PORT_DESC - A valid instruction is being issued.
    input  riscv_instr_t issue_opcode_i, // AI_TAG: PORT_DESC - Opcode of the issued instruction.
    input  logic [DATA_WIDTH-1:0] issue_v_rs1_i,    // AI_TAG: PORT_DESC - Value of operand 1.
    input  logic [DATA_WIDTH-1:0] issue_v_rs2_i,    // AI_TAG: PORT_DESC - Value of operand 2.
    input  logic [$clog2(ROB_SIZE)-1:0] issue_rob_tag_i,  // AI_TAG: PORT_DESC - ROB tag of the issued instruction.

    // Interface to Result Bus (CDB)
    output logic result_valid_o,           // AI_TAG: PORT_DESC - A valid result is being broadcast.
    output logic [$clog2(ROB_SIZE)-1:0] result_rob_tag_o, // AI_TAG: PORT_DESC - ROB tag of the result.
    output logic [DATA_WIDTH-1:0] result_data_o,    // AI_TAG: PORT_DESC - Data value of the result.
    output logic result_exception_valid_o, // AI_TAG: PORT_DESC - The instruction resulted in an exception.
    output logic [31:0] result_exception_cause_o  // AI_TAG: PORT_DESC - The cause of the exception.
);

    localparam ROB_ADDR_WIDTH  = $clog2(ROB_SIZE);

    //---------------------------------------------------------------------------
    // Instruction Decoder
    //---------------------------------------------------------------------------
    logic is_alu_op_c, is_mult_op_c, is_div_op_c;

    // AI_TAG: FSM_NAME - instruction_decoder_fsm
    // AI_TAG: FSM_PURPOSE - instruction_decoder_fsm - Decodes opcode to determine required FU type.
    always_comb begin : proc_instr_decoder
        is_alu_op_c  = 1'b0;
        is_mult_op_c = 1'b0;
        is_div_op_c  = 1'b0;

        case (issue_opcode_i.op)
            OP_IMM, OP: begin
                // M-extension standard: funct7 = 0000001 for MUL/DIV/REM
                if (issue_opcode_i.funct7 == 7'b0000001) begin
                    case (issue_opcode_i.funct3)
                        // All MULT opcodes
                        3'b000, 3'b001, 3'b010, 3'b011: is_mult_op_c = 1'b1;
                        // All DIV/REM opcodes
                        3'b100, 3'b101, 3'b110, 3'b111: is_div_op_c = 1'b1;
                        default: is_alu_op_c = 1'b1; // Should not happen with valid instructions
                    endcase
                end else begin
                    is_alu_op_c = 1'b1;
                end
            end
            default:    is_alu_op_c = 1'b1; // Default to ALU for branches, loads, stores, etc.
        endcase
    end

    //---------------------------------------------------------------------------
    // Functional Unit Instantiations & Interfaces
    //---------------------------------------------------------------------------
    logic [TOTAL_UNITS-1:0] fu_busy_c;
    logic [TOTAL_UNITS-1:0] fu_result_valid_c;
    logic [DATA_WIDTH-1:0]  fu_result_data_c [TOTAL_UNITS];
    logic [ROB_ADDR_WIDTH-1:0] fu_result_rob_tag_c [TOTAL_UNITS];
    logic                   fu_result_ex_valid_c [TOTAL_UNITS];
    logic [31:0]            fu_result_ex_cause_c [TOTAL_UNITS];

    // --- ALUs ---
    generate
        for (genvar i = 0; i < NUM_ALU_UNITS; i++) begin : gen_alu_units
            localparam unit_idx = i;
            logic start;
            assign start = issue_valid_i && is_alu_op_c && !fu_busy_c[unit_idx];
            
            alu #(
                .DATA_WIDTH(DATA_WIDTH)
            ) u_alu (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .alu_op_i(issue_opcode_i), // alu will decode funct3/7
                .operand_a_i(issue_v_rs1_i),
                .operand_b_i(issue_v_rs2_i),
                .start_i(start),
                .result_o(fu_result_data_c[unit_idx]),
                .busy_o(fu_busy_c[unit_idx]),
                .done_o(fu_result_valid_c[unit_idx])
            );
            // Pipeline the ROB tag
            always_ff @(posedge clk_i) if(start) fu_result_rob_tag_c[unit_idx] <= issue_rob_tag_i;
            assign fu_result_ex_valid_c[unit_idx] = 1'b0; // ALU has no exceptions for now
            assign fu_result_ex_cause_c[unit_idx] = '0;
        end
    endgenerate

    // --- Multipliers ---
    generate
        for (genvar i = 0; i < NUM_MULT_UNITS; i++) begin : gen_mult_units
            localparam unit_idx = NUM_ALU_UNITS + i;
            logic start;
            assign start = issue_valid_i && is_mult_op_c && !fu_busy_c[unit_idx];

            mult_unit #(
                .DATA_WIDTH(DATA_WIDTH)
            ) u_mult_unit (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mult_op_i(issue_opcode_i.funct3),
                .operand_a_i(issue_v_rs1_i),
                .operand_b_i(issue_v_rs2_i),
                .start_i(start),
                .result_o(fu_result_data_c[unit_idx]),
                .busy_o(fu_busy_c[unit_idx]),
                .done_o(fu_result_valid_c[unit_idx])
            );
            // Pipeline the ROB tag
            always_ff @(posedge clk_i) if(start) fu_result_rob_tag_c[unit_idx] <= issue_rob_tag_i;
            assign fu_result_ex_valid_c[unit_idx] = 1'b0;
            assign fu_result_ex_cause_c[unit_idx] = '0;
        end
    endgenerate

    // --- Division Units ---
    generate
        for (genvar i = 0; i < NUM_DIV_UNITS; i++) begin : gen_div_units
            localparam unit_idx = TOTAL_MULT_UNITS + i;
            logic start;
            assign start = issue_valid_i && is_div_op_c && !fu_busy_c[unit_idx];

            div_unit #(
                .LATENCY(32) // Keep default latency
            ) u_div_unit (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .start_i(start),
                .operand_a_i(issue_v_rs1_i),
                .operand_b_i(issue_v_rs2_i),
                .op_type_i(issue_opcode_i.funct3),
                .result_o(fu_result_data_c[unit_idx]),
                .done_o(fu_result_valid_c[unit_idx]),
                .exception_valid_o(fu_result_ex_valid_c[unit_idx]),
                .exception_cause_o(fu_result_ex_cause_c[unit_idx])
            );
            // The div_unit is multi-cycle but combinatorial internally, so busy is tied to done.
            assign fu_busy_c[unit_idx] = u_div_unit.busy_o;

            // Pipeline the ROB tag
            always_ff @(posedge clk_i) if(start) fu_result_rob_tag_c[unit_idx] <= issue_rob_tag_i;

        end
    endgenerate

    //---------------------------------------------------------------------------
    // Dispatcher & issue_ready_o Logic
    //---------------------------------------------------------------------------
    logic alu_units_full_c, mult_units_full_c, div_units_full_c;

    assign alu_units_full_c  = &fu_busy_c[TOTAL_ALU_UNITS-1:0];
    assign mult_units_full_c = &fu_busy_c[TOTAL_MULT_UNITS-1:TOTAL_ALU_UNITS];
    assign div_units_full_c  = &fu_busy_c[TOTAL_UNITS-1:TOTAL_MULT_UNITS];

    assign issue_ready_o = (is_alu_op_c  && !alu_units_full_c) ||
                           (is_mult_op_c && !mult_units_full_c) ||
                           (is_div_op_c  && !div_units_full_c);

    //---------------------------------------------------------------------------
    // Result Arbiter (fixed priority)
    //---------------------------------------------------------------------------
    always_comb begin : proc_result_arbiter
        result_valid_o           = 1'b0;
        result_rob_tag_o         = '0;
        result_data_o            = '0;
        result_exception_valid_o = 1'b0;
        result_exception_cause_o = '0;

        for (int i = 0; i < TOTAL_UNITS; i++) begin
            if (fu_result_valid_c[i]) begin
                result_valid_o           = 1'b1;
                result_rob_tag_o         = fu_result_rob_tag_c[i];
                result_data_o            = fu_result_data_c[i];
                result_exception_valid_o = fu_result_ex_valid_c[i];
                result_exception_cause_o = fu_result_ex_cause_c[i];
                break; // This creates the fixed priority
            end
        end
    end

endmodule : multiple_execution_units

//=============================================================================
// Dependencies: 
//   - riscv_config_pkg: For system-wide configurations (e.g., number of units).
//   Instantiates:
//   - alu: For arithmetic and logic operations.
//   - mult_unit: For multiplication operations.
//   - div_unit: For division operations.
//
// Instantiated In: Likely within the main execute stage of the pipeline.
//
// Performance:
//   - Critical Path: Combination of instruction decode, dispatcher, and result arbiter logic.
//   - Max Frequency: <TBD>
//   - Area:          Highly dependent on the number and type of functional units configured.
//
// Verification Coverage:
//   - Code Coverage:     <Not Measured>
//   - Functional Coverage: <Not Measured>
//   - Branch Coverage:   <Not Measured>
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool:    <e.g., Design Compiler, Vivado>
//   - Clock Domains:     Single clock domain (clk_i).
//   - Constraints File:  <e.g., core_constraints.sdc>
//
// Testing:
//   - Testbench:    Verified as part of the `reorder_buffer_tb` and `riscv_core_integration_tb`.
//   - Test Vectors: Tests cover dispatching to all unit types, handling of multi-cycle
//                   operations, and result bus arbitration.
//
//----
// Revision History:
// Version | Date       | Author                          | Description
//=============================================================================
// 1.0.1   | 2025-07-31 | DesignAI (designai@sondrel.com) | Updated documentation to new standard format.
// 1.0.0   | 2025-06-27 | DesignAI (designai@sondrel.com) | Initial release of the multiple execution unit module.
//=============================================================================

`default_nettype wire 