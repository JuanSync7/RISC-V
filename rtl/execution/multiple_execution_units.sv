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

//=============================================================================
// Toolchain:
//   - Synopsys Design Compiler for synthesis
//   - Cadence Xcelium for simulation
//
// Dependencies:
//   - rtl/pkg/riscv_core_pkg.sv
//   - rtl/pkg/ooo_pkg.sv
//   - rtl/units/alu.sv
//   - rtl/units/mult_unit.sv
//   - rtl/units/div_unit.sv
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import ooo_pkg::*;

// AI_TAG: FEATURE - Dispatches instructions to multiple configurable functional units.
// AI_TAG: FEATURE - Supports multi-cycle units (e.g., multiplier).
// AI_TAG: FEATURE - Arbitrates for a single result bus (CDB).
// AI_TAG: INTERNAL_BLOCK - InstructionDecoder - Determines required functional unit type from opcode.
// AI_TAG: INTERNAL_BLOCK - Dispatcher - Routes instruction to a free unit of the correct type.
// AI_TAG: INTERNAL_BLOCK - ResultArbiter - Selects one valid result to drive the output CDB.

module multiple_execution_units #(
    parameter integer DATA_WIDTH      = ooo_pkg::DATA_WIDTH,
    parameter integer ROB_ADDR_WIDTH  = ooo_pkg::ROB_ADDR_WIDTH,
    parameter integer NUM_ALU_UNITS   = 2, // AI_TAG: PARAM_DESC - Number of Arithmetic Logic Units.
    parameter integer NUM_MULT_UNITS  = 1, // AI_TAG: PARAM_DESC - Number of Multiplier Units.
    parameter integer NUM_DIV_UNITS   = 1  // AI_TAG: PARAM_DESC - Number of Division Units.
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Interface to Reservation Station
    output logic issue_ready_o,
    input  ooo_issue_t issue_i,

    // Interface to Result Bus (CDB)
    output ooo_result_t result_o
);

    localparam TOTAL_ALU_UNITS  = NUM_ALU_UNITS;
    localparam TOTAL_MULT_UNITS = TOTAL_ALU_UNITS + NUM_MULT_UNITS;
    localparam TOTAL_UNITS      = TOTAL_MULT_UNITS + NUM_DIV_UNITS;

    //---------------------------------------------------------------------------
    // Instruction Decoder
    //---------------------------------------------------------------------------
    logic is_alu_op_c, is_mult_op_c, is_div_op_c;
    alu_op_e alu_op_c;

    // AI_TAG: FSM_NAME - instruction_decoder_fsm
    // AI_TAG: FSM_PURPOSE - instruction_decoder_fsm - Decodes opcode to determine required FU type.
    always_comb begin : proc_instr_decoder
        is_alu_op_c  = 1'b0;
        is_mult_op_c = 1'b0;
        is_div_op_c  = 1'b0;
        alu_op_c     = ALU_OP_ADD; // Default

        case (issue_i.opcode.opcode)
            OPCODE_OP_IMM: begin
                is_alu_op_c = 1'b1;
                case (issue_i.opcode.funct3)
                    3'b000: alu_op_c = ALU_OP_ADD; // ADDI
                    3'b010: alu_op_c = ALU_OP_SLT; // SLTI
                    3'b011: alu_op_c = ALU_OP_SLTU; // SLTIU
                    3'b100: alu_op_c = ALU_OP_XOR; // XORI
                    3'b110: alu_op_c = ALU_OP_OR;  // ORI
                    3'b111: alu_op_c = ALU_OP_AND; // ANDI
                    3'b001: alu_op_c = ALU_OP_SLL; // SLLI
                    3'b101: begin // SRLI / SRAI
                        if (issue_i.opcode.funct7[5]) alu_op_c = ALU_OP_SRA; // SRAI
                        else alu_op_c = ALU_OP_SRL; // SRLI
                    end
                    default: alu_op_c = ALU_OP_ADD;
                endcase
            end
            OPCODE_OP: begin
                // M-extension standard: funct7 = 0000001 for MUL/DIV/REM
                if (issue_i.opcode.funct7 == FUNCT7_M_EXT) begin
                    case (issue_i.opcode.funct3)
                        // All MULT opcodes
                        3'b000, 3'b001, 3'b010, 3'b011: is_mult_op_c = 1'b1;
                        // All DIV/REM opcodes
                        3'b100, 3'b101, 3'b110, 3'b111: is_div_op_c = 1'b1;
                        default: is_alu_op_c = 1'b1; // Should not happen with valid instructions
                    endcase
                end else begin
                    is_alu_op_c = 1'b1;
                    case (issue_i.opcode.funct3)
                        3'b000: begin // ADD/SUB
                            if (issue_i.opcode.funct7[5]) alu_op_c = ALU_OP_SUB; // SUB
                            else alu_op_c = ALU_OP_ADD; // ADD
                        end
                        3'b001: alu_op_c = ALU_OP_SLL; // SLL
                        3'b010: alu_op_c = ALU_OP_SLT; // SLT
                        3'b011: alu_op_c = ALU_OP_SLTU; // SLTU
                        3'b100: alu_op_c = ALU_OP_XOR; // XOR
                        3'b101: begin // SRL/SRA
                            if (issue_i.opcode.funct7[5]) alu_op_c = ALU_OP_SRA; // SRA
                            else alu_op_c = ALU_OP_SRL; // SRL
                        end
                        3'b110: alu_op_c = ALU_OP_OR;  // OR
                        3'b111: alu_op_c = ALU_OP_AND; // AND
                        default: alu_op_c = ALU_OP_ADD;
                    endcase
                end
            end
            OPCODE_LUI: begin
                is_alu_op_c = 1'b1;
                alu_op_c = ALU_OP_LUI;
            end
            OPCODE_AUIPC: begin
                is_alu_op_c = 1'b1;
                alu_op_c = ALU_OP_ADD; // AUIPC is PC + immediate
            end
            OPCODE_JAL: begin
                is_alu_op_c = 1'b1;
                alu_op_c = ALU_OP_ADD; // JAL calculates PC + immediate
            end
            OPCODE_JALR: begin
                is_alu_op_c = 1'b1;
                alu_op_c = ALU_OP_COPY_A; // JALR uses RS1 + immediate
            end
            OPCODE_BRANCH: begin
                is_alu_op_c = 1'b1;
                alu_op_c = ALU_OP_SUB; // Branch condition check (RS1 - RS2)
            end
            OPCODE_LOAD, OPCODE_STORE: begin
                is_alu_op_c = 1'b1;
                alu_op_c = ALU_OP_ADD; // Load/Store address calculation (RS1 + immediate)
            end
            default:    is_alu_op_c = 1'b1; // Default to ALU for other instructions
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
            assign start = issue_i.valid && is_alu_op_c && !fu_busy_c[unit_idx];
            
            alu #(
                .DATA_WIDTH(DATA_WIDTH)
            ) u_alu (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .alu_op_i(alu_op_c),
                .operand_a_i(issue_i.v_rs1),
                .operand_b_i(issue_i.v_rs2),
                .start_i(start),
                .result_o(fu_result_data_c[unit_idx]),
                .busy_o(fu_busy_c[unit_idx]),
                .done_o(fu_result_valid_c[unit_idx])
            );
            // Pipeline the ROB tag
            always_ff @(posedge clk_i) if(start) fu_result_rob_tag_c[unit_idx] <= issue_i.rob_tag;
            assign fu_result_ex_valid_c[unit_idx] = 1'b0; // ALU has no exceptions for now
            assign fu_result_ex_cause_c[unit_idx] = '0;
        end
    endgenerate

    // --- Multipliers ---
    generate
        for (genvar i = 0; i < NUM_MULT_UNITS; i++) begin : gen_mult_units
            localparam unit_idx = NUM_ALU_UNITS + i;
            logic start;
            assign start = issue_i.valid && is_mult_op_c && !fu_busy_c[unit_idx];

            mult_unit #(
                .DATA_WIDTH(DATA_WIDTH)
            ) u_mult_unit (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .mult_op_i(issue_i.opcode.funct3),
                .operand_a_i(issue_i.v_rs1),
                .operand_b_i(issue_i.v_rs2),
                .start_i(start),
                .result_o(fu_result_data_c[unit_idx]),
                .busy_o(fu_busy_c[unit_idx]),
                .done_o(fu_result_valid_c[unit_idx])
            );
            // Pipeline the ROB tag
            always_ff @(posedge clk_i) if(start) fu_result_rob_tag_c[unit_idx] <= issue_i.rob_tag;
            assign fu_result_ex_valid_c[unit_idx] = 1'b0;
            assign fu_result_ex_cause_c[unit_idx] = '0;
        end
    endgenerate

    // --- Division Units ---
    generate
        for (genvar i = 0; i < NUM_DIV_UNITS; i++) begin : gen_div_units
            localparam unit_idx = TOTAL_MULT_UNITS + i;
            logic start;
            assign start = issue_i.valid && is_div_op_c && !fu_busy_c[unit_idx];

            div_unit #(
                .LATENCY(32) // Keep default latency
            ) u_div_unit (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .start_i(start),
                .operand_a_i(issue_i.v_rs1),
                .operand_b_i(issue_i.v_rs2),
                .op_type_i(issue_i.opcode.funct3),
                .result_o(fu_result_data_c[unit_idx]),
                .done_o(fu_result_valid_c[unit_idx]),
                .exception_valid_o(fu_result_ex_valid_c[unit_idx]),
                .exception_cause_o(fu_result_ex_cause_c[unit_idx])
            );
            // The div_unit is multi-cycle but combinatorial internally, so busy is tied to done.
            assign fu_busy_c[unit_idx] = u_div_unit.busy_o;

            // Pipeline the ROB tag
            always_ff @(posedge clk_i) if(start) fu_result_rob_tag_c[unit_idx] <= issue_i.rob_tag;

        end
    endgenerate

    //---------------------------------------------------------------------------
    // Dispatcher & issue_ready_o Logic
    //---------------------------------------------------------------------------
    logic alu_units_full_c, mult_units_full_c, div_units_full_c;

    assign alu_units_full_c  = &fu_busy_c[TOTAL_ALU_UNITS-1:0];
    assign mult_units_full_c = &fu_busy_c[TOTAL_MULT_UNITS-1:TOTAL_ALU_UNITS];
    assign div_units_full_c  = &fu_busy_c[TOTAL_UNITS-1:TOTAL_MULT_UNITS];

    assign issue_ready_o = (issue_i.valid && is_alu_op_c  && !alu_units_full_c) ||
                           (issue_i.valid && is_mult_op_c && !mult_units_full_c) ||
                           (issue_i.valid && is_div_op_c  && !div_units_full_c);

    //---------------------------------------------------------------------------
    // Result Arbiter (fixed priority)
    //---------------------------------------------------------------------------
    always_comb begin : proc_result_arbiter
        result_o.valid           = 1'b0;
        result_o.rob_tag         = '0;
        result_o.data            = '0;
        result_o.exception_valid = 1'b0;
        result_o.exception_cause = '0;

        for (int i = 0; i < TOTAL_UNITS; i++) begin
            if (fu_result_valid_c[i]) begin
                result_o.valid           = 1'b1;
                result_o.rob_tag         = fu_result_rob_tag_c[i];
                result_o.data            = fu_result_data_c[i];
                result_o.exception_valid = fu_result_ex_valid_c[i];
                result_o.exception_cause = fu_result_ex_cause_c[i];
                break; // This creates the fixed priority
            end
        end
    end

endmodule : multiple_execution_units

//=============================================================================
// Dependencies:
//   - rtl/units/alu.sv
//   - rtl/units/mult_unit.sv
//   - rtl/units/div_unit.sv
//   - rtl/core/riscv_core_pkg.sv
//
// Performance:
//   - Critical Path: TBD
//   - Max Frequency: TBD
//   - Area: TBD
//
// Verification Coverage:
//   - Code Coverage: N/A
//   - Functional Coverage: N/A
//   - Branch Coverage: N/A
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: N/A
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: TBD
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial fleshed-out implementation with FU instantiation and arbitration.
// 0.1.0   | 2025-06-27 | DesignAI           | Initial skeleton release
//=============================================================================

`default_nettype wire 