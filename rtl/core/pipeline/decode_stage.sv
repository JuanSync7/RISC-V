//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: decode_stage.sv
// Module: decode_stage
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   The Decode Stage (D) of the 5-stage RISC-V pipeline. Decodes the
//   instruction's opcode, funct3, and funct7 fields, generates all control
//   signals for downstream stages, generates the sign-extended immediate
//   value, provides the rs1 and rs2 addresses to the Register File, and
//   latches all results into the ID/EX pipeline register.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

module decode_stage
    import riscv_core_pkg::*;
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Control Signals from Hazard Unit ---
    input  logic        stall_e_i,
    input  logic        flush_d_i,

    // --- Input from Fetch Stage ---
    input  if_id_reg_t  if_id_reg_i,

    // --- Register File Read Interface ---
    output reg_addr_t   rs1_addr_o,
    output reg_addr_t   rs2_addr_o,
    input  word_t       rs1_data_i,
    input  word_t       rs2_data_i,

    // --- Output to Execute Stage ---
    output id_ex_reg_t  id_ex_reg_o
);

    // AI_TAG: INTERNAL_WIRE - Instruction field decoding for clarity.
    logic [6:0]  opcode;
    logic [4:0]  rd_addr;
    logic [2:0]  funct3;
    logic [4:0]  rs1_addr;
    logic [4:0]  rs2_addr;
    logic [6:0]  funct7;

    assign {funct7, rs2_addr, rs1_addr, funct3, rd_addr, opcode} = if_id_reg_i.instr;

    // AI_TAG: INTERNAL_LOGIC - Combinational logic for control signal and immediate generation.
    ctrl_signals_t ctrl_d;
    word_t         immediate_d;
    id_ex_reg_t    id_ex_reg_q;

    // AI_TAG: INTERNAL_LOGIC - Main Instruction Decoder
    always_comb begin
        // Default control signals for a bubble (NOP)
        ctrl_d.alu_op         = ALU_OP_ADD;
        ctrl_d.alu_src_a_sel  = ALU_A_SEL_RS1;
        ctrl_d.alu_src_b_sel  = ALU_B_SEL_IMM;
        ctrl_d.mem_read_en    = 1'b0;
        ctrl_d.mem_write_en   = 1'b0;
        ctrl_d.reg_write_en   = 1'b0;
        ctrl_d.wb_mux_sel     = WB_SEL_ALU;
        ctrl_d.is_branch      = 1'b0;
        ctrl_d.mult_en        = 1'b0; // AI_TAG: UPDATE - Set default for new signal
        ctrl_d.div_en         = 1'b0; // AI_TAG: UPDATE - Set default for new signal
        ctrl_d.csr_cmd_en     = 1'b0; // AI_TAG: UPDATE - Set default for new signal
        ctrl_d.funct3         = funct3;

        // Only decode if the instruction from the fetch stage is valid
        if (if_id_reg_i.valid) begin
            case (opcode)
                OPCODE_LUI: begin
                    ctrl_d.alu_op        = ALU_OP_LUI;
                    ctrl_d.alu_src_b_sel = ALU_B_SEL_IMM;
                    ctrl_d.reg_write_en  = 1'b1;
                    ctrl_d.wb_mux_sel    = WB_SEL_ALU;
                end
                OPCODE_AUIPC: begin
                    ctrl_d.alu_op        = ALU_OP_ADD;
                    ctrl_d.alu_src_a_sel = ALU_A_SEL_PC;
                    ctrl_d.alu_src_b_sel = ALU_B_SEL_IMM;
                    ctrl_d.reg_write_en  = 1'b1;
                    ctrl_d.wb_mux_sel    = WB_SEL_ALU;
                end
                OPCODE_JAL: begin
                    ctrl_d.alu_op        = ALU_OP_ADD;
                    ctrl_d.alu_src_a_sel = ALU_A_SEL_PC;
                    ctrl_d.alu_src_b_sel = ALU_B_SEL_IMM;
                    ctrl_d.reg_write_en  = 1'b1;
                    ctrl_d.wb_mux_sel    = WB_SEL_PC_P4;
                end
                OPCODE_JALR: begin
                    ctrl_d.alu_op        = ALU_OP_ADD;
                    ctrl_d.alu_src_a_sel = ALU_A_SEL_RS1;
                    ctrl_d.alu_src_b_sel = ALU_B_SEL_IMM;
                    ctrl_d.reg_write_en  = 1'b1;
                    ctrl_d.wb_mux_sel    = WB_SEL_PC_P4;
                end
                OPCODE_BRANCH: begin
                    ctrl_d.alu_op        = ALU_OP_SUB;
                    ctrl_d.alu_src_a_sel = ALU_A_SEL_RS1;
                    ctrl_d.alu_src_b_sel = ALU_B_SEL_RS2;
                    ctrl_d.is_branch     = 1'b1;
                end
                OPCODE_LOAD: begin
                    ctrl_d.alu_op        = ALU_OP_ADD;
                    ctrl_d.alu_src_a_sel = ALU_A_SEL_RS1;
                    ctrl_d.alu_src_b_sel = ALU_B_SEL_IMM;
                    ctrl_d.mem_read_en   = 1'b1;
                    ctrl_d.reg_write_en  = 1'b1;
                    ctrl_d.wb_mux_sel    = WB_SEL_MEM;
                end
                OPCODE_STORE: begin
                    ctrl_d.alu_op        = ALU_OP_ADD;
                    ctrl_d.alu_src_a_sel = ALU_A_SEL_RS1;
                    ctrl_d.alu_src_b_sel = ALU_B_SEL_IMM;
                    ctrl_d.mem_write_en  = 1'b1;
                end
                OPCODE_OP_IMM: begin
                    ctrl_d.alu_src_a_sel = ALU_A_SEL_RS1;
                    ctrl_d.alu_src_b_sel = ALU_B_SEL_IMM;
                    ctrl_d.reg_write_en  = 1'b1;
                    case (funct3)
                        3'b000: ctrl_d.alu_op = ALU_OP_ADD;
                        3'b010: ctrl_d.alu_op = ALU_OP_SLT;
                        3'b011: ctrl_d.alu_op = ALU_OP_SLTU;
                        3'b100: ctrl_d.alu_op = ALU_OP_XOR;
                        3'b110: ctrl_d.alu_op = ALU_OP_OR;
                        3'b111: ctrl_d.alu_op = ALU_OP_AND;
                        3'b001: ctrl_d.alu_op = ALU_OP_SLL;
                        3'b101: begin
                            if (funct7[5]) ctrl_d.alu_op = ALU_OP_SRA;
                            else           ctrl_d.alu_op = ALU_OP_SRL;
                        end
                        default:;
                    endcase
                end
                OPCODE_OP: begin
                    // AI_TAG: UPDATE - Differentiate between standard R-type and M-extension
                    if (funct7 == FUNCT7_M_EXT) begin
                        // This is an M-extension instruction (MUL/DIV)
                        ctrl_d.reg_write_en = 1'b1;
                        ctrl_d.wb_mux_sel   = WB_SEL_ALU; // Result comes from Execute stage path
                        
                        // AI_TAG: UPDATE - Differentiate between multiplication and division based on funct3
                        case (funct3)
                            3'b000, 3'b001, 3'b010, 3'b011: begin
                                // Multiplication instructions: MUL, MULH, MULHSU, MULHU
                                ctrl_d.mult_en = 1'b1;
                                ctrl_d.div_en  = 1'b0;
                            end
                            3'b100, 3'b101, 3'b110, 3'b111: begin
                                // Division instructions: DIV, DIVU, REM, REMU
                                ctrl_d.mult_en = 1'b0;
                                ctrl_d.div_en  = 1'b1;
                            end
                            default: begin
                                ctrl_d.mult_en = 1'b0;
                                ctrl_d.div_en  = 1'b0;
                            end
                        endcase
                    end else begin
                        // This is a standard R-type instruction
                        ctrl_d.alu_src_a_sel = ALU_A_SEL_RS1;
                        ctrl_d.alu_src_b_sel = ALU_B_SEL_RS2;
                        ctrl_d.reg_write_en  = 1'b1;
                        case (funct3)
                            3'b000: begin
                                if (funct7[5]) ctrl_d.alu_op = ALU_OP_SUB;
                                else           ctrl_d.alu_op = ALU_OP_ADD;
                            end
                            3'b001: ctrl_d.alu_op = ALU_OP_SLL;
                            3'b010: ctrl_d.alu_op = ALU_OP_SLT;
                            3'b011: ctrl_d.alu_op = ALU_OP_SLTU;
                            3'b100: ctrl_d.alu_op = ALU_OP_XOR;
                            3'b101: begin
                                if (funct7[5]) ctrl_d.alu_op = ALU_OP_SRA;
                                else           ctrl_d.alu_op = ALU_OP_SRL;
                            end
                            3'b110: ctrl_d.alu_op = ALU_OP_OR;
                            3'b111: ctrl_d.alu_op = ALU_OP_AND;
                            default:;
                        endcase
                    end
                end
                // AI_TAG: UPDATE - Added handler for SYSTEM instructions (CSR ops)
                OPCODE_SYSTEM: begin
                    ctrl_d.csr_cmd_en   = 1'b1;
                    ctrl_d.reg_write_en = 1'b1; // CSR reads write the old value back to rd
                    ctrl_d.wb_mux_sel   = WB_SEL_CSR;
                end
                default:;
            endcase
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Immediate Generator
    always_comb begin
        immediate_d = '0;
        case (opcode)
            OPCODE_LUI,     OPCODE_AUIPC: immediate_d = {if_id_reg_i.instr[31:12], 12'b0};
            OPCODE_JAL:     immediate_d = {{12{if_id_reg_i.instr[31]}}, if_id_reg_i.instr[19:12], if_id_reg_i.instr[20], if_id_reg_i.instr[30:21], 1'b0};
            OPCODE_JALR,    OPCODE_LOAD, OPCODE_OP_IMM, OPCODE_SYSTEM: immediate_d = {{21{if_id_reg_i.instr[31]}}, if_id_reg_i.instr[30:20]};
            OPCODE_BRANCH:  immediate_d = {{20{if_id_reg_i.instr[31]}}, if_id_reg_i.instr[7], if_id_reg_i.instr[30:25], if_id_reg_i.instr[11:8], 1'b0};
            OPCODE_STORE:   immediate_d = {{21{if_id_reg_i.instr[31]}}, if_id_reg_i.instr[30:25], if_id_reg_i.instr[11:7]};
            default:        immediate_d = '0;
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - ID/EX Pipeline Register
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            id_ex_reg_q.ctrl.reg_write_en <= 1'b0;
            id_ex_reg_q.pc                <= '0;
            id_ex_reg_q.rs1_addr          <= '0;
            id_ex_reg_q.rs2_addr          <= '0;
        end else if (!stall_e_i) begin
            if (flush_d_i) begin
                id_ex_reg_q.ctrl.reg_write_en <= 1'b0;
                id_ex_reg_q.pc                <= '0;
                id_ex_reg_q.rs1_addr          <= '0;
                id_ex_reg_q.rs2_addr          <= '0;
            end else begin
                id_ex_reg_q.pc         <= if_id_reg_i.pc;
                id_ex_reg_q.rs1_data   <= rs1_data_i;
                id_ex_reg_q.rs2_data   <= rs2_data_i;
                id_ex_reg_q.immediate  <= immediate_d;
                id_ex_reg_q.rd_addr    <= rd_addr;
                id_ex_reg_q.ctrl       <= ctrl_d;
                // AI_TAG: CRITICAL_UPDATE - Latch source register addresses for the hazard unit.
                id_ex_reg_q.rs1_addr   <= rs1_addr;
                id_ex_reg_q.rs2_addr   <= rs2_addr;
            end
        end
    end

    // --- Module Outputs ---
    assign rs1_addr_o  = rs1_addr;
    assign rs2_addr_o  = rs2_addr;
    assign id_ex_reg_o = id_ex_reg_q;

endmodule : decode_stage

//=============================================================================
// Dependencies: riscv_core_pkg.sv, reg_file.sv
// Instantiated In:
//   - rtl/core/integration/core_subsystem.sv
//
// Performance:
//   - Critical Path: Instruction decode to control signals
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