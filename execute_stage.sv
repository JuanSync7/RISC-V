////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-27
// Design Name:   RV32IM Core
// Module Name:   execute_stage
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   The Execute Stage (E) of the 5-stage RISC-V pipeline.
//                - Selects ALU operands, incorporating data forwarding.
//                - Performs calculations using the main ALU and a multi-cycle multiplier.
//                - Evaluates branch conditions and calculates jump target addresses.
//                - Generates PC redirect and stall signals.
//                - Latches results into the EX/MEM pipeline register.
//
// Dependencies:  riscv_core_pkg.sv, alu.sv, mult_unit.sv
//
// Revision:
// Revision 1.1.0 - Integrated the multi-cycle mult_unit, including stall
//                  and result muxing logic.
// Revision 1.0.0 - File Created
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps
`default_nettype none

module execute_stage
    import riscv_core_pkg::*;
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Control Signals from Hazard Unit ---
    input  logic        stall_m_i,
    input  logic        flush_e_i,
    input  logic [1:0]  forward_a_sel_i,
    input  logic [1:0]  forward_b_sel_i,

    // --- Input from Decode Stage ---
    input  id_ex_reg_t  id_ex_reg_i,

    // --- Forwarding Path Inputs ---
    input  ex_mem_reg_t ex_mem_reg_m_i,
    input  word_t       wb_data_w_i,

    // --- PC Redirect Outputs (to Fetch Stage) ---
    output logic        pc_redirect_o,
    output addr_t       pc_redirect_target_o,

    // AI_TAG: NEW_PORT - Stall request output to the Hazard Unit
    // AI_TAG: PORT_DESC - exec_stall_req_o - Asserts when a multi-cycle operation is in progress.
    output logic        exec_stall_req_o,

    // --- Output to Memory Stage ---
    output ex_mem_reg_t ex_mem_reg_o
);

    localparam logic [1:0] FWD_SEL_REG  = 2'b00;
    localparam logic [1:0] FWD_SEL_MEM  = 2'b01;
    localparam logic [1:0] FWD_SEL_WB   = 2'b10;

    // AI_TAG: INTERNAL_WIRE - Wires for operand selection, ALU and Multiplier interfaces.
    word_t fwd_operand_a;
    word_t fwd_operand_b;
    word_t alu_operand_a;
    word_t alu_operand_b;
    word_t alu_result;
    logic  alu_zero_flag;
    logic  branch_taken;
    word_t mult_result;
    logic  mult_done;
    word_t final_result; // AI_TAG: UPDATE - Muxed result from ALU or Multiplier

    ex_mem_reg_t ex_mem_reg_q;

    // AI_TAG: INTERNAL_LOGIC - Forwarding Logic for Operand A (rs1)
    always_comb begin
        case (forward_a_sel_i)
            FWD_SEL_REG: fwd_operand_a = id_ex_reg_i.rs1_data;
            FWD_SEL_MEM: fwd_operand_a = ex_mem_reg_m_i.alu_result;
            FWD_SEL_WB:  fwd_operand_a = wb_data_w_i;
            default:     fwd_operand_a = id_ex_reg_i.rs1_data;
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Forwarding Logic for Operand B (rs2)
    always_comb begin
        case (forward_b_sel_i)
            FWD_SEL_REG: fwd_operand_b = id_ex_reg_i.rs2_data;
            FWD_SEL_MEM: fwd_operand_b = ex_mem_reg_m_i.alu_result;
            FWD_SEL_WB:  fwd_operand_b = wb_data_w_i;
            default:     fwd_operand_b = id_ex_reg_i.rs2_data;
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - ALU Input Muxes
    assign alu_operand_a = (id_ex_reg_i.ctrl.alu_src_a_sel == ALU_A_SEL_PC) ? id_ex_reg_i.pc : fwd_operand_a;
    assign alu_operand_b = (id_ex_reg_i.ctrl.alu_src_b_sel == ALU_B_SEL_IMM) ? id_ex_reg_i.immediate : fwd_operand_b;

    // AI_TAG: MODULE_INSTANCE - Main ALU Instantiation
    alu u_alu (
        .alu_op_i     ( id_ex_reg_i.ctrl.alu_op ),
        .operand_a_i  ( alu_operand_a             ),
        .operand_b_i  ( alu_operand_b             ),
        .alu_result_o ( alu_result                ),
        .zero_o       ( alu_zero_flag             )
    );

    // AI_TAG: MODULE_INSTANCE - Multi-cycle Multiplier Unit Instantiation
    mult_unit u_mult_unit (
        .clk_i        ( clk_i                     ),
        .rst_ni       ( rst_ni                    ),
        .start_i      ( id_ex_reg_i.ctrl.mult_en  ),
        .operand_a_i  ( fwd_operand_a             ),
        .operand_b_i  ( fwd_operand_b             ),
        .op_type_i    ( id_ex_reg_i.ctrl.funct3[1:0] ),
        .result_o     ( mult_result               ),
        .done_o       ( mult_done                 )
    );

    // AI_TAG: INTERNAL_LOGIC - Final Result Mux
    // Selects the result from the active unit.
    assign final_result = id_ex_reg_i.ctrl.mult_en ? mult_result : alu_result;

    // AI_TAG: INTERNAL_LOGIC - Stall Request Generation
    // Stall the pipeline if a multiplication is in progress and not yet complete.
    assign exec_stall_req_o = id_ex_reg_i.ctrl.mult_en & !mult_done;

    // AI_TAG: INTERNAL_LOGIC - Branch Evaluation Logic
    always_comb begin
        branch_taken = 1'b0;
        if (id_ex_reg_i.ctrl.is_branch) begin
            case (id_ex_reg_i.ctrl.funct3)
                3'b000: branch_taken = alu_zero_flag;
                3'b001: branch_taken = !alu_zero_flag;
                3'b100: branch_taken = alu_result[0];
                3'b101: branch_taken = !alu_result[0];
                3'b110: branch_taken = alu_result[0];
                3'b111: branch_taken = !alu_result[0];
                default: branch_taken = 1'b0;
            endcase
        end
    end

    // AI_TAG: INTERNAL_LOGIC - PC Redirect Logic
    assign pc_redirect_o        = branch_taken || (id_ex_reg_i.ctrl.wb_mux_sel == WB_SEL_PC_P4);
    assign pc_redirect_target_o = (id_ex_reg_i.ctrl.wb_mux_sel == WB_SEL_PC_P4 && id_ex_reg_i.ctrl.alu_op == ALU_OP_ADD)
                                  ? {alu_result[XLEN-1:1], 1'b0}
                                  : id_ex_reg_i.pc + id_ex_reg_i.immediate;


    // AI_TAG: INTERNAL_LOGIC - EX/MEM Pipeline Register
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            ex_mem_reg_q.ctrl.reg_write_en <= 1'b0;
        end else if (!stall_m_i) begin
            if (flush_e_i) begin
                ex_mem_reg_q.ctrl.reg_write_en <= 1'b0;
                ex_mem_reg_q.ctrl.mem_read_en  <= 1'b0;
                ex_mem_reg_q.ctrl.mem_write_en <= 1'b0;
                ex_mem_reg_q.ctrl.mult_en      <= 1'b0;
            end else begin
                // AI_TAG: UPDATE - Latch the muxed result into the pipeline register.
                ex_mem_reg_q.alu_result <= final_result;
                ex_mem_reg_q.store_data <= fwd_operand_b;
                ex_mem_reg_q.rd_addr    <= id_ex_reg_i.rd_addr;
                ex_mem_reg_q.ctrl       <= id_ex_reg_i.ctrl;
            end
        end
    end

    assign ex_mem_reg_o = ex_mem_reg_q;

endmodule : execute_stage