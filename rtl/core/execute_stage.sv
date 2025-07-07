//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: execute_stage.sv
// Module: execute_stage
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   The Execute Stage (E) of the 5-stage RISC-V pipeline. Selects ALU operands,
//   incorporating data forwarding, performs calculations using the main ALU and
//   multi-cycle multiplier/divider, evaluates branch conditions and calculates
//   jump target addresses, generates PC redirect and stall signals, and latches
//   results into the EX/MEM pipeline register.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import mmu_pkg::*;

module execute_stage #(
    // AI_TAG: PARAMETER - ENABLE_MMU - Enable Memory Management Unit
    parameter bit ENABLE_MMU = 1,
    parameter bit ENABLE_OOO = 0 // New: Enable Out-of-Order Execution
)
    import riscv_core_pkg::*;
    import ooo_pkg::*;

    // --- Control Signals from Hazard Unit ---
    input  logic        stall_m_i,
    input  logic        flush_e_i,
    input  logic [1:0]  forward_a_sel_i,
    input  logic [1:0]  forward_b_sel_i,

    // --- Input from Decode Stage ---
    generate
        if (ENABLE_OOO) begin : gen_ooo_input
            input ooo_issue_t issue_i;
        end else begin : gen_inorder_input
            input id_ex_reg_t  id_ex_reg_i;
        end
    endgenerate

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
    output ex_mem_reg_t ex_mem_reg_o,

    // --- MMU Interface (from core_subsystem) ---
    input  mmu_request_t           mmu_req_i,
    input  logic                   mmu_req_valid_i,
    output logic                   mmu_req_ready_o,
    output mmu_response_t          mmu_resp_o,
    output logic                   mmu_resp_valid_o,
    input  logic                   mmu_resp_ready_i,

    // AI_TAG: NEW_PORT - Overflow output for arithmetic operations
    output logic overflow_o,

    // AI_TAG: NEW_PORT - Branch prediction update output
    // AI_TAG: PORT_DESC - bp_update_o - Branch prediction update information for the BPU.
    output branch_update_t bp_update_o,

    // AI_TAG: NEW_PORT - Exception detection output
    // AI_TAG: PORT_DESC - exception_o - Exception information from execute stage
    output exception_info_t exception_o,

    // --- CSR Interface (to core_subsystem for MMU CSRs) ---
    output logic        csr_read_en_o,
    output logic [11:0] csr_addr_o,
    input  logic [31:0] csr_rdata_i,
    output logic        csr_write_en_o,
    output logic [11:0] csr_addr_w_o,
    output logic [31:0] csr_wdata_o,

    // OOO Result Output (CDB)
    output ooo_result_t ooo_result_o
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
    logic  alu_overflow_flag;  // AI_TAG: NEW - Overflow flag from ALU
    logic  branch_taken;
    word_t mult_result;
    logic  mult_done;
    word_t div_result;         // AI_TAG: NEW - Division result
    logic  div_done;           // AI_TAG: NEW - Division done flag
    word_t final_result; // AI_TAG: UPDATE - Muxed result from ALU, Multiplier, Divider, or DPU

    // AI_TAG: NEW_WIRE - DPU related signals
    word_t fpu_result;
    logic  fpu_done;
    word_t vpu_result;
    logic  vpu_done;
    word_t mliu_result;
    logic  mliu_done;

    // AI_TAG: INTERNAL_WIRE - Exception detection signals
    logic illegal_instruction;
    logic div_by_zero;
    logic ecall_exception;
    logic breakpoint_exception;
    logic overflow_exception;
    exception_info_t exception_detected;

    // Internal signals for MMU interaction
    mmu_request_t  mmu_data_req;
    mmu_response_t mmu_data_resp;
    logic          mmu_data_req_valid;
    logic          mmu_data_req_ready;
    logic          mmu_data_resp_valid;
    logic          mmu_data_resp_ready;

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
    generate
        if (ENABLE_OOO) begin : gen_ooo_alu_inputs
            assign alu_operand_a = issue_i.v_rs1;
            assign alu_operand_b = issue_i.v_rs2;
        end else begin : gen_inorder_alu_inputs
            assign alu_operand_a = (id_ex_reg_i.ctrl.alu_src_a_sel == ALU_A_SEL_PC) ? id_ex_reg_i.pc : fwd_operand_a;
            assign alu_operand_b = (id_ex_reg_i.ctrl.alu_src_b_sel == ALU_B_SEL_IMM) ? id_ex_reg_i.immediate : fwd_operand_b;
        end
    endgenerate

    // AI_TAG: MODULE_INSTANCE - Main ALU Instantiation
    alu u_alu (
        .alu_op_i     ( ENABLE_OOO ? issue_i.opcode.alu_op : id_ex_reg_i.ctrl.alu_op ),
        .operand_a_i  ( alu_operand_a             ),
        .operand_b_i  ( alu_operand_b             ),
        .alu_result_o ( alu_result                ),
        .zero_o       ( alu_zero_flag             ),
        .overflow_o   ( alu_overflow_flag         )
    );

    // AI_TAG: MODULE_INSTANCE - Multi-cycle Multiplier Unit Instantiation
    mult_unit u_mult_unit (
        .clk_i        ( clk_i                     ),
        .rst_ni       ( rst_ni                    ),
        .start_i      ( ENABLE_OOO ? issue_i.opcode.mult_en : id_ex_reg_i.ctrl.mult_en  ),
        .operand_a_i  ( fwd_operand_a             ),
        .operand_b_i  ( fwd_operand_b             ),
        .op_type_i    ( ENABLE_OOO ? issue_i.opcode.funct3 : id_ex_reg_i.ctrl.funct3   ),
        .result_o     ( mult_result               ),
        .done_o       ( mult_done                 )
    );

    // AI_TAG: MODULE_INSTANCE - Multi-cycle Division Unit Instantiation
    div_unit u_div_unit (
        .clk_i        ( clk_i                     ),
        .rst_ni       ( rst_ni                    ),
        .start_i      ( ENABLE_OOO ? issue_i.opcode.div_en : id_ex_reg_i.ctrl.div_en   ),
        .operand_a_i  ( fwd_operand_a             ),
        .operand_b_i  ( fwd_operand_b             ),
        .op_type_i    ( ENABLE_OOO ? issue_i.opcode.funct3 : id_ex_reg_i.ctrl.funct3   ),
        .result_o     ( div_result                ),
        .done_o       ( div_done                  )
    );

    // AI_TAG: MODULE_INSTANCE - FPU Instantiation
    if (ENABLE_FPU) begin : gen_fpu
        fpu_unit u_fpu (
            .clk_i        ( clk_i                     ),
            .rst_ni       ( rst_ni                    ),
            .start_i      ( ENABLE_OOO ? (issue_i.opcode.dpu_en && issue_i.opcode.dpu_unit_sel == 2'b00) : (id_ex_reg_i.ctrl.dpu_en && id_ex_reg_i.ctrl.dpu_unit_sel == 2'b00) ),
            .operand_a_i  ( ENABLE_OOO ? issue_i.v_rs1 : id_ex_reg_i.fpu_operand_a ),
            .operand_b_i  ( ENABLE_OOO ? issue_i.v_rs2 : id_ex_reg_i.fpu_operand_b ),
            .op_type_i    ( ENABLE_OOO ? issue_i.opcode.dpu_op_sel : id_ex_reg_i.ctrl.dpu_op_sel ),
            .result_o     ( fpu_result                ),
            .done_o       ( fpu_done                  )
        );
    end

    // AI_TAG: MODULE_INSTANCE - VPU Instantiation
    if (ENABLE_VPU) begin : gen_vpu
        vpu_unit u_vpu (
            .clk_i        ( clk_i                     ),
            .rst_ni       ( rst_ni                    ),
            .start_i      ( ENABLE_OOO ? (issue_i.opcode.dpu_en && issue_i.opcode.dpu_unit_sel == 2'b01) : (id_ex_reg_i.ctrl.dpu_en && id_ex_reg_i.ctrl.dpu_unit_sel == 2'b01) ),
            .operand_a_i  ( ENABLE_OOO ? issue_i.v_rs1 : id_ex_reg_i.vpu_operand_a ),
            .operand_b_i  ( ENABLE_OOO ? issue_i.v_rs2 : id_ex_reg_i.vpu_operand_b ),
            .op_type_i    ( ENABLE_OOO ? issue_i.opcode.dpu_op_sel : id_ex_reg_i.ctrl.dpu_op_sel ),
            .result_o     ( vpu_result                ),
            .done_o       ( vpu_done                  )
        );
    end

    // AI_TAG: MODULE_INSTANCE - MLIU Instantiation
    if (ENABLE_ML_INFERENCE) begin : gen_mliu
        ml_inference_unit u_mliu (
            .clk_i        ( clk_i                     ),
            .rst_ni       ( rst_ni                    ),
            .start_i      ( ENABLE_OOO ? (issue_i.opcode.dpu_en && issue_i.opcode.dpu_unit_sel == 2'b10) : (id_ex_reg_i.ctrl.dpu_en && id_ex_reg_i.ctrl.dpu_unit_sel == 2'b10) ),
            .operand_a_i  ( ENABLE_OOO ? issue_i.v_rs1 : id_ex_reg_i.mliu_operand_a ),
            .operand_b_i  ( ENABLE_OOO ? issue_i.v_rs2 : id_ex_reg_i.mliu_operand_b ),
            .op_type_i    ( ENABLE_OOO ? issue_i.opcode.dpu_op_sel : id_ex_reg_i.ctrl.dpu_op_sel ),
            .result_o     ( mliu_result               ),
            .done_o       ( mliu_done                 )
        );
    end

    // AI_TAG: INTERNAL_LOGIC - Final Result Mux
    // Selects the result from the active unit.
    assign final_result = (ENABLE_OOO ? issue_i.opcode.mult_en : id_ex_reg_i.ctrl.mult_en) ? mult_result :
                         (ENABLE_OOO ? issue_i.opcode.div_en : id_ex_reg_i.ctrl.div_en)  ? div_result  :
                         ((ENABLE_OOO ? issue_i.opcode.dpu_en : id_ex_reg_i.ctrl.dpu_en) && (ENABLE_OOO ? issue_i.opcode.dpu_unit_sel == 2'b00 : id_ex_reg_i.ctrl.dpu_unit_sel == 2'b00)) ? fpu_result :
                         ((ENABLE_OOO ? issue_i.opcode.dpu_en : id_ex_reg_i.ctrl.dpu_en) && (ENABLE_OOO ? issue_i.opcode.dpu_unit_sel == 2'b01 : id_ex_reg_i.ctrl.dpu_unit_sel == 2'b01)) ? vpu_result :
                         ((ENABLE_OOO ? issue_i.opcode.dpu_en : id_ex_reg_i.ctrl.dpu_en) && (ENABLE_OOO ? issue_i.opcode.dpu_unit_sel == 2'b10 : id_ex_reg_i.ctrl.dpu_unit_sel == 2'b10)) ? mliu_result : alu_result;

    // AI_TAG: INTERNAL_LOGIC - Stall Request Generation
    // Stall the pipeline if a multi-cycle operation (MUL/DIV/DPU) is in progress and not yet complete.
    assign exec_stall_req_o = ENABLE_OOO ? 1'b0 : ((id_ex_reg_i.ctrl.mult_en & !mult_done) || 
                             (id_ex_reg_i.ctrl.div_en  & !div_done)  ||
                             (id_ex_reg_i.ctrl.dpu_en  && 
                               ((id_ex_reg_i.ctrl.dpu_unit_sel == 2'b00 && !fpu_done) ||
                                (id_ex_reg_i.ctrl.dpu_unit_sel == 2'b01 && !vpu_done) ||
                                (id_ex_reg_i.ctrl.dpu_unit_sel == 2'b10 && !mliu_done))));

    // AI_TAG: INTERNAL_LOGIC - Branch Evaluation Logic
    always_comb begin
        branch_taken = 1'b0;
        if (ENABLE_OOO ? issue_i.opcode.is_branch : id_ex_reg_i.ctrl.is_branch) begin
            case (ENABLE_OOO ? issue_i.opcode.funct3 : id_ex_reg_i.ctrl.funct3)
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

    // AI_TAG: INTERNAL_LOGIC - Exception Detection Logic
    // Detect illegal instructions (unimplemented opcodes or invalid combinations)
    always_comb begin
        illegal_instruction = 1'b0;
        
        // Check for unimplemented opcodes
        case (ENABLE_OOO ? issue_i.opcode.alu_op : id_ex_reg_i.ctrl.alu_op)
            ALU_OP_ADD, ALU_OP_SUB, ALU_OP_XOR, ALU_OP_OR, ALU_OP_AND,
            ALU_OP_SLL, ALU_OP_SRL, ALU_OP_SRA, ALU_OP_SLT, ALU_OP_SLTU,
            ALU_OP_LUI, ALU_OP_COPY_A, ALU_OP_COPY_B: illegal_instruction = 1'b0;
            default: illegal_instruction = 1'b1;
        endcase
        
        // Check for invalid CSR operations (if not a CSR instruction)
        if ((ENABLE_OOO ? issue_i.opcode.csr_cmd_en : id_ex_reg_i.ctrl.csr_cmd_en) && !(ENABLE_OOO ? issue_i.opcode.reg_write_en : id_ex_reg_i.ctrl.reg_write_en)) begin
            illegal_instruction = 1'b1;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Division by Zero Detection
    always_comb begin
        div_by_zero = 1'b0;
        if ((ENABLE_OOO ? issue_i.opcode.div_en : id_ex_reg_i.ctrl.div_en) && fwd_operand_b == '0) begin
            div_by_zero = 1'b1;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Overflow Detection
    always_comb begin
        overflow_exception = 1'b0;
        // Check for arithmetic overflow in ADD/SUB operations
        if (((ENABLE_OOO ? issue_i.opcode.alu_op : id_ex_reg_i.ctrl.alu_op) == ALU_OP_ADD || (ENABLE_OOO ? issue_i.opcode.alu_op : id_ex_reg_i.ctrl.alu_op) == ALU_OP_SUB) &&
            alu_overflow_flag) begin
            overflow_exception = 1'b1;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - System Call Detection
    always_comb begin
        ecall_exception = 1'b0;
        breakpoint_exception = 1'b0;
        
        // Check for ECALL instruction (SYSTEM opcode with specific immediate)
        if ((ENABLE_OOO ? issue_i.opcode.csr_cmd_en : id_ex_reg_i.ctrl.csr_cmd_en) && (ENABLE_OOO ? issue_i.opcode.immediate[11:0] : id_ex_reg_i.immediate[11:0]) == 12'h000) begin
            ecall_exception = 1'b1;
        end
        
        // Check for EBREAK instruction (SYSTEM opcode with specific immediate)
        if ((ENABLE_OOO ? issue_i.opcode.csr_cmd_en : id_ex_reg_i.ctrl.csr_cmd_en) && (ENABLE_OOO ? issue_i.opcode.immediate[11:0] : id_ex_reg_i.immediate[11:0]) == 12'h001) begin
            breakpoint_exception = 1'b1;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Exception Information Generation
    always_comb begin
        exception_detected = '0; // Default to no exception
        
        // Determine the instruction's PC and immediate based on OOO enable
        addr_t current_pc = ENABLE_OOO ? issue_i.opcode.pc : id_ex_reg_i.pc;
        word_t current_immediate = ENABLE_OOO ? issue_i.opcode.immediate : id_ex_reg_i.immediate;
        ctrl_signals_t current_ctrl = ENABLE_OOO ? issue_i.opcode.ctrl : id_ex_reg_i.ctrl;

        // Check for exceptions in priority order
        if (ENABLE_MMU && mmu_data_resp_valid && mmu_data_resp.fault) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = mmu_data_resp.fault_type; // Use fault type from MMU
            exception_detected.pc = current_pc;
            exception_detected.tval = alu_result; // The virtual address
            exception_detected.priority = PRIO_DATA_FAULT; // Assuming highest priority for now
        end else if (div_by_zero) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_LOAD_ACCESS_FAULT; // Use load fault as proxy for div by zero
            exception_detected.pc = current_pc;
            exception_detected.tval = fwd_operand_b; // The divisor value
            exception_detected.priority = PRIO_DIV_ZERO;
        end
        else if (overflow_exception) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_LOAD_ACCESS_FAULT; // Use load fault as proxy for overflow
            exception_detected.pc = current_pc;
            exception_detected.tval = alu_result; // The result that overflowed
            exception_detected.priority = PRIO_OVERFLOW;
        end
        else if (ecall_exception) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ECALL_M;
            exception_detected.pc = current_pc;
            exception_detected.tval = '0; // ECALL doesn't have tval
            exception_detected.priority = PRIO_ECALL;
        end
        else if (breakpoint_exception) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_BREAKPOINT;
            exception_detected.pc = current_pc;
            exception_detected.tval = '0; // EBREAK doesn't have tval
            exception_detected.priority = PRIO_BREAKPOINT;
        end
        else if (current_ctrl.dpu_en && !ENABLE_DATA_ACCELERATOR) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = current_pc;
            exception_detected.tval = current_immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
        else if (current_ctrl.dpu_en && current_ctrl.dpu_unit_sel == 2'b00 && !ENABLE_FPU) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = current_pc;
            exception_detected.tval = current_immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
        else if (current_ctrl.dpu_en && current_ctrl.dpu_unit_sel == 2'b01 && !ENABLE_VPU) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = current_pc;
            exception_detected.tval = current_immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
        else if (current_ctrl.dpu_en && current_ctrl.dpu_unit_sel == 2'b10 && !ENABLE_ML_INFERENCE) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = current_pc;
            exception_detected.tval = current_immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
        else if (illegal_instruction) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = current_pc;
            exception_detected.tval = current_immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Branch Prediction Update Logic
    // Generate branch prediction updates for the BPU
    always_comb begin
        bp_update_o.update_valid = id_ex_reg_i.ctrl.is_branch;
        bp_update_o.update_pc = id_ex_reg_i.pc;
        bp_update_o.actual_taken = branch_taken;
        bp_update_o.actual_target = (branch_taken) ? 
                                   (id_ex_reg_i.pc + id_ex_reg_i.immediate) : 
                                   (id_ex_reg_i.pc + 4);
        bp_update_o.is_branch = id_ex_reg_i.ctrl.is_branch;
        bp_update_o.is_jal = id_ex_reg_i.is_jal;
        bp_update_o.jal_target = id_ex_reg_i.jal_target;
        bp_update_o.is_jalr = id_ex_reg_i.is_jalr;
    end

    // AI_TAG: INTERNAL_LOGIC - PC Redirect Logic
    assign pc_redirect_o        = branch_taken || (id_ex_reg_i.ctrl.wb_mux_sel == WB_SEL_PC_P4);
    assign pc_redirect_target_o = (id_ex_reg_i.ctrl.wb_mux_sel == WB_SEL_PC_P4 && id_ex_reg_i.ctrl.alu_op == ALU_OP_ADD)
                                  ? {alu_result[XLEN-1:1], 1'b0}
                                  : id_ex_reg_i.pc + id_ex_reg_i.immediate;

    // Connect to MMU interface
    assign mmu_req_o = mmu_data_req;
    assign mmu_req_valid_o = mmu_data_req_valid;
    assign mmu_data_req_ready = mmu_req_ready_i;
    assign mmu_data_resp = mmu_resp_i;
    assign mmu_data_resp_valid = mmu_resp_valid_i;
    assign mmu_resp_ready_o = mmu_data_resp_ready;

    // MMU request for data access
    assign mmu_data_req.vaddr = alu_result; // Virtual address for memory access
    assign mmu_data_req.is_write = id_ex_reg_i.ctrl.mem_write_en;
    assign mmu_data_req.is_fetch = 1'b0;
    assign mmu_data_req_valid = (id_ex_reg_i.ctrl.mem_read_en || id_ex_reg_i.ctrl.mem_write_en);

    // AI_TAG: INTERNAL_LOGIC - Exception Information Generation
    always_comb begin
        exception_detected = '0; // Default to no exception
        
        // Check for exceptions in priority order
        if (ENABLE_MMU && mmu_data_resp_valid && mmu_data_resp.fault) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = mmu_data_resp.fault_type; // Use fault type from MMU
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = alu_result; // The virtual address
            exception_detected.priority = PRIO_DATA_FAULT; // Assuming highest priority for now
        end else if (div_by_zero) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_LOAD_ACCESS_FAULT; // Use load fault as proxy for div by zero
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = fwd_operand_b; // The divisor value
            exception_detected.priority = PRIO_DIV_ZERO;
        end
        else if (overflow_exception) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_LOAD_ACCESS_FAULT; // Use load fault as proxy for overflow
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = alu_result; // The result that overflowed
            exception_detected.priority = PRIO_OVERFLOW;
        end
        else if (ecall_exception) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ECALL_M;
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = '0; // ECALL doesn't have tval
            exception_detected.priority = PRIO_ECALL;
        end
        else if (breakpoint_exception) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_BREAKPOINT;
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = '0; // EBREAK doesn't have tval
            exception_detected.priority = PRIO_BREAKPOINT;
        end
        else if (id_ex_reg_i.ctrl.dpu_en && !ENABLE_DATA_ACCELERATOR) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = id_ex_reg_i.immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
        else if (id_ex_reg_i.ctrl.dpu_en && id_ex_reg_i.ctrl.dpu_unit_sel == 2'b00 && !ENABLE_FPU) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = id_ex_reg_i.immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
        else if (id_ex_reg_i.ctrl.dpu_en && id_ex_reg_i.ctrl.dpu_unit_sel == 2'b01 && !ENABLE_VPU) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = id_ex_reg_i.immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
        else if (id_ex_reg_i.ctrl.dpu_en && id_ex_reg_i.ctrl.dpu_unit_sel == 2'b10 && !ENABLE_ML_INFERENCE) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = id_ex_reg_i.immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
        else if (illegal_instruction) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_ILLEGAL_INSTRUCTION;
            exception_detected.pc = id_ex_reg_i.pc;
            exception_detected.tval = id_ex_reg_i.immediate; // The instruction that caused the fault
            exception_detected.priority = PRIO_ILLEGAL;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Branch Prediction Update Logic
    // Generate branch prediction updates for the BPU
    always_comb begin
        bp_update_o.update_valid = id_ex_reg_i.ctrl.is_branch;
        bp_update_o.update_pc = id_ex_reg_i.pc;
        bp_update_o.actual_taken = branch_taken;
        bp_update_o.actual_target = (branch_taken) ? 
                                   (id_ex_reg_i.pc + id_ex_reg_i.immediate) : 
                                   (id_ex_reg_i.pc + 4);
        bp_update_o.is_branch = id_ex_reg_i.ctrl.is_branch;
        bp_update_o.is_jal = id_ex_reg_i.is_jal;
        bp_update_o.jal_target = id_ex_reg_i.jal_target;
        bp_update_o.is_jalr = id_ex_reg_i.is_jalr;
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
                ex_mem_reg_q.exception.valid   <= 1'b0; // AI_TAG: NEW - Clear exception on flush
            end else begin
                // AI_TAG: UPDATE - Latch the muxed result into the pipeline register.
                ex_mem_reg_q.alu_result <= ENABLE_MMU ? mmu_data_resp.paddr : final_result; // Use physical address from MMU if enabled
                ex_mem_reg_q.store_data <= fwd_operand_b;
                ex_mem_reg_q.rd_addr    <= id_ex_reg_i.rd_addr;
                ex_mem_reg_q.alu_overflow <= alu_overflow_flag;  // AI_TAG: NEW - Latch overflow flag
                ex_mem_reg_q.exception  <= exception_detected;   // AI_TAG: NEW - Latch exception info
                ex_mem_reg_q.ctrl       <= id_ex_reg_i.ctrl;
            end
        end
    end

    assign ex_mem_reg_o = ex_mem_reg_q;

    // AI_TAG: INTERNAL_LOGIC - Exception Output Assignment
    assign exception_o = exception_detected;

    // AI_TAG: INTERNAL_LOGIC - CSR Interface Assignment
    assign csr_read_en_o = id_ex_reg_i.ctrl.csr_read_en;
    assign csr_addr_o = id_ex_reg_i.csr_addr;
    assign csr_write_en_o = id_ex_reg_i.ctrl.csr_write_en;
    assign csr_addr_w_o = id_ex_reg_i.csr_addr;
    assign csr_wdata_o = id_ex_reg_i.rs1_data; // Or immediate, depending on CSR instruction

endmodule : execute_stage

//=============================================================================
// Dependencies: riscv_core_pkg.sv, alu.sv, mult_unit.sv, div_unit.sv, csr_regfile.sv, branch_predictor.sv
//
// Performance:
//   - Critical Path: ALU operation to result output
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