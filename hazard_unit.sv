////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-28
// Design Name:   RV32IM Core
// Module Name:   hazard_unit
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   Hazard Detection and Resolution Unit for the 5-stage pipeline.
//                This is a purely combinational module that generates stall,
//                flush, and forwarding control signals. It prevents data and
//                control hazards to ensure correct program execution.
//
// Dependencies:  riscv_core_pkg.sv
//
// Revision:
// Revision 1.1.0 - Implemented memory and execution stall logic. Corrected
//                  load-use hazard detection and resolution mechanism.
// Revision 1.0.0 - File Created
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps
`default_nettype none

module hazard_unit
    import riscv_core_pkg::*;
(
    // --- Pipeline Register State Inputs ---
    input  reg_addr_t   rs1_addr_d_i,       // rs1 address from instruction currently in Decode
    input  reg_addr_t   rs2_addr_d_i,       // rs2 address from instruction currently in Decode
    input  id_ex_reg_t  id_ex_reg_i,        // State of the ID/EX pipeline register
    input  ex_mem_reg_t ex_mem_reg_i,       // State of the EX/MEM pipeline register
    input  mem_wb_reg_t mem_wb_reg_i,       // State of the MEM/WB pipeline register

    // --- Control and Status Inputs ---
    input  logic        pc_redirect_e_i,    // Asserted by Execute stage on a taken branch/jump
    input  logic        exec_stall_req_i,   // Stall request from a multi-cycle unit in Execute
    input  logic        i_arvalid_i,        // Instruction fetch is valid
    input  logic        i_arready_i,        // Instruction memory is ready
    input  logic        d_mem_req_i,        // Data memory access is requested from Mem stage
    input  logic        d_mem_ready_i,      // Data memory is ready for the request

    // --- Pipeline Control Outputs ---
    output logic        stall_f_o,
    output logic        stall_d_o,
    output logic        stall_m_o,
    output logic        stall_w_o,
    output logic        flush_f_o,
    output logic        flush_d_o,
    output logic        flush_e_o,
    output logic [1:0]  forward_a_sel_o,
    output logic [1:0]  forward_b_sel_o
);

    localparam logic [1:0] FWD_SEL_REG = 2'b00;
    localparam logic [1:0] FWD_SEL_MEM = 2'b01;
    localparam logic [1:0] FWD_SEL_WB  = 2'b10;

    always_comb begin
        // --- Primary Hazard/Stall Source Detection ---
        logic load_use_hazard;
        logic m_ext_stall;
        logic i_mem_wait_stall;
        logic d_mem_wait_stall;
        logic stall_e; // Internal stall signal for execute stage

        // --- Default assignments: no hazards ---
        stall_f_o         = 1'b0;
        stall_d_o         = 1'b0;
        stall_m_o         = 1'b0;
        stall_w_o         = 1'b0;
        flush_f_o         = 1'b0;
        flush_d_o         = 1'b0;
        flush_e_o         = 1'b0;
        forward_a_sel_o   = FWD_SEL_REG;
        forward_b_sel_o   = FWD_SEL_REG;

        // AI_TAG: HAZARD_DETECTION - Load-Use Data Hazard
        // An instruction in Decode needs the result of a LOAD from Execute.
        // This is the one case where forwarding is not enough.
        load_use_hazard = id_ex_reg_i.ctrl.mem_read_en &&
                          (id_ex_reg_i.rd_addr != '0) &&
                          ((id_ex_reg_i.rd_addr == rs1_addr_d_i) || (id_ex_reg_i.rd_addr == rs2_addr_d_i));

        // AI_TAG: STALL_LOGIC - Multi-cycle Execution Stall (e.g., for future M-extension)
        m_ext_stall = exec_stall_req_i;

        // AI_TAG: STALL_LOGIC - Instruction Memory Wait
        // Stall the Fetch stage if it sends a request but the memory is not ready.
        i_mem_wait_stall = i_arvalid_i & !i_arready_i;

        // AI_TAG: STALL_LOGIC - Data Memory Wait
        // Stall the Memory stage if it sends a request but the memory is not ready.
        d_mem_wait_stall = d_mem_req_i & !d_mem_ready_i;

        // --- Combine Stall Signals and Propagate Backwards ---
        stall_w_o = 1'b0; // Write-back stage never stalls
        stall_m_o = d_mem_wait_stall;
        stall_e   = stall_m_o || m_ext_stall; // An internal signal representing stall conditions originating from E or later
        stall_d_o = stall_e || load_use_hazard;
        stall_f_o = stall_d_o || i_mem_wait_stall;

        // --- Flush Signal Generation ---
        // AI_TAG: HAZARD_DETECTION - Control Hazard Flush
        // On a PC redirect (branch/jump), flush the two instructions behind it.
        if (pc_redirect_e_i) begin
            flush_f_o = 1'b1;
            flush_d_o = 1'b1;
        end

        // AI_TAG: HAZARD_RESOLUTION - Bubble injection for Load-Use Hazard
        // To resolve the load-use hazard, we stall F/D and inject a bubble into E.
        // The flush_e signal is used by the execute stage to create this bubble.
        if (load_use_hazard) begin
            flush_e_o = 1'b1;
        end

        // --- Forwarding Logic ---
        // AI_TAG: FORWARDING_LOGIC - EX/MEM -> EX Path (Highest Priority Forward)
        if (ex_mem_reg_i.ctrl.reg_write_en && (ex_mem_reg_i.rd_addr != '0)) begin
            if (ex_mem_reg_i.rd_addr == id_ex_reg_i.rd_addr) begin
                forward_a_sel_o = FWD_SEL_MEM;
            end
            if (ex_mem_reg_i.rd_addr == id_ex_reg_i.rd_addr) begin
                forward_b_sel_o = FWD_SEL_MEM;
            end
        end

        // AI_TAG: FORWARDING_LOGIC - MEM/WB -> EX Path
        if (mem_wb_reg_i.reg_write_en && (mem_wb_reg_i.rd_addr != '0)) begin
            if ((mem_wb_reg_i.rd_addr == id_ex_reg_i.rd_addr) && (forward_a_sel_o == FWD_SEL_REG)) begin
                forward_a_sel_o = FWD_SEL_WB;
            end
            if ((mem_wb_reg_i.rd_addr == id_ex_reg_i.rd_addr) && (forward_b_sel_o == FWD_SEL_REG)) begin
                forward_b_sel_o = FWD_SEL_WB;
            end
        end
    end

endmodule : hazard_unit