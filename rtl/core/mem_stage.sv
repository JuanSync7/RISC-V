//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: mem_stage.sv
// Module: mem_stage
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   The Memory Stage (M) of the 5-stage RISC-V pipeline. Drives the AXI4 data
//   memory interface for LOAD and STORE operations, contains data alignment
//   logic for byte and half-word accesses, passes the ALU result through for
//   non-memory operations, and latches results into the MEM/WB pipeline register.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import mmu_pkg::*;

module mem_stage #(
    // AI_TAG: PARAMETER - ENABLE_MMU - Enable Memory Management Unit
    parameter bit ENABLE_MMU = 1,
    parameter bit ENABLE_OOO = 0 // New: Enable Out-of-Order Execution
)
    import riscv_core_pkg::*;
    import ooo_pkg::*;

    // --- Control Signals from Hazard Unit ---
    // AI_TAG: PORT_DESC - stall_w_i - Stalls the MEM/WB pipeline register.
    input  logic        stall_w_i,
    // AI_TAG: PORT_DESC - flush_m_i - Injects a bubble into the MEM/WB register.
    input  logic        flush_m_i,

    // --- Input from Execute Stage ---
    generate
        if (!ENABLE_OOO) begin : gen_inorder_input
            input  ex_mem_reg_t ex_mem_reg_i;
        end
    endgenerate

    // --- MMU Interface (from core_subsystem) ---
    input  mmu_response_t          mmu_data_resp_i,
    input  logic                   mmu_data_resp_valid_i,
    output logic                   mmu_data_resp_ready_o,

    // --- Memory Wrapper Data Interface ---
    // AI_TAG: PORT_DESC - data_req_valid_o - Data request valid.
    output logic        data_req_valid_o,
    // AI_TAG: PORT_DESC - data_req_ready_i - Data request ready.
    input  logic        data_req_ready_i,
    // AI_TAG: PORT_DESC - data_req_addr_o - Data request address.
    output addr_t       data_req_addr_o,
    // AI_TAG: PORT_DESC - data_req_write_o - Data request write flag.
    output logic        data_req_write_o,
    // AI_TAG: PORT_DESC - data_req_size_o - Data request size.
    output logic [2:0]  data_req_size_o,
    // AI_TAG: PORT_DESC - data_req_data_o - Data request write data.
    output word_t       data_req_data_o,
    // AI_TAG: PORT_DESC - data_req_strb_o - Data request write strobes.
    output logic [3:0]  data_req_strb_o,
    // AI_TAG: PORT_DESC - data_rsp_valid_i - Data response valid.
    input  logic        data_rsp_valid_i,
    // AI_TAG: PORT_DESC - data_rsp_ready_o - Data response ready.
    output logic        data_rsp_ready_o,
    // AI_TAG: PORT_DESC - data_rsp_data_i - Data response data.
    input  word_t       data_rsp_data_i,
    // AI_TAG: PORT_DESC - data_rsp_error_i - Data response error,
    input  logic        data_rsp_error_i,

    // OOO Memory Interface
    input  logic        ooo_mem_req_valid_i,
    input  addr_t       ooo_mem_req_addr_i,
    input  logic        ooo_mem_req_write_i,
    input  logic [3:0]  ooo_mem_req_strb_i,
    input  word_t       ooo_mem_req_data_i,
    output logic        ooo_mem_req_ready_o,
    output logic        ooo_mem_rsp_valid_o,
    output word_t       ooo_mem_rsp_data_o,

    // --- Output to Write-back Stage ---
    // AI_TAG: PORT_DESC - mem_wb_reg_o - The MEM/WB pipeline register data.
    output mem_wb_reg_t mem_wb_reg_o,

    // AI_TAG: NEW_PORT - Exception detection output
    // AI_TAG: PORT_DESC - exception_o - Exception information from memory stage
    output exception_info_t exception_o
);
);

    // AI_TAG: INTERNAL_WIRE - Wires for data alignment and write-back data selection.
    word_t       write_data_aligned;
    logic [3:0]  write_strobes;
    word_t       read_data_aligned;
    word_t       wb_data_d;

    // AI_TAG: INTERNAL_WIRE - Exception detection signals
    logic load_addr_misaligned;
    logic store_addr_misaligned;
    logic load_access_fault;
    logic store_access_fault;
    exception_info_t exception_detected;

    mem_wb_reg_t mem_wb_reg_q;

    // AI_TAG: INTERNAL_LOGIC - Write Data Alignment Logic
    // Description: For STORE instructions, this shifts the data to the correct byte lanes
    // and generates the appropriate write strobes based on address and access size (funct3).
    always_comb begin
        logic [2:0] current_funct3 = ENABLE_OOO ? ooo_mem_req_size_i : ex_mem_reg_i.ctrl.funct3;
        addr_t current_alu_result = ENABLE_OOO ? ooo_mem_req_addr_i : ex_mem_reg_i.alu_result;
        word_t current_store_data = ENABLE_OOO ? ooo_mem_req_data_i : ex_mem_reg_i.store_data;

        write_strobes      = 4'b0;
        write_data_aligned = current_store_data; // Default for SW
        case (current_funct3)
            3'b000: begin // SB (Store Byte)
                write_strobes      = 4'b1 << current_alu_result[1:0];
                write_data_aligned = current_store_data << (current_alu_result[1:0] * 8);
            end
            3'b001: begin // SH (Store Half-word)
                write_strobes      = 4'b11 << current_alu_result[1:0];
                write_data_aligned = current_store_data << (current_alu_result[1:0] * 8);
            end
            3'b010: begin // SW (Store Word)
                write_strobes      = 4'b1111;
                write_data_aligned = current_store_data;
            end
            default: ;
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Read Data Alignment Logic
    // Description: For LOAD instructions, this extracts the correct byte or half-word
    // from the 32-bit memory response and sign- or zero-extends it.
    always_comb begin
        logic [15:0] halfword;
        logic [7:0]  byte;
        logic [1:0]  addr_lsb = ENABLE_OOO ? ooo_mem_req_addr_i[1:0] : ex_mem_reg_i.alu_result[1:0];
        word_t current_data_rsp_data = ENABLE_OOO ? ooo_mem_rsp_data_i : data_rsp_data_i;
        logic [2:0] current_funct3 = ENABLE_OOO ? ooo_mem_req_size_i : ex_mem_reg_i.ctrl.funct3;

        read_data_aligned = 'x;
        halfword = current_data_rsp_data[addr_lsb*8 +: 16];
        byte     = current_data_rsp_data[addr_lsb*8 +: 8];

        case (current_funct3)
            3'b000: read_data_aligned = {{24{byte[7]}}, byte};                // LB (Load Byte, sign-extended)
            3'b001: read_data_aligned = {{16{halfword[15]}}, halfword};       // LH (Load Half-word, sign-extended)
            3'b010: read_data_aligned = current_data_rsp_data;                            // LW (Load Word)
            3'b100: read_data_aligned = {24'b0, byte};                        // LBU (Load Byte, Unsigned)
            3'b101: read_data_aligned = {16'b0, halfword};                    // LHU (Load Half-word, Unsigned)
            default: read_data_aligned = current_data_rsp_data; // Should not happen for loads
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Write-back Data Selection Mux
    // Description: Selects the data source for the write-back stage. For LOADs, it's the
    // aligned data from memory. For all other instructions, it's the ALU result.
    assign wb_data_d = (ENABLE_OOO ? !ooo_mem_req_write_i : ex_mem_reg_i.ctrl.mem_read_en) ? read_data_aligned : (ENABLE_OOO ? ooo_mem_req_data_i : ex_mem_reg_i.alu_result);

    // AI_TAG: INTERNAL_LOGIC - Memory Wrapper Interface Control
    // Description: Drives the memory wrapper signals based on control signals from the EX/MEM register.
    // The Hazard Unit is expected to stall this stage until the memory handshake completes.
    generate
        if (ENABLE_OOO) begin : gen_ooo_mem_req
            assign data_req_valid_o = ooo_mem_req_valid_i;
            assign data_req_addr_o  = ooo_mem_req_addr_i;
            assign data_req_write_o = ooo_mem_req_write_i;
            assign data_req_data_o  = ooo_mem_req_data_i;
            assign data_req_strb_o  = ooo_mem_req_strb_i;
            assign ooo_mem_req_ready_o = data_req_ready_i;
            assign ooo_mem_rsp_valid_o = data_rsp_valid_i;
            assign ooo_mem_rsp_data_o  = data_rsp_data_i;
        end else begin : gen_inorder_mem_req
            assign data_req_valid_o = (ex_mem_reg_i.ctrl.mem_read_en || ex_mem_reg_i.ctrl.mem_write_en) &&
                                      (ENABLE_MMU ? (mmu_data_resp_valid_i && !mmu_data_resp_i.fault) : 1'b1);
            assign data_req_addr_o  = ENABLE_MMU ? mmu_data_resp_i.paddr : ex_mem_reg_i.alu_result;
            assign data_req_write_o = ex_mem_reg_i.ctrl.mem_write_en;
            assign data_req_data_o  = write_data_aligned;
            assign data_req_strb_o  = write_strobes;
            assign ooo_mem_req_ready_o = 1'b0; // Tie off if not OOO
            assign ooo_mem_rsp_valid_o = 1'b0; // Tie off if not OOO
            assign ooo_mem_rsp_data_o  = '0;    // Tie off if not OOO
        end
    endgenerate
    assign data_rsp_ready_o = 1'b1; // Always ready to accept response
    assign mmu_data_resp_ready_o = 1'b1; // Always ready to accept MMU response
    
    // Map funct3 to AXI size for memory wrapper
    always_comb begin
        case (ENABLE_OOO ? ooo_mem_req_size_i : ex_mem_reg_i.ctrl.funct3)
            3'b000: data_req_size_o = 3'b000; // SB/LB - 1 byte
            3'b001: data_req_size_o = 3'b001; // SH/LH - 2 bytes
            3'b010: data_req_size_o = 3'b010; // SW/LW - 4 bytes
            3'b100: data_req_size_o = 3'b000; // LBU - 1 byte
            3'b101: data_req_size_o = 3'b001; // LHU - 2 bytes
            default: data_req_size_o = 3'b010; // Default to word
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Memory Exception Detection
    // Address misalignment detection
    always_comb begin
        load_addr_misaligned = 1'b0;
        store_addr_misaligned = 1'b0;
        
        if (ex_mem_reg_i.ctrl.mem_read_en) begin
            case (ex_mem_reg_i.ctrl.funct3)
                3'b001: begin // LH/LHU - halfword alignment check
                    load_addr_misaligned = ex_mem_reg_i.alu_result[0];
                end
                3'b010: begin // LW - word alignment check
                    load_addr_misaligned = |ex_mem_reg_i.alu_result[1:0];
                end
                default: load_addr_misaligned = 1'b0; // Byte loads are always aligned
            endcase
        end
        
        if (ex_mem_reg_i.ctrl.mem_write_en) begin
            case (ex_mem_reg_i.ctrl.funct3)
                3'b001: begin // SH - halfword alignment check
                    store_addr_misaligned = ex_mem_reg_i.alu_result[0];
                end
                3'b010: begin // SW - word alignment check
                    store_addr_misaligned = |ex_mem_reg_i.alu_result[1:0];
                end
                default: store_addr_misaligned = 1'b0; // Byte stores are always aligned
            endcase
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Memory Access Fault Detection
    always_comb begin
        load_access_fault = 1'b0;
        store_access_fault = 1'b0;
        
        // Check for memory response errors
        if (ex_mem_reg_i.ctrl.mem_read_en && data_rsp_valid_i && data_rsp_error_i) begin
            load_access_fault = 1'b1;
        end
        
        if (ex_mem_reg_i.ctrl.mem_write_en && data_rsp_valid_i && data_rsp_error_i) begin
            store_access_fault = 1'b1;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Memory Exception Information Generation
    always_comb begin
        exception_detected = '0; // Default to no exception
        
        logic is_mem_read = ENABLE_OOO ? !ooo_mem_req_write_i : ex_mem_reg_i.ctrl.mem_read_en;
        logic is_mem_write = ENABLE_OOO ? ooo_mem_req_write_i : ex_mem_reg_i.ctrl.mem_write_en;
        addr_t current_alu_result = ENABLE_OOO ? ooo_mem_req_addr_i : ex_mem_reg_i.alu_result;
        logic current_mmu_data_resp_valid = ENABLE_OOO ? 1'b0 : mmu_data_resp_valid_i; // OOO engine handles MMU faults
        mmu_response_t current_mmu_data_resp = ENABLE_OOO ? '0 : mmu_data_resp_i; // OOO engine handles MMU faults
        exception_info_t prev_exception = ENABLE_OOO ? '0 : ex_mem_reg_i.exception; // OOO engine handles previous stage exceptions

        // Check for memory exceptions in priority order
        if (ENABLE_MMU && current_mmu_data_resp_valid && current_mmu_data_resp.fault) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = current_mmu_data_resp.fault_type; // Use fault type from MMU
            exception_detected.pc = prev_exception.pc; // Use PC from previous stage
            exception_detected.tval = current_alu_result; // The virtual address
            exception_detected.priority = PRIO_DATA_FAULT; // Assuming highest priority for now
        } else if (load_addr_misaligned) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_LOAD_ADDR_MISALIGNED;
            exception_detected.pc = prev_exception.pc; // Use PC from previous stage
            exception_detected.tval = current_alu_result; // The misaligned address
            exception_detected.priority = PRIO_MISALIGNED;
        end
        else if (store_addr_misaligned) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_STORE_ADDR_MISALIGNED;
            exception_detected.pc = prev_exception.pc; // Use PC from previous stage
            exception_detected.tval = current_alu_result; // The misaligned address
            exception_detected.priority = PRIO_MISALIGNED;
        end
        else if (load_access_fault) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_LOAD_ACCESS_FAULT;
            exception_detected.pc = prev_exception.pc; // Use PC from previous stage
            exception_detected.tval = current_alu_result; // The faulting address
            exception_detected.priority = PRIO_LOAD_FAULT;
        end
        else if (store_access_fault) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = EXC_CAUSE_STORE_ACCESS_FAULT;
            exception_detected.pc = prev_exception.pc; // Use PC from previous stage
            exception_detected.tval = current_alu_result; // The faulting address
            exception_detected.priority = PRIO_STORE_FAULT;
        end
        else begin
            // Pass through exception from execute stage if no memory exception
            exception_detected = prev_exception;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Exception Output Assignment
    assign exception_o = exception_detected;

    // AI_TAG: INTERNAL_LOGIC - MEM/WB Pipeline Register
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            mem_wb_reg_q.reg_write_en <= 1'b0; // Reset to a bubble
        end else if (!stall_w_i) begin
            if (flush_m_i) begin
                mem_wb_reg_q.reg_write_en <= 1'b0; // Flush to a bubble
                mem_wb_reg_q.exception.valid <= 1'b0; // AI_TAG: NEW - Clear exception on flush
            end else begin
                // AI_TAG: DESIGN_NOTE - The wb_data is only valid if the instruction was a non-memory
                // op OR it was a load and data_rsp_valid_i is asserted by the memory system.
                // The Hazard Unit must stall this stage until data_rsp_valid_i is high for loads.
                mem_wb_reg_q.wb_data      <= wb_data_d;
                mem_wb_reg_q.rd_addr      <= ENABLE_OOO ? ooo_mem_req_addr_i : ex_mem_reg_i.rd_addr;
                mem_wb_reg_q.reg_write_en <= ENABLE_OOO ? 1'b1 : ex_mem_reg_i.ctrl.reg_write_en;
                mem_wb_reg_q.wb_mux_sel   <= ENABLE_OOO ? WB_SEL_MEM : ex_mem_reg_i.ctrl.wb_mux_sel;
                mem_wb_reg_q.exception    <= exception_detected; // AI_TAG: NEW - Latch exception info
            end
        end
        // If stall_w_i, register holds its value.
    end

    assign mem_wb_reg_o = mem_wb_reg_q;

endmodule : mem_stage

//=============================================================================
// Dependencies: riscv_core_pkg.sv, memory_wrapper.sv
//
// Performance:
//   - Critical Path: Memory access to data output
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
