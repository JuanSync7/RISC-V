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

import riscv_core_pkg::*;
import riscv_config_pkg::*;

module mem_stage
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Control Signals from Hazard Unit ---
    // AI_TAG: PORT_DESC - stall_w_i - Stalls the MEM/WB pipeline register.
    input  logic        stall_w_i,
    // AI_TAG: PORT_DESC - flush_m_i - Injects a bubble into the MEM/WB register.
    input  logic        flush_m_i,

    // --- Input from Execute Stage ---
    // AI_TAG: PORT_DESC - ex_mem_reg_i - The EX/MEM pipeline register data.
    input  ex_mem_reg_t ex_mem_reg_i,

    // --- Data Cache Interface ---
    // AI_TAG: PORT_DESC - dcache_if - Interface to the Data Cache.
    memory_req_rsp_if.master dcache_if,

    // --- Output to Write-back Stage ---
    // AI_TAG: PORT_DESC - mem_wb_reg_o - The MEM/WB pipeline register data.
    output mem_wb_reg_t mem_wb_reg_o,

    // AI_TAG: NEW_PORT - Exception detection output
    // AI_TAG: PORT_DESC - exception_o - Exception information from memory stage
    output exception_info_t exception_o
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
        write_strobes      = 4'b0;
        write_data_aligned = ex_mem_reg_i.store_data; // Default for SW
        case (ex_mem_reg_i.ctrl.funct3)
            3'b000: begin // SB (Store Byte)
                write_strobes      = 4'b1 << ex_mem_reg_i.alu_result[1:0];
                write_data_aligned = ex_mem_reg_i.store_data << (ex_mem_reg_i.alu_result[1:0] * 8);
            end
            3'b001: begin // SH (Store Half-word)
                write_strobes      = 4'b11 << ex_mem_reg_i.alu_result[1:0];
                write_data_aligned = ex_mem_reg_i.store_data << (ex_mem_reg_i.alu_result[1:0] * 8);
            end
            3'b010: begin // SW (Store Word)
                write_strobes      = 4'b1111;
                write_data_aligned = ex_mem_reg_i.store_data;
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
        logic [1:0]  addr_lsb = ex_mem_reg_i.alu_result[1:0];

        read_data_aligned = 'x;
        halfword = data_rsp_data_i[addr_lsb*8 +: 16];
        byte     = data_rsp_data_i[addr_lsb*8 +: 8];

        case (ex_mem_reg_i.ctrl.funct3)
            3'b000: read_data_aligned = {{24{byte[7]}}, byte};                // LB (Load Byte, sign-extended)
            3'b001: read_data_aligned = {{16{halfword[15]}}, halfword};       // LH (Load Half-word, sign-extended)
            3'b010: read_data_aligned = data_rsp_data_i;                            // LW (Load Word)
            3'b100: read_data_aligned = {24'b0, byte};                        // LBU (Load Byte, Unsigned)
            3'b101: read_data_aligned = {16'b0, halfword};                    // LHU (Load Half-word, Unsigned)
            default: read_data_aligned = data_rsp_data_i; // Should not happen for loads
        endcase
    end

    // AI_TAG: INTERNAL_LOGIC - Write-back Data Selection Mux
    // Description: Selects the data source for the write-back stage. For LOADs, it's the
    // aligned data from memory. For all other instructions, it's the ALU result.
    assign wb_data_d = (ex_mem_reg_i.ctrl.mem_read_en) ? dcache_if.rsp.data : ex_mem_reg_i.alu_result;

    // AI_TAG: INTERNAL_LOGIC - Data Cache Interface Control
    // Description: Drives the data cache signals based on control signals from the EX/MEM register.
    // The Hazard Unit is expected to stall this stage until the cache handshake completes.
    assign dcache_if.req_valid = ex_mem_reg_i.ctrl.mem_read_en || ex_mem_reg_i.ctrl.mem_write_en;
    assign dcache_if.req.addr  = ex_mem_reg_i.alu_result;
    assign dcache_if.req.write = ex_mem_reg_i.ctrl.mem_write_en;
    assign dcache_if.req.data  = write_data_aligned;
    assign dcache_if.req.strb  = write_strobes;
    assign dcache_if.rsp_ready = 1'b1; // Always ready to accept response
    
    // Map funct3 to AXI size for memory wrapper
    always_comb begin
        case (ex_mem_reg_i.ctrl.funct3)
            3'b000: dcache_if.req.size = 3'b000; // SB/LB - 1 byte
            3'b001: dcache_if.req.size = 3'b001; // SH/LH - 2 bytes
            3'b010: dcache_if.req.size = 3'b010; // SW/LW - 4 bytes
            3'b100: dcache_if.req.size = 3'b000; // LBU - 1 byte
            3'b101: dcache_if.req.size = 3'b001; // LHU - 2 bytes
            default: dcache_if.req.size = 3'b010; // Default to word
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
        if (ex_mem_reg_i.ctrl.mem_read_en && dcache_if.rsp_valid && dcache_if.rsp.error) begin
            load_access_fault = 1'b1;
        end
        
        if (ex_mem_reg_i.ctrl.mem_write_en && dcache_if.rsp_valid && dcache_if.rsp.error) begin
            store_access_fault = 1'b1;
        end
    end

    // AI_TAG: INTERNAL_LOGIC - Memory Exception Information Generation
    always_comb begin
        exception_detected = '0; // Default to no exception
        
        // Check for memory exceptions in priority order
        if (load_addr_misaligned) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = riscv_config_pkg::CAUSE_MISALIGNED_LOAD;
            exception_detected.pc = ex_mem_reg_i.exception.pc; // Use PC from previous stage
            exception_detected.tval = ex_mem_reg_i.alu_result; // The misaligned address
            exception_detected.priority = riscv_config_pkg::PRIO_MISALIGNED_MEM;
        end
        else if (store_addr_misaligned) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = riscv_config_pkg::CAUSE_MISALIGNED_STORE;
            exception_detected.pc = ex_mem_reg_i.exception.pc; // Use PC from previous stage
            exception_detected.tval = ex_mem_reg_i.alu_result; // The misaligned address
            exception_detected.priority = riscv_config_pkg::PRIO_MISALIGNED_MEM;
        end
        else if (load_access_fault) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = riscv_config_pkg::CAUSE_LOAD_ACCESS;
            exception_detected.pc = ex_mem_reg_i.exception.pc; // Use PC from previous stage
            exception_detected.tval = ex_mem_reg_i.alu_result; // The faulting address
            exception_detected.priority = riscv_config_pkg::PRIO_MEM_FAULT;
        end
        else if (store_access_fault) begin
            exception_detected.valid = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause = riscv_config_pkg::CAUSE_STORE_ACCESS;
            exception_detected.pc = ex_mem_reg_i.exception.pc; // Use PC from previous stage
            exception_detected.tval = ex_mem_reg_i.alu_result; // The faulting address
            exception_detected.priority = riscv_config_pkg::PRIO_MEM_FAULT;
        end
        else begin
            // Pass through exception from execute stage if no memory exception
            exception_detected = ex_mem_reg_i.exception;
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
                mem_wb_reg_q.rd_addr      <= ex_mem_reg_i.rd_addr;
                mem_wb_reg_q.reg_write_en <= ex_mem_reg_i.ctrl.reg_write_en;
                mem_wb_reg_q.wb_mux_sel   <= ex_mem_reg_i.ctrl.wb_mux_sel;
                mem_wb_reg_q.exception    <= exception_detected; // AI_TAG: NEW - Latch exception info
            end
        end
        // If stall_w_i, register holds its value.
    end

    assign mem_wb_reg_o = mem_wb_reg_q;

endmodule : mem_stage

//=============================================================================
// Dependencies: riscv_core_pkg.sv, memory_wrapper.sv
// Instantiated In:
//   - rtl/core/integration/core_subsystem.sv
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
