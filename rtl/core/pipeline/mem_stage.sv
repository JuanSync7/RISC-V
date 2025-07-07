"""//=============================================================================
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
//   The Memory Stage (M) of the 5-stage RISC-V pipeline. Drives the data
//   memory interface for LOAD and STORE operations, contains data alignment
//   logic for byte and half-word accesses, passes the ALU result through for
//   non-memory operations, and latches results into the MEM/WB pipeline register.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_core_types_pkg::*;

// AI_TAG: MODULE_SUMMARY
// The mem_stage module implements the Memory Access stage of the RISC-V pipeline.
// Key Functions:
// 1.  Handles LOAD and STORE operations by interfacing with the data cache.
// 2.  Performs data alignment for byte (LB, LBU, SB) and half-word (LH, LHU, SH) accesses.
// 3.  Detects memory-related exceptions:
//     - Misaligned memory access (Load and Store).
//     - Memory access faults (from cache/memory system).
// 4.  Passes results from the Execute stage (ALU result) to the Write-back stage for non-memory instructions.
// 5.  Selects the correct data for write-back (either memory data for LOADs or ALU result).
// 6.  Propagates pipeline control signals (stall, flush) and handles exception propagation.
module mem_stage
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // --- Control Signals from Hazard Unit ---
    input  logic        stall_w_i,          // AI_TAG: PORT_DESC - Stalls the MEM/WB pipeline register.
    input  logic        flush_m_i,          // AI_TAG: PORT_DESC - Injects a bubble into the MEM/WB register.

    // --- Input from Execute Stage ---
    input  ex_mem_reg_t ex_mem_reg_i,       // AI_TAG: PORT_DESC - The EX/MEM pipeline register data.

    // --- Data Cache Interface ---
    memory_req_rsp_if.master dcache_if,     // AI_TAG: PORT_DESC - Interface to the Data Cache.

    // --- Output to Write-back Stage ---
    output mem_wb_reg_t mem_wb_reg_o,       // AI_TAG: PORT_DESC - The MEM/WB pipeline register data.

    // --- Exception Output ---
    output exception_info_t exception_o     // AI_TAG: PORT_DESC - Exception information from memory stage.
);

    // AI_TAG: INTERNAL_SIGNAL - Wires for data alignment and write-back data selection.
    word_t       write_data_aligned;
    logic [3:0]  write_strobes;
    word_t       read_data_aligned;
    word_t       wb_data_d;

    // AI_TAG: INTERNAL_SIGNAL - Exception detection signals.
    logic        load_addr_misaligned;
    logic        store_addr_misaligned;
    logic        load_access_fault;
    logic        store_access_fault;
    exception_info_t exception_detected;

    // AI_TAG: INTERNAL_REGISTER - Pipeline register between MEM and WB stages.
    mem_wb_reg_t mem_wb_reg_q;

    //=========================================================================
    // Write Data Alignment Logic
    //=========================================================================
    // AI_TAG: LOGIC_BLOCK - Write Data Alignment
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
            default: begin
                write_strobes      = 4'b0;
                write_data_aligned = ex_mem_reg_i.store_data;
            end
        endcase
    end

    //=========================================================================
    // Read Data Alignment Logic
    //=========================================================================
    // AI_TAG: LOGIC_BLOCK - Read Data Alignment
    // Description: For LOAD instructions, this extracts the correct byte or half-word
    // from the 32-bit memory response and sign- or zero-extends it.
    always_comb begin
        logic [15:0] halfword;
        logic [7:0]  byte;
        logic [1:0]  addr_lsb = ex_mem_reg_i.alu_result[1:0];

        // Extract byte/halfword based on LSBs of the address
        halfword = dcache_if.rsp.data >> (addr_lsb[1] * 16);
        byte     = dcache_if.rsp.data >> (addr_lsb * 8);

        case (ex_mem_reg_i.ctrl.funct3)
            3'b000: read_data_aligned = {{($bits(word_t)-8){byte[7]}}, byte};                // LB (Load Byte, sign-extended)
            3'b001: read_data_aligned = {{($bits(word_t)-16){halfword[15]}}, halfword};       // LH (Load Half-word, sign-extended)
            3'b010: read_data_aligned = dcache_if.rsp.data;                   // LW (Load Word)
            3'b100: read_data_aligned = {($bits(word_t)-8)'b0, byte};                        // LBU (Load Byte, Unsigned)
            3'b101: read_data_aligned = {($bits(word_t)-16)'b0, halfword};                    // LHU (Load Half-word, Unsigned)
            default: read_data_aligned = dcache_if.rsp.data; // Default for non-load or unexpected funct3
        endcase
    end

    //=========================================================================
    // Write-back Data Selection
    //=========================================================================
    // AI_TAG: LOGIC_BLOCK - Write-back Data Selection Mux
    // Description: Selects the data source for the write-back stage. For LOADs, it's the
    // aligned data from memory. For all other instructions, it's the ALU result.
    assign wb_data_d = (ex_mem_reg_i.ctrl.mem_read_en) ? read_data_aligned : ex_mem_reg_i.alu_result;

    //=========================================================================
    // Data Cache Interface Control
    //=========================================================================
    // AI_TAG: LOGIC_BLOCK - Data Cache Interface Control
    // Description: Drives the data cache signals based on control signals from the EX/MEM register.
    // The Hazard Unit is expected to stall this stage until the cache handshake completes.
    assign dcache_if.req_valid = ex_mem_reg_i.ctrl.mem_read_en || ex_mem_reg_i.ctrl.mem_write_en;
    assign dcache_if.req.addr  = ex_mem_reg_i.alu_result;
    assign dcache_if.req.write = ex_mem_reg_i.ctrl.mem_write_en;
    assign dcache_if.req.data  = write_data_aligned;
    assign dcache_if.req.strb  = write_strobes;
    assign dcache_if.rsp_ready = 1'b1; // Always ready to accept response

    // Map funct3 to memory request size
    always_comb begin
        case (ex_mem_reg_i.ctrl.funct3)
            3'b000, 3'b100: dcache_if.req.size = MEM_SIZE_B;  // 1 byte
            3'b001, 3'b101: dcache_if.req.size = MEM_SIZE_H;  // 2 bytes
            3'b010:         dcache_if.req.size = MEM_SIZE_W;  // 4 bytes
            default:        dcache_if.req.size = MEM_SIZE_W;  // Default to word
        endcase
    end

    //=========================================================================
    // Memory Exception Detection
    //=========================================================================
    // AI_TAG: LOGIC_BLOCK - Address Misalignment Detection
    always_comb begin
        load_addr_misaligned = 1'b0;
        if (ex_mem_reg_i.ctrl.mem_read_en) begin
            case (ex_mem_reg_i.ctrl.funct3[1:0])
                2'b01: load_addr_misaligned = ex_mem_reg_i.alu_result[0];      // LH/LHU
                2'b10: load_addr_misaligned = |ex_mem_reg_i.alu_result[1:0]; // LW
                default: load_addr_misaligned = 1'b0;
            endcase
        end

        store_addr_misaligned = 1'b0;
        if (ex_mem_reg_i.ctrl.mem_write_en) begin
            case (ex_mem_reg_i.ctrl.funct3[1:0])
                2'b01: store_addr_misaligned = ex_mem_reg_i.alu_result[0];     // SH
                2'b10: store_addr_misaligned = |ex_mem_reg_i.alu_result[1:0];// SW
                default: store_addr_misaligned = 1'b0;
            endcase
        end
    end

    // AI_TAG: LOGIC_BLOCK - Memory Access Fault Detection
    // Description: Checks for memory response errors from the cache.
    always_comb begin
        load_access_fault  = ex_mem_reg_i.ctrl.mem_read_en  && dcache_if.rsp_valid && dcache_if.rsp.error;
        store_access_fault = ex_mem_reg_i.ctrl.mem_write_en && dcache_if.rsp_valid && dcache_if.rsp.error;
    end

    // AI_TAG: LOGIC_BLOCK - Memory Exception Information Generation
    // Description: Generates exception information based on detected faults, prioritizing them.
    always_comb begin
        exception_detected = ex_mem_reg_i.exception; // Pass through existing exceptions by default

        // Check for memory exceptions in priority order
        if (load_addr_misaligned) begin
            exception_detected.valid    = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause    = CONFIG_CAUSE_MISALIGNED_LOAD;
            exception_detected.pc       = ex_mem_reg_i.pc;
            exception_detected.tval     = ex_mem_reg_i.alu_result; // The misaligned address
            exception_detected.priority = PRIO_MISALIGNED_MEM;
        end
        else if (store_addr_misaligned) begin
            exception_detected.valid    = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause    = CONFIG_CAUSE_MISALIGNED_STORE;
            exception_detected.pc       = ex_mem_reg_i.pc;
            exception_detected.tval     = ex_mem_reg_i.alu_result; // The misaligned address
            exception_detected.priority = PRIO_MISALIGNED_MEM;
        end
        else if (load_access_fault) begin
            exception_detected.valid    = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause    = CONFIG_CAUSE_LOAD_ACCESS;
            exception_detected.pc       = ex_mem_reg_i.pc;
            exception_detected.tval     = ex_mem_reg_i.alu_result; // The faulting address
            exception_detected.priority = PRIO_MEM_FAULT;
        end
        else if (store_access_fault) begin
            exception_detected.valid    = 1'b1;
            exception_detected.exc_type = EXC_TYPE_EXCEPTION;
            exception_detected.cause    = CONFIG_CAUSE_STORE_ACCESS;
            exception_detected.pc       = ex_mem_reg_i.pc;
            exception_detected.tval     = ex_mem_reg_i.alu_result; // The faulting address
            exception_detected.priority = PRIO_MEM_FAULT;
        end
    end

    // AI_TAG: DRIVER - Exception Output Assignment
    assign exception_o = exception_detected;

    //=========================================================================
    // MEM/WB Pipeline Register
    //=========================================================================
    // AI_TAG: REGISTER - MEM/WB Pipeline Register
    // Description: Latches the results of the memory stage, to be used by the
    // write-back stage. Can be stalled or flushed by the pipeline control logic.
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            mem_wb_reg_q              <= '{default:'0};
            mem_wb_reg_q.reg_write_en <= 1'b0; // Reset to a bubble
        end else if (!stall_w_i) begin
            if (flush_m_i) begin
                mem_wb_reg_q.reg_write_en    <= 1'b0; // Flush to a bubble
                mem_wb_reg_q.exception.valid <= 1'b0;
            end else begin
                // AI_TAG: DESIGN_NOTE - The wb_data is only valid if the instruction was a non-memory
                // op OR it was a load and the cache response is valid.
                // The Hazard Unit must stall this stage until the response is valid for loads.
                mem_wb_reg_q.wb_data      <= wb_data_d;
                mem_wb_reg_q.rd_addr      <= ex_mem_reg_i.rd_addr;
                mem_wb_reg_q.reg_write_en <= ex_mem_reg_i.ctrl.reg_write_en;
                mem_wb_reg_q.wb_mux_sel   <= ex_mem_reg_i.ctrl.wb_mux_sel;
                mem_wb_reg_q.pc           <= ex_mem_reg_i.pc;
                mem_wb_reg_q.exception    <= exception_detected;
            end
        end
        // If stall_w_i, register holds its value.
    end

    // AI_TAG: DRIVER - Pipeline Register Output Assignment
    assign mem_wb_reg_o = mem_wb_reg_q;

endmodule : mem_stage

//=============================================================================
// 'include "riscv_core_pkg.sv"
// 'include "memory_req_rsp_if.sv"
//
// Dependencies: riscv_core_pkg.sv, riscv_config_pkg.sv, memory_req_rsp_if.sv
// Instantiated In:
//   - rtl/core/integration/core_subsystem.sv
//
// Performance:
//   - Critical Path: dcache_if.rsp.data -> read_data_aligned -> wb_data_d -> mem_wb_reg_q.wb_data
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
// 1.1.0   | 2025-07-07 | DesignAI           | Corrected read data alignment, wb_data selection, exception logic, and added comments.
// 1.0.0   | 2025-06-27 | DesignAI           | Initial release
//=============================================================================
""
