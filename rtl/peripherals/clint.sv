//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: clint.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: clint
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-29
// DESCRIPTION: Core Local Interruptor (CLINT) for RISC-V timer and software interrupts.
// PRIMARY_PURPOSE: Provide machine timer and software interrupt functionality per RISC-V spec.
// ROLE_IN_SYSTEM: Generate timer interrupts and handle inter-processor interrupts in multi-core.
// PROBLEM_SOLVED: Implements standard RISC-V timer and software interrupt mechanism.
// MODULE_TYPE: RTL
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V Privileged Specification v1.12
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

module clint
import riscv_base_pkg::*;
import riscv_system_config_pkg::*;
#(
    parameter integer NUM_CORES      = DEFAULT_CORE_CONFIG.num_cores,
    parameter integer CLINT_BASE     = 32'h0200_0000,
    parameter integer MSIP_OFFSET    = 32'h0000_0000,
    parameter integer MTIMECMP_OFFSET = 32'h0000_4000,
    parameter integer MTIME_OFFSET   = 32'h0000_BFF8
) (
    // Clock and Reset
    input  logic                    clk_i,              // AI_TAG: PORT_DESC - System clock
    input  logic                    rst_ni,             // AI_TAG: PORT_DESC - Active-low asynchronous reset
    input  logic                    rtc_i,              // AI_TAG: PORT_DESC - Real-time clock input (1-100MHz)
    
    // Memory-mapped Interface (AXI4-Lite compatible)
    input  logic                    mem_req_i,          // AI_TAG: PORT_DESC - Memory request valid
    input  logic                    mem_we_i,           // AI_TAG: PORT_DESC - Memory write enable
    input  logic [31:0]             mem_addr_i,         // AI_TAG: PORT_DESC - Memory address
    input  logic [31:0]             mem_wdata_i,        // AI_TAG: PORT_DESC - Memory write data
    input  logic [3:0]              mem_be_i,           // AI_TAG: PORT_DESC - Byte enables
    output logic [31:0]             mem_rdata_o,        // AI_TAG: PORT_DESC - Memory read data
    output logic                    mem_ready_o,        // AI_TAG: PORT_DESC - Memory transaction ready
    
    // Interrupt Outputs (per core)
    output logic [NUM_CORES-1:0]    msip_o,             // AI_TAG: PORT_DESC - Machine software interrupt pending
    output logic [NUM_CORES-1:0]    mtip_o              // AI_TAG: PORT_DESC - Machine timer interrupt pending
);

    //-------------------------------------------------------------------------
    // CLINT Memory Map
    //-------------------------------------------------------------------------
    // AI_TAG: FEATURE - Standard RISC-V CLINT memory map
    // MSIP[n]      : 0x0000_0000 + 4*n  (Machine Software Interrupt Pending)
    // MTIMECMP[n]  : 0x0000_4000 + 8*n  (Machine Timer Compare)
    // MTIME        : 0x0000_BFF8        (Machine Timer, 64-bit)
    
    //-------------------------------------------------------------------------
    // Internal Registers
    //-------------------------------------------------------------------------
    // Software interrupt pending registers (one per core)
    logic [NUM_CORES-1:0] msip_r;
    
    // Timer compare registers (64-bit per core)
    logic [63:0] mtimecmp_r [NUM_CORES];
    
    // Global timer register (64-bit)
    logic [63:0] mtime_r;
    
    // RTC synchronization
    logic rtc_sync_r, rtc_sync_rr;
    logic rtc_edge;
    
    //-------------------------------------------------------------------------
    // Address Decoding
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Decode memory-mapped register addresses
    logic [31:0] local_addr;
    logic msip_access;
    logic mtimecmp_access;
    logic mtime_access;
    logic [4:0] core_idx;
    logic addr_valid;
    
    assign local_addr = mem_addr_i - CLINT_BASE;
    
    always_comb begin
        msip_access = 1'b0;
        mtimecmp_access = 1'b0;
        mtime_access = 1'b0;
        core_idx = '0;
        addr_valid = 1'b0;
        
        // Check if address is in MSIP range
        if (local_addr >= MSIP_OFFSET && local_addr < MSIP_OFFSET + 4*NUM_CORES) begin
            msip_access = 1'b1;
            core_idx = (local_addr - MSIP_OFFSET) >> 2;
            addr_valid = 1'b1;
        end
        // Check if address is in MTIMECMP range
        else if (local_addr >= MTIMECMP_OFFSET && local_addr < MTIMECMP_OFFSET + 8*NUM_CORES) begin
            mtimecmp_access = 1'b1;
            core_idx = (local_addr - MTIMECMP_OFFSET) >> 3;
            addr_valid = 1'b1;
        end
        // Check if address is MTIME
        else if (local_addr >= MTIME_OFFSET && local_addr < MTIME_OFFSET + 8) begin
            mtime_access = 1'b1;
            addr_valid = 1'b1;
        end
    end
    
    //-------------------------------------------------------------------------
    // RTC Edge Detection
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Synchronize and detect RTC edges for timer increment
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            rtc_sync_r  <= 1'b0;
            rtc_sync_rr <= 1'b0;
        end else begin
            rtc_sync_r  <= rtc_i;
            rtc_sync_rr <= rtc_sync_r;
        end
    end
    
    assign rtc_edge = rtc_sync_r && !rtc_sync_rr;
    
    //-------------------------------------------------------------------------
    // Timer Register (MTIME)
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - 64-bit timer incremented on RTC edges
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            mtime_r <= 64'h0;
        end else if (mem_req_i && mem_we_i && mtime_access) begin
            // Write to MTIME
            if (local_addr[2]) begin
                // Upper 32 bits
                mtime_r[63:32] <= mem_wdata_i;
            end else begin
                // Lower 32 bits
                mtime_r[31:0] <= mem_wdata_i;
            end
        end else if (rtc_edge) begin
            // Increment on RTC edge
            mtime_r <= mtime_r + 64'h1;
        end
    end
    
    //-------------------------------------------------------------------------
    // Software Interrupt Registers (MSIP)
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Per-core software interrupt pending bits
    genvar i;
    generate
        for (i = 0; i < NUM_CORES; i++) begin : gen_msip
            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    msip_r[i] <= 1'b0;
                end else if (mem_req_i && mem_we_i && msip_access && core_idx == i) begin
                    msip_r[i] <= mem_wdata_i[0];
                end
            end
        end
    endgenerate
    
    //-------------------------------------------------------------------------
    // Timer Compare Registers (MTIMECMP)
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Per-core 64-bit timer compare values
    generate
        for (i = 0; i < NUM_CORES; i++) begin : gen_mtimecmp
            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    mtimecmp_r[i] <= 64'hFFFF_FFFF_FFFF_FFFF;
                end else if (mem_req_i && mem_we_i && mtimecmp_access && core_idx == i) begin
                    if (local_addr[2]) begin
                        // Upper 32 bits
                        mtimecmp_r[i][63:32] <= mem_wdata_i;
                    end else begin
                        // Lower 32 bits
                        mtimecmp_r[i][31:0] <= mem_wdata_i;
                    end
                end
            end
        end
    endgenerate
    
    //-------------------------------------------------------------------------
    // Read Data Multiplexer
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Select read data based on address
    always_comb begin
        mem_rdata_o = 32'h0;
        
        if (msip_access && core_idx < NUM_CORES) begin
            mem_rdata_o = {31'h0, msip_r[core_idx]};
        end
        else if (mtimecmp_access && core_idx < NUM_CORES) begin
            if (local_addr[2]) begin
                mem_rdata_o = mtimecmp_r[core_idx][63:32];
            end else begin
                mem_rdata_o = mtimecmp_r[core_idx][31:0];
            end
        end
        else if (mtime_access) begin
            if (local_addr[2]) begin
                mem_rdata_o = mtime_r[63:32];
            end else begin
                mem_rdata_o = mtime_r[31:0];
            end
        end
    end
    
    //-------------------------------------------------------------------------
    // Memory Interface Response
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Single-cycle response for all accesses
    assign mem_ready_o = mem_req_i && addr_valid;
    
    //-------------------------------------------------------------------------
    // Interrupt Generation
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Generate timer interrupts by comparing mtime with mtimecmp
    generate
        for (i = 0; i < NUM_CORES; i++) begin : gen_interrupts
            // Software interrupt is direct from register
            assign msip_o[i] = msip_r[i];
            
            // Timer interrupt when mtime >= mtimecmp
            assign mtip_o[i] = (mtime_r >= mtimecmp_r[i]);
        end
    endgenerate
    
    //-------------------------------------------------------------------------
    // Assertions
    //-------------------------------------------------------------------------
    // AI_TAG: ASSERTION - Valid address access
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    ValidAddress: assert property (@(posedge clk_i) disable iff (!rst_ni)
        mem_req_i |-> addr_valid);
    
    // AI_TAG: ASSERTION - Core index within bounds
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    CoreIdxBounds: assert property (@(posedge clk_i) disable iff (!rst_ni)
        (msip_access || mtimecmp_access) |-> (core_idx < NUM_CORES));
    
    // AI_TAG: ASSERTION - Timer monotonicity
    // AI_TAG: ASSERTION_TYPE - Formal
    // AI_TAG: ASSERTION_SEVERITY - Error
    TimerMonotonic: assert property (@(posedge clk_i) disable iff (!rst_ni)
        !mem_we_i |-> (mtime_r >= $past(mtime_r)));

endmodule : clint

//=============================================================================
// Dependencies: riscv_base_pkg, riscv_system_config_pkg
//
// Instantiated In:
//   - soc/riscv_soc_top.sv
//   - platform/riscv_platform.sv
//
// Performance:
//   - Critical Path: Timer comparison logic
//   - Max Frequency: > 200MHz typical
//   - Area: Scales with NUM_CORES
//
// Verification Coverage:
//   - Code Coverage: TBD
//   - Functional Coverage: TBD
//   - Branch Coverage: TBD
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Vivado
//   - Clock Domains: 2 (clk_i, rtc_i)
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: clint_tb.sv
//   - Test Vectors: TBD
//
//----
// Revision History:
// Version | Date       | Author         | Description
//=============================================================================
// 1.0.0   | 2025-01-29 | DesignAI      | Initial release
//=============================================================================