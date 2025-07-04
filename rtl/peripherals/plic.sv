//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: plic.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: plic
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-29
// DESCRIPTION: Platform-Level Interrupt Controller (PLIC) for RISC-V external interrupts.
// PRIMARY_PURPOSE: Manage and prioritize external interrupts across multiple cores.
// ROLE_IN_SYSTEM: Routes external interrupts to cores based on priority and enable masks.
// PROBLEM_SOLVED: Implements standard RISC-V PLIC for flexible interrupt handling.
// MODULE_TYPE: RTL
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V Platform-Level Interrupt Controller Specification
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

module plic
import riscv_base_pkg::*;
import riscv_system_config_pkg::*;
#(
    parameter integer NUM_SOURCES   = 32,               // Number of interrupt sources
    parameter integer NUM_TARGETS   = DEFAULT_CORE_CONFIG.num_cores * 2,  // M-mode + S-mode per core
    parameter integer MAX_PRIORITY  = 7,                // Maximum priority level
    parameter integer PLIC_BASE     = 32'h0C00_0000,
    parameter integer PRIORITY_BASE = 32'h0000_0000,
    parameter integer PENDING_BASE  = 32'h0000_1000,
    parameter integer ENABLE_BASE   = 32'h0000_2000,
    parameter integer THRESHOLD_BASE = 32'h0020_0000,
    parameter integer CLAIM_BASE    = 32'h0020_0004
) (
    // Clock and Reset
    input  logic                        clk_i,          // AI_TAG: PORT_DESC - System clock
    input  logic                        rst_ni,         // AI_TAG: PORT_DESC - Active-low asynchronous reset
    
    // Interrupt Sources
    input  logic [NUM_SOURCES-1:0]      irq_sources_i,  // AI_TAG: PORT_DESC - External interrupt sources
    
    // Memory-mapped Interface (AXI4-Lite compatible)
    input  logic                        mem_req_i,      // AI_TAG: PORT_DESC - Memory request valid
    input  logic                        mem_we_i,       // AI_TAG: PORT_DESC - Memory write enable
    input  logic [31:0]                 mem_addr_i,     // AI_TAG: PORT_DESC - Memory address
    input  logic [31:0]                 mem_wdata_i,    // AI_TAG: PORT_DESC - Memory write data
    input  logic [3:0]                  mem_be_i,       // AI_TAG: PORT_DESC - Byte enables
    output logic [31:0]                 mem_rdata_o,    // AI_TAG: PORT_DESC - Memory read data
    output logic                        mem_ready_o,    // AI_TAG: PORT_DESC - Memory transaction ready
    
    // Interrupt Outputs (per target)
    output logic [NUM_TARGETS-1:0]      irq_o           // AI_TAG: PORT_DESC - Interrupt request per target
);

    //-------------------------------------------------------------------------
    // PLIC Memory Map
    //-------------------------------------------------------------------------
    // AI_TAG: FEATURE - Standard RISC-V PLIC memory map
    // Priority[n]       : 0x0000_0000 + 4*n     (Interrupt source priority)
    // Pending[n/32]     : 0x0000_1000 + 4*(n/32) (Interrupt pending bits)
    // Enable[t][n/32]   : 0x0000_2000 + 0x80*t + 4*(n/32) (Interrupt enable per target)
    // Threshold[t]      : 0x0020_0000 + 0x1000*t (Priority threshold per target)
    // Claim/Complete[t] : 0x0020_0004 + 0x1000*t (Claim/complete per target)
    
    //-------------------------------------------------------------------------
    // Internal Registers
    //-------------------------------------------------------------------------
    // Source priorities (0 = never interrupt)
    logic [2:0] priority_r [NUM_SOURCES];
    
    // Interrupt pending bits
    logic [NUM_SOURCES-1:0] pending_r;
    
    // Interrupt enable bits per target
    logic [NUM_SOURCES-1:0] enable_r [NUM_TARGETS];
    
    // Priority threshold per target
    logic [2:0] threshold_r [NUM_TARGETS];
    
    // Claimed interrupt ID per target
    logic [7:0] claim_r [NUM_TARGETS];
    
    // Gateway - edge detection and synchronization
    logic [NUM_SOURCES-1:0] irq_sync_r, irq_sync_rr;
    logic [NUM_SOURCES-1:0] irq_edge;
    
    //-------------------------------------------------------------------------
    // Address Decoding
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Decode memory-mapped register addresses
    logic [31:0] local_addr;
    logic priority_access;
    logic pending_access;
    logic enable_access;
    logic threshold_access;
    logic claim_access;
    logic [7:0] source_idx;
    logic [4:0] target_idx;
    logic [2:0] word_idx;
    logic addr_valid;
    
    assign local_addr = mem_addr_i - PLIC_BASE;
    
    always_comb begin
        priority_access = 1'b0;
        pending_access = 1'b0;
        enable_access = 1'b0;
        threshold_access = 1'b0;
        claim_access = 1'b0;
        source_idx = '0;
        target_idx = '0;
        word_idx = '0;
        addr_valid = 1'b0;
        
        // Priority registers
        if (local_addr >= PRIORITY_BASE && local_addr < PRIORITY_BASE + 4*NUM_SOURCES) begin
            priority_access = 1'b1;
            source_idx = (local_addr - PRIORITY_BASE) >> 2;
            addr_valid = (source_idx < NUM_SOURCES);
        end
        // Pending registers
        else if (local_addr >= PENDING_BASE && local_addr < PENDING_BASE + 4*((NUM_SOURCES+31)/32)) begin
            pending_access = 1'b1;
            word_idx = (local_addr - PENDING_BASE) >> 2;
            addr_valid = 1'b1;
        end
        // Enable registers
        else if (local_addr >= ENABLE_BASE && local_addr < ENABLE_BASE + 0x80*NUM_TARGETS) begin
            enable_access = 1'b1;
            target_idx = (local_addr - ENABLE_BASE) >> 7;
            word_idx = ((local_addr - ENABLE_BASE) & 32'h7F) >> 2;
            addr_valid = (target_idx < NUM_TARGETS);
        end
        // Threshold/Claim registers
        else if (local_addr >= THRESHOLD_BASE && local_addr < THRESHOLD_BASE + 0x1000*NUM_TARGETS) begin
            target_idx = (local_addr - THRESHOLD_BASE) >> 12;
            if ((local_addr & 32'hFFF) == 0) begin
                threshold_access = 1'b1;
                addr_valid = (target_idx < NUM_TARGETS);
            end
            else if ((local_addr & 32'hFFF) == 4) begin
                claim_access = 1'b1;
                addr_valid = (target_idx < NUM_TARGETS);
            end
        end
    end
    
    //-------------------------------------------------------------------------
    // Interrupt Gateway - Edge Detection
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Synchronize and detect rising edges on interrupt sources
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            irq_sync_r  <= '0;
            irq_sync_rr <= '0;
        end else begin
            irq_sync_r  <= irq_sources_i;
            irq_sync_rr <= irq_sync_r;
        end
    end
    
    assign irq_edge = irq_sync_r & ~irq_sync_rr;
    
    //-------------------------------------------------------------------------
    // Pending Register Management
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Set pending on edge, clear on claim
    genvar i;
    generate
        for (i = 0; i < NUM_SOURCES; i++) begin : gen_pending
            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    pending_r[i] <= 1'b0;
                end else if (irq_edge[i] && priority_r[i] != 0) begin
                    // Set pending on edge if priority is non-zero
                    pending_r[i] <= 1'b1;
                end else if (mem_req_i && !mem_we_i && claim_access) begin
                    // Clear pending when claimed
                    if (claim_r[target_idx] == i+1) begin
                        pending_r[i] <= 1'b0;
                    end
                end
            end
        end
    endgenerate
    
    //-------------------------------------------------------------------------
    // Priority Registers
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Configurable priority per interrupt source
    generate
        for (i = 0; i < NUM_SOURCES; i++) begin : gen_priority
            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    priority_r[i] <= 3'h0;
                end else if (mem_req_i && mem_we_i && priority_access && source_idx == i) begin
                    priority_r[i] <= mem_wdata_i[2:0];
                end
            end
        end
    endgenerate
    
    //-------------------------------------------------------------------------
    // Enable Registers
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Per-target interrupt enable masks
    generate
        for (i = 0; i < NUM_TARGETS; i++) begin : gen_target_enable
            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    enable_r[i] <= '0;
                end else if (mem_req_i && mem_we_i && enable_access && target_idx == i && word_idx == 0) begin
                    enable_r[i] <= mem_wdata_i[NUM_SOURCES-1:0];
                end
            end
        end
    endgenerate
    
    //-------------------------------------------------------------------------
    // Threshold Registers
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Per-target priority threshold
    generate
        for (i = 0; i < NUM_TARGETS; i++) begin : gen_threshold
            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    threshold_r[i] <= 3'h0;
                end else if (mem_req_i && mem_we_i && threshold_access && target_idx == i) begin
                    threshold_r[i] <= mem_wdata_i[2:0];
                end
            end
        end
    endgenerate
    
    //-------------------------------------------------------------------------
    // Interrupt Arbitration and Claim Logic
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Find highest priority pending interrupt per target
    logic [7:0] highest_id [NUM_TARGETS];
    logic [2:0] highest_prio [NUM_TARGETS];
    
    generate
        for (i = 0; i < NUM_TARGETS; i++) begin : gen_arbitration
            always_comb begin
                highest_id[i] = 8'h0;
                highest_prio[i] = 3'h0;
                
                // Find highest priority pending and enabled interrupt
                for (int j = 0; j < NUM_SOURCES; j++) begin
                    if (pending_r[j] && enable_r[i][j] && 
                        priority_r[j] > threshold_r[i] &&
                        priority_r[j] > highest_prio[i]) begin
                        highest_id[i] = j + 1;
                        highest_prio[i] = priority_r[j];
                    end
                end
            end
            
            // Claim register - holds ID of claimed interrupt
            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    claim_r[i] <= 8'h0;
                end else if (mem_req_i && !mem_we_i && claim_access && target_idx == i) begin
                    // Claim the highest priority interrupt
                    claim_r[i] <= highest_id[i];
                end else if (mem_req_i && mem_we_i && claim_access && target_idx == i) begin
                    // Complete the interrupt (write to claim register)
                    if (mem_wdata_i[7:0] == claim_r[i]) begin
                        claim_r[i] <= 8'h0;
                    end
                end
            end
            
            // Generate interrupt output
            assign irq_o[i] = (highest_id[i] != 0);
        end
    endgenerate
    
    //-------------------------------------------------------------------------
    // Read Data Multiplexer
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Select read data based on address
    always_comb begin
        mem_rdata_o = 32'h0;
        
        if (priority_access && source_idx < NUM_SOURCES) begin
            mem_rdata_o = {29'h0, priority_r[source_idx]};
        end
        else if (pending_access && word_idx == 0) begin
            mem_rdata_o = {{32-NUM_SOURCES{1'b0}}, pending_r};
        end
        else if (enable_access && target_idx < NUM_TARGETS && word_idx == 0) begin
            mem_rdata_o = {{32-NUM_SOURCES{1'b0}}, enable_r[target_idx]};
        end
        else if (threshold_access && target_idx < NUM_TARGETS) begin
            mem_rdata_o = {29'h0, threshold_r[target_idx]};
        end
        else if (claim_access && target_idx < NUM_TARGETS) begin
            if (!mem_we_i) begin
                // Read returns highest priority ID
                mem_rdata_o = {24'h0, highest_id[target_idx]};
            end else begin
                // Write returns current claim ID
                mem_rdata_o = {24'h0, claim_r[target_idx]};
            end
        end
    end
    
    //-------------------------------------------------------------------------
    // Memory Interface Response
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Single-cycle response for all accesses
    assign mem_ready_o = mem_req_i && addr_valid;
    
    //-------------------------------------------------------------------------
    // Assertions
    //-------------------------------------------------------------------------
    // AI_TAG: ASSERTION - Valid address access
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    ValidAddress: assert property (@(posedge clk_i) disable iff (!rst_ni)
        mem_req_i |-> addr_valid);
    
    // AI_TAG: ASSERTION - Priority within range
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    PriorityRange: assert property (@(posedge clk_i) disable iff (!rst_ni)
        $onehot0(priority_r[*] > MAX_PRIORITY));
    
    // AI_TAG: ASSERTION - Claim ID validity
    // AI_TAG: ASSERTION_TYPE - Formal
    // AI_TAG: ASSERTION_SEVERITY - Error
    ClaimValid: assert property (@(posedge clk_i) disable iff (!rst_ni)
        (claim_r[*] != 0) |-> (claim_r[*] <= NUM_SOURCES));

endmodule : plic

//=============================================================================
// Dependencies: riscv_base_pkg, riscv_system_config_pkg
//
// Instantiated In:
//   - soc/riscv_soc_top.sv
//   - platform/riscv_platform.sv
//
// Performance:
//   - Critical Path: Priority arbitration logic
//   - Max Frequency: > 150MHz typical
//   - Area: Scales with NUM_SOURCES * NUM_TARGETS
//
// Verification Coverage:
//   - Code Coverage: TBD
//   - Functional Coverage: TBD
//   - Branch Coverage: TBD
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Vivado
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: plic_tb.sv
//   - Test Vectors: TBD
//
//----
// Revision History:
// Version | Date       | Author         | Description
//=============================================================================
// 1.0.0   | 2025-01-29 | DesignAI      | Initial release
//=============================================================================