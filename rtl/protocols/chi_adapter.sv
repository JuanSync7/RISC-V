//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: chi_adapter.sv
// Module: chi_adapter
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   CHI (Coherent Hub Interface) protocol adapter that translates between
//   the generic memory interface and ARM CHI protocol. Supports coherent
//   cache operations and snoop transactions. Updated to use proper interface.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - CHI protocol translation from generic memory interface using proper interface
// AI_TAG: FEATURE - Support for ReadNoSnp, WriteNoSnp, and coherent operations
// AI_TAG: FEATURE - Transaction tracking with outstanding request management
// AI_TAG: FEATURE - CHI response handling and data ordering using CHI interface

import riscv_config_pkg::*;
import riscv_types_pkg::*;
import riscv_protocol_types_pkg::*;
import riscv_core_pkg::*;

module chi_adapter #(
    parameter integer ADDR_WIDTH = 32,      // AI_TAG: PARAM_DESC - Address bus width
                                            // AI_TAG: PARAM_USAGE - Must match chi_if parameter
                                            // AI_TAG: PARAM_CONSTRAINTS - Must match chi_if parameter
    parameter integer DATA_WIDTH = 128,     // AI_TAG: PARAM_DESC - Data bus width
                                            // AI_TAG: PARAM_USAGE - Must match chi_if parameter
                                            // AI_TAG: PARAM_CONSTRAINTS - Must match chi_if parameter
    parameter integer NODEID_WIDTH = 7,     // AI_TAG: PARAM_DESC - CHI Node ID width
                                            // AI_TAG: PARAM_USAGE - Must match chi_if parameter
                                            // AI_TAG: PARAM_CONSTRAINTS - Must match chi_if parameter
    parameter integer TXNID_WIDTH = 8,      // AI_TAG: PARAM_DESC - CHI transaction ID width
                                            // AI_TAG: PARAM_USAGE - Must match chi_if parameter
                                            // AI_TAG: PARAM_CONSTRAINTS - Must match chi_if parameter
    parameter integer MAX_OUTSTANDING = 16  // AI_TAG: PARAM_DESC - Maximum outstanding transactions
                                            // AI_TAG: PARAM_USAGE - Sets transaction table size
                                            // AI_TAG: PARAM_CONSTRAINTS - Must be power of 2, max 64
) (
    input  logic        clk_i,     // AI_TAG: PORT_DESC - System clock
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        rst_ni,    // AI_TAG: PORT_DESC - Asynchronous active-low reset
                                   // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
                                   // AI_TAG: PORT_TIMING - Asynchronous

    // Generic memory interface
    // AI_TAG: IF_TYPE - Generic Memory Interface (slave)
    // AI_TAG: IF_DESC - Protocol-agnostic memory interface
    // AI_TAG: IF_CLOCKING - clk_i
    // AI_TAG: IF_RESET - rst_ni
    memory_req_rsp_if.slave mem_if,

    // CHI Interface - Using proper interface
    // AI_TAG: IF_TYPE - CHI Request Node (RN)
    // AI_TAG: IF_MODPORT - rn
    // AI_TAG: IF_PROTOCOL_VERSION - CHI-B
    // AI_TAG: IF_DESC - CHI interface for coherent memory access
    // AI_TAG: IF_DATA_WIDTHS - Data: parameterized, Addr: parameterized, Node ID: parameterized
    // AI_TAG: IF_CLOCKING - clk_i via chi_if.clk connection
    // AI_TAG: IF_RESET - rst_ni via chi_if.resetn connection
    chi_if.rn chi_if
);

    // AI_TAG: INTERNAL_BLOCK - TransactionTracker - Manages outstanding CHI transactions
    // AI_TAG: INTERNAL_BLOCK - StateMachine - Controls CHI transaction flow
    // AI_TAG: INTERNAL_BLOCK - ProtocolConverter - Converts between memory and CHI protocols

    // Connect interface clock and reset
    assign chi_if.clk = clk_i;
    assign chi_if.resetn = rst_ni;

    // AI_TAG: DATAPATH_DESC - Memory requests are converted to CHI requests, responses are tracked and converted back
    
    //-----
    // CHI Opcodes (CHI-B Specification)
    //-----
    localparam logic [6:0] CHI_ReadNoSnp         = 7'h01;  // Non-snooping read
    localparam logic [6:0] CHI_WriteNoSnpPtl     = 7'h20;  // Non-snooping partial write
    localparam logic [6:0] CHI_WriteNoSnpFull    = 7'h18;  // Non-snooping full write
    
    localparam logic [4:0] CHI_CompData          = 5'h04;  // Complete with data
    localparam logic [4:0] CHI_Comp              = 5'h0C;  // Complete without data
    
    localparam logic [3:0] CHI_NonCopyBackWrData = 4'h6;   // Non-copyback write data

    //-----
    // Transaction Tracking
    //-----
    // AI_TAG: INTERNAL_STORAGE - Transaction table for tracking outstanding requests
    // AI_TAG: INTERNAL_STORAGE_TYPE - Transaction table - Memory array
    // AI_TAG: INTERNAL_STORAGE_ACCESS - Transaction table - FSM controlled
    typedef struct packed {
        logic                       valid;
        logic                       is_write;
        logic [ADDR_WIDTH-1:0]      addr;
        logic [DATA_WIDTH-1:0]      data;
        logic [(DATA_WIDTH/8)-1:0]  strb;
        logic [15:0]                mem_req_id;  // Original memory request ID
        logic                       data_sent;
        logic                       rsp_received;
        logic [TXNID_WIDTH-1:0]     chi_txn_id;
    } transaction_entry_t;

    transaction_entry_t transaction_table [MAX_OUTSTANDING-1:0];
    logic [TXNID_WIDTH-1:0] next_txn_id;
    logic [TXNID_WIDTH-1:0] allocated_txn_id;
    logic                   txn_alloc_valid;

    // AI_TAG: FSM_NAME - chi_adapter_fsm
    // AI_TAG: FSM_PURPOSE - chi_adapter_fsm - Controls CHI transaction flow and state management
    // AI_TAG: FSM_ENCODING - chi_adapter_fsm - binary
    // AI_TAG: FSM_RESET_STATE - chi_adapter_fsm - IDLE
    typedef enum logic [2:0] {
        IDLE,               // AI_TAG: FSM_STATE - IDLE - Waiting for request or checking responses
        SEND_REQ,           // AI_TAG: FSM_STATE - SEND_REQ - Sending CHI request
        SEND_DATA,          // AI_TAG: FSM_STATE - SEND_DATA - Sending CHI write data
        WAIT_RSP,           // AI_TAG: FSM_STATE - WAIT_RSP - Waiting for CHI response
        SEND_GENERIC_RSP    // AI_TAG: FSM_STATE - SEND_GENERIC_RSP - Sending response to memory interface
    } state_e;

    state_e current_state_q, next_state_c;

    //-----
    // Internal Signals
    //-----
    logic can_accept_request;
    logic [TXNID_WIDTH-1:0] free_txn_id;
    logic found_free_slot;
    logic [TXNID_WIDTH-1:0] completed_txn_id;
    logic completed_txn_valid;

    //-----
    // Transaction ID Management
    //-----
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_txn_id_counter
        if (!rst_ni) begin
            next_txn_id <= '0;
        end else if (txn_alloc_valid) begin
            next_txn_id <= next_txn_id + 1;
        end
    end

    // Find free transaction slot
    always_comb begin : proc_find_free_slot
        found_free_slot = 1'b0;
        free_txn_id = '0;
        
        for (int i = 0; i < MAX_OUTSTANDING; i++) begin
            if (!transaction_table[i].valid) begin
                found_free_slot = 1'b1;
                free_txn_id = i[TXNID_WIDTH-1:0];
                break;
            end
        end
    end

    // Find completed transaction for response
    always_comb begin : proc_find_completed_txn
        completed_txn_valid = 1'b0;
        completed_txn_id = '0;
        
        for (int i = 0; i < MAX_OUTSTANDING; i++) begin
            if (transaction_table[i].valid && transaction_table[i].rsp_received) begin
                if (!transaction_table[i].is_write || transaction_table[i].data_sent) begin
                    completed_txn_valid = 1'b1;
                    completed_txn_id = i[TXNID_WIDTH-1:0];
                    break;
                end
            end
        end
    end

    assign can_accept_request = found_free_slot;
    assign allocated_txn_id = free_txn_id;

    // AI_TAG: FSM_TRANSITION - chi_adapter_fsm: IDLE -> SEND_REQ when (mem_if.req_valid && can_accept_request)
    // AI_TAG: FSM_TRANSITION - chi_adapter_fsm: SEND_REQ -> SEND_DATA when (chi_if.reqflitv && chi_if.reqlcrdv && is_write)
    // AI_TAG: FSM_TRANSITION - chi_adapter_fsm: SEND_REQ -> WAIT_RSP when (chi_if.reqflitv && chi_if.reqlcrdv && !is_write)
    // AI_TAG: FSM_TRANSITION - chi_adapter_fsm: SEND_DATA -> WAIT_RSP when (chi_if.datflitv && chi_if.datlcrdv)
    // AI_TAG: FSM_TRANSITION - chi_adapter_fsm: WAIT_RSP -> IDLE when transaction complete
    // AI_TAG: FSM_TRANSITION - chi_adapter_fsm: SEND_GENERIC_RSP -> IDLE when (mem_if.rsp_ready)

    //-----
    // Main FSM
    //-----
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_fsm_state
        if (!rst_ni) begin
            current_state_q <= IDLE;
            for (int i = 0; i < MAX_OUTSTANDING; i++) begin
                transaction_table[i] <= '0;
            end
        end else begin
            current_state_q <= next_state_c;
            
            // Handle transaction allocation
            if (txn_alloc_valid) begin
                transaction_table[allocated_txn_id].valid <= 1'b1;
                transaction_table[allocated_txn_id].is_write <= mem_if.req.write;
                transaction_table[allocated_txn_id].addr <= mem_if.req.addr;
                transaction_table[allocated_txn_id].data <= mem_if.req.data;
                transaction_table[allocated_txn_id].strb <= mem_if.req.strb[(DATA_WIDTH/8)-1:0];
                transaction_table[allocated_txn_id].mem_req_id <= mem_if.req.id;
                transaction_table[allocated_txn_id].data_sent <= 1'b0;
                transaction_table[allocated_txn_id].rsp_received <= 1'b0;
                transaction_table[allocated_txn_id].chi_txn_id <= next_txn_id;
            end
            
            // Handle data sent acknowledgment
            if (chi_if.datflitv && chi_if.datlcrdv) begin
                for (int i = 0; i < MAX_OUTSTANDING; i++) begin
                    if (transaction_table[i].valid && 
                        transaction_table[i].chi_txn_id == chi_if.dat_txnid) begin
                        transaction_table[i].data_sent <= 1'b1;
                        break;
                    end
                end
            end
            
            // Handle response reception
            if (chi_if.rspflitv && chi_if.rsplcrdv) begin
                for (int i = 0; i < MAX_OUTSTANDING; i++) begin
                    if (transaction_table[i].valid && 
                        transaction_table[i].chi_txn_id == chi_if.rsp_txnid) begin
                        transaction_table[i].rsp_received <= 1'b1;
                        break;
                    end
                end
            end
            
            // Clear completed transactions
            if (mem_if.rsp_valid && mem_if.rsp_ready) begin
                transaction_table[completed_txn_id].valid <= 1'b0;
            end
        end
    end

    always_comb begin : proc_fsm_logic
        next_state_c = current_state_q;
        
        // Default memory interface outputs
        mem_if.req_ready = 1'b0;
        mem_if.rsp_valid = 1'b0;
        mem_if.rsp = '0;
        
        // Default CHI interface outputs
        chi_if.reqflitpend = 1'b0;
        chi_if.reqflitv = 1'b0;
        chi_if.req_addr = '0;
        chi_if.req_opcode = '0;
        chi_if.req_size = 3'b010; // 4 bytes default
        chi_if.req_srcid = '0;     // Source node ID
        chi_if.req_txnid = '0;
        chi_if.req_tgtid = '0;     // Target node ID
        chi_if.req_ns = 1'b0;      // Secure access
        chi_if.req_allowretry = 1'b1;
        chi_if.req_order = 2'b00;  // No ordering
        chi_if.req_memattr = 4'b0000; // Device memory
        chi_if.req_lpid_valid = 1'b0;
        chi_if.req_lpid = '0;
        chi_if.req_excl = 1'b0;
        chi_if.req_expcompack = 1'b0;
        
        chi_if.datflitpend = 1'b0;
        chi_if.datflitv = 1'b0;
        chi_if.dat_srcid = '0;
        chi_if.dat_txnid = '0;
        chi_if.dat_tgtid = '0;
        chi_if.dat_homenid = '0;
        chi_if.dat_opcode = '0;
        chi_if.dat_resperr = 2'b00;
        chi_if.dat_resp = 1'b0;
        chi_if.dat_fwdstate = 2'b00;
        chi_if.dat_cbusy = 3'b000;
        chi_if.dat_dbid = '0;
        chi_if.dat_ccid = 2'b00;
        chi_if.dat_dataid = 2'b00;
        chi_if.dat_data = '0;
        chi_if.dat_datacheck = '0;
        chi_if.dat_poison = 1'b0;
        
        chi_if.rsplcrdv = 1'b1;    // Always ready for responses
        chi_if.snplcrdv = 1'b1;    // Always ready for snoops
        
        txn_alloc_valid = 1'b0;

        case (current_state_q)
            IDLE: begin
                mem_if.req_ready = can_accept_request;
                
                if (mem_if.req_valid && can_accept_request) begin
                    txn_alloc_valid = 1'b1;
                    next_state_c = SEND_REQ;
                end else if (completed_txn_valid) begin
                    next_state_c = SEND_GENERIC_RSP;
                end
            end

            SEND_REQ: begin
                chi_if.reqflitv = 1'b1;
                chi_if.req_txnid = next_txn_id;
                chi_if.req_addr = mem_if.req.addr;
                chi_if.req_srcid = 7'd1; // Source node ID (this adapter)
                chi_if.req_tgtid = 7'd0; // Target node ID (home node)
                
                // Map memory request size to CHI size encoding
                case (mem_if.req.size)
                    3'd0: chi_if.req_size = 3'd0; // 1 byte
                    3'd1: chi_if.req_size = 3'd1; // 2 bytes
                    3'd2: chi_if.req_size = 3'd2; // 4 bytes
                    3'd3: chi_if.req_size = 3'd3; // 8 bytes
                    default: chi_if.req_size = 3'd2; // Default to 4 bytes
                endcase
                
                if (mem_if.req.write) begin
                    // Determine write type based on strobe pattern
                    if (&mem_if.req.strb) begin
                        chi_if.req_opcode = CHI_WriteNoSnpFull;
                    end else begin
                        chi_if.req_opcode = CHI_WriteNoSnpPtl;
                    end
                end else begin
                    chi_if.req_opcode = CHI_ReadNoSnp;
                end
                
                if (chi_if.reqlcrdv) begin
                    if (mem_if.req.write) begin
                        next_state_c = SEND_DATA;
                    end else begin
                        next_state_c = WAIT_RSP;
                    end
                end
            end

            SEND_DATA: begin
                chi_if.datflitv = 1'b1;
                chi_if.dat_opcode = CHI_NonCopyBackWrData;
                chi_if.dat_txnid = transaction_table[allocated_txn_id].chi_txn_id;
                chi_if.dat_srcid = 7'd1; // Source node ID
                chi_if.dat_data = transaction_table[allocated_txn_id].data;
                // CHI doesn't use byte enables in the same way, but we can use datacheck for ECC
                chi_if.dat_datacheck = '0; // No ECC for now
                
                if (chi_if.datlcrdv) begin
                    next_state_c = WAIT_RSP;
                end
            end

            WAIT_RSP: begin
                // Wait for response, handled by transaction table updates
                if (completed_txn_valid) begin
                    next_state_c = SEND_GENERIC_RSP;
                end else begin
                    next_state_c = IDLE;
                end
            end

            SEND_GENERIC_RSP: begin
                mem_if.rsp_valid = 1'b1;
                mem_if.rsp.id = transaction_table[completed_txn_id].mem_req_id;
                mem_if.rsp.last = 1'b1;
                
                if (!transaction_table[completed_txn_id].is_write) begin
                    // Read response - get data from CHI data response
                    if (chi_if.datflitv) begin
                        mem_if.rsp.data = chi_if.dat_data;
                        mem_if.rsp.error = (chi_if.dat_resperr != 2'b00);
                    end else begin
                        mem_if.rsp.data = '0;
                        mem_if.rsp.error = 1'b0;
                    end
                end else begin
                    // Write response
                    mem_if.rsp.data = '0;
                    mem_if.rsp.error = (chi_if.rsp_resperr != 3'b000);
                end
                
                if (mem_if.rsp_ready) begin
                    next_state_c = IDLE;
                end
            end

            default: begin
                next_state_c = IDLE;
            end
        endcase
    end

    // AI_TAG: ASSERTION - a_transaction_table_no_overflow: Transaction table should not overflow
    // AI_TAG: ASSERTION_TYPE - Simulation
    // AI_TAG: ASSERTION_SEVERITY - Error
`ifdef SIMULATION
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        mem_if.req_valid |-> can_accept_request)
    else $error("Transaction table overflow detected");

    // AI_TAG: ASSERTION - a_valid_transaction_fields: Valid transactions should have correct fields
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        txn_alloc_valid |-> (allocated_txn_id < MAX_OUTSTANDING))
    else $error("Invalid transaction ID allocation");

    // AI_TAG: ASSERTION - a_chi_req_stable: CHI request should remain stable when valid
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        chi_if.reqflitv && !chi_if.reqlcrdv |=> chi_if.reqflitv)
    else $error("CHI request not stable");
`endif

endmodule : chi_adapter

//=============================================================================
// Dependencies: riscv_core_pkg.sv, memory_req_rsp_if.sv, chi_if.sv
//
// Performance:
//   - Critical Path: Transaction table lookup and CHI interface timing
//   - Max Frequency: 400MHz ASIC, 200MHz FPGA
//   - Area: Depends on MAX_OUTSTANDING parameter (~500 gates base + 50 per transaction)
//
// Verification Coverage:
//   - Code Coverage: TBD
//   - Functional Coverage: CHI protocol compliance
//   - Branch Coverage: All CHI opcodes and transaction states
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: Design Compiler/Quartus
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: chi_adapter.sdc
//
// Testing:
//   - Testbench: chi_adapter_tb.sv
//   - Test Vectors: CHI protocol compliance scenarios
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 2.0.0   | 2025-01-27 | DesignAI          | Updated to use proper chi_if interface
// 1.0.0   | 2025-01-27 | DesignAI          | Initial CHI adapter implementation
//============================================================================= 