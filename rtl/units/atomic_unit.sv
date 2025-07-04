//=============================================================================
// Company: Sondrel Ltd
// Project Name: RISC-V RV32IM Core
//
// File: atomic_unit.sv
//
// ----- Fields for Automated Documentation -----
// MODULE_NAME: atomic_unit
// AUTHOR: DesignAI (designai@sondrel.com)
// VERSION: 1.0.0
// DATE: 2025-01-29
// DESCRIPTION: Atomic operations unit for RV32A extension (Load-Reserved/Store-Conditional and AMO).
// PRIMARY_PURPOSE: Implement atomic memory operations for multi-core synchronization.
// ROLE_IN_SYSTEM: Provides thread-safe memory operations for multi-core systems.
// PROBLEM_SOLVED: Enables lock-free programming and atomic data structures.
// MODULE_TYPE: RTL
// TARGET_TECHNOLOGY_PREF: ASIC/FPGA
// RELATED_SPECIFICATION: RISC-V ISA Specification RV32A Extension
//
// ----- Status and Tracking -----
// VERIFICATION_STATUS: Not Verified
// QUALITY_STATUS: Draft
//
//=============================================================================
//
`timescale 1ns/1ps
`default_nettype none

module atomic_unit
import riscv_base_pkg::*;
import riscv_system_config_pkg::*;
#(
    parameter integer XLEN = 32,
    parameter integer RESERVATION_TIMEOUT = 1000  // Cycles before reservation expires
) (
    // Clock and Reset
    input  logic                clk_i,              // AI_TAG: PORT_DESC - System clock
    input  logic                rst_ni,             // AI_TAG: PORT_DESC - Active-low asynchronous reset
    
    // Control Interface
    input  logic                atomic_req_i,       // AI_TAG: PORT_DESC - Atomic operation request
    input  logic [4:0]          funct5_i,           // AI_TAG: PORT_DESC - Function code (atomic operation type)
    input  logic [2:0]          funct3_i,           // AI_TAG: PORT_DESC - Width field (always 010 for 32-bit)
    input  logic                aq_i,               // AI_TAG: PORT_DESC - Acquire ordering constraint
    input  logic                rl_i,               // AI_TAG: PORT_DESC - Release ordering constraint
    input  logic [XLEN-1:0]     rs1_data_i,        // AI_TAG: PORT_DESC - Address operand
    input  logic [XLEN-1:0]     rs2_data_i,        // AI_TAG: PORT_DESC - Source operand
    output logic [XLEN-1:0]     result_o,           // AI_TAG: PORT_DESC - Result data
    output logic                atomic_done_o,      // AI_TAG: PORT_DESC - Operation complete
    
    // Memory Interface
    output logic                mem_req_o,          // AI_TAG: PORT_DESC - Memory request
    output logic                mem_we_o,           // AI_TAG: PORT_DESC - Memory write enable
    output logic [XLEN-1:0]     mem_addr_o,         // AI_TAG: PORT_DESC - Memory address
    output logic [XLEN-1:0]     mem_wdata_o,        // AI_TAG: PORT_DESC - Memory write data
    output logic [3:0]          mem_be_o,           // AI_TAG: PORT_DESC - Memory byte enable
    input  logic [XLEN-1:0]     mem_rdata_i,        // AI_TAG: PORT_DESC - Memory read data
    input  logic                mem_ready_i,        // AI_TAG: PORT_DESC - Memory operation ready
    
    // Reservation Monitoring (for other cores)
    input  logic [7:0]          core_id_i,          // AI_TAG: PORT_DESC - Core ID for reservation tracking
    output logic                reservation_valid_o, // AI_TAG: PORT_DESC - Reservation active
    output logic [XLEN-1:0]     reservation_addr_o, // AI_TAG: PORT_DESC - Reserved address
    input  logic                global_monitor_clear_i, // AI_TAG: PORT_DESC - Global reservation clear
    
    // Cache Coherency Interface
    output logic                invalidate_req_o,   // AI_TAG: PORT_DESC - Cache invalidation request
    output logic [XLEN-1:0]     invalidate_addr_o,  // AI_TAG: PORT_DESC - Address to invalidate
    input  logic                invalidate_ack_i    // AI_TAG: PORT_DESC - Invalidation acknowledge
);

    //-------------------------------------------------------------------------
    // RV32A Instruction Encoding
    //-------------------------------------------------------------------------
    // AI_TAG: FEATURE - Implements RV32A atomic operations per RISC-V spec
    
    // Atomic operation function codes
    typedef enum logic [4:0] {
        ATOMIC_LR      = 5'b00010,  // Load-Reserved
        ATOMIC_SC      = 5'b00011,  // Store-Conditional
        ATOMIC_AMOSWAP = 5'b00001,  // Atomic Swap
        ATOMIC_AMOADD  = 5'b00000,  // Atomic Add
        ATOMIC_AMOXOR  = 5'b00100,  // Atomic XOR
        ATOMIC_AMOAND  = 5'b01100,  // Atomic AND
        ATOMIC_AMOOR   = 5'b01000,  // Atomic OR
        ATOMIC_AMOMIN  = 5'b10000,  // Atomic Minimum (signed)
        ATOMIC_AMOMAX  = 5'b10100,  // Atomic Maximum (signed)
        ATOMIC_AMOMINU = 5'b11000,  // Atomic Minimum (unsigned)
        ATOMIC_AMOMAXU = 5'b11100   // Atomic Maximum (unsigned)
    } atomic_op_e;
    
    //-------------------------------------------------------------------------
    // FSM States
    //-------------------------------------------------------------------------
    // AI_TAG: FSM_NAME - atomic_fsm
    // AI_TAG: FSM_PURPOSE - atomic_fsm - Controls atomic operation sequencing
    // AI_TAG: FSM_ENCODING - atomic_fsm - one-hot
    // AI_TAG: FSM_RESET_STATE - atomic_fsm - S_IDLE
    typedef enum logic [3:0] {
        S_IDLE,
        S_LR_READ,          // Load-Reserved: Read memory
        S_LR_COMPLETE,      // Load-Reserved: Complete operation
        S_SC_CHECK,         // Store-Conditional: Check reservation
        S_SC_WRITE,         // Store-Conditional: Write memory
        S_SC_COMPLETE,      // Store-Conditional: Complete operation
        S_AMO_READ,         // AMO: Read current value
        S_AMO_COMPUTE,      // AMO: Compute new value
        S_AMO_WRITE,        // AMO: Write new value
        S_AMO_COMPLETE,     // AMO: Complete operation
        S_INVALIDATE        // Cache invalidation
    } atomic_state_e;
    
    atomic_state_e state_r, state_ns;
    
    //-------------------------------------------------------------------------
    // Reservation Table
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Load-Reserved/Store-Conditional reservation tracking
    logic                reservation_valid_r;
    logic [XLEN-1:0]     reservation_addr_r;
    logic [7:0]          reservation_core_r;
    logic [15:0]         reservation_timeout_r;
    logic                reservation_match;
    
    assign reservation_match = reservation_valid_r && 
                              (reservation_addr_r[XLEN-1:2] == rs1_data_i[XLEN-1:2]) &&
                              (reservation_core_r == core_id_i);
    
    // Reservation outputs
    assign reservation_valid_o = reservation_valid_r;
    assign reservation_addr_o = reservation_addr_r;
    
    //-------------------------------------------------------------------------
    // Internal Registers
    //-------------------------------------------------------------------------
    logic [XLEN-1:0]     saved_mem_data;    // Original memory value for AMO
    logic [XLEN-1:0]     computed_result;   // Computed result for AMO
    logic [XLEN-1:0]     operation_addr;    // Current operation address
    atomic_op_e          current_op;        // Current atomic operation
    
    //-------------------------------------------------------------------------
    // AMO Computation Logic
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Compute AMO operation results
    always_comb begin
        computed_result = saved_mem_data;  // Default: no change
        
        case (current_op)
            ATOMIC_AMOSWAP: computed_result = rs2_data_i;
            ATOMIC_AMOADD:  computed_result = saved_mem_data + rs2_data_i;
            ATOMIC_AMOXOR:  computed_result = saved_mem_data ^ rs2_data_i;
            ATOMIC_AMOAND:  computed_result = saved_mem_data & rs2_data_i;
            ATOMIC_AMOOR:   computed_result = saved_mem_data | rs2_data_i;
            ATOMIC_AMOMIN:  computed_result = ($signed(saved_mem_data) < $signed(rs2_data_i)) ? 
                                             saved_mem_data : rs2_data_i;
            ATOMIC_AMOMAX:  computed_result = ($signed(saved_mem_data) > $signed(rs2_data_i)) ? 
                                             saved_mem_data : rs2_data_i;
            ATOMIC_AMOMINU: computed_result = (saved_mem_data < rs2_data_i) ? 
                                             saved_mem_data : rs2_data_i;
            ATOMIC_AMOMAXU: computed_result = (saved_mem_data > rs2_data_i) ? 
                                             saved_mem_data : rs2_data_i;
            default:        computed_result = saved_mem_data;
        endcase
    end
    
    //-------------------------------------------------------------------------
    // FSM Next State Logic
    //-------------------------------------------------------------------------
    // AI_TAG: FSM_TRANSITION - atomic_fsm: S_IDLE -> S_LR_READ when (atomic_req_i && funct5_i == ATOMIC_LR)
    // AI_TAG: FSM_TRANSITION - atomic_fsm: S_IDLE -> S_SC_CHECK when (atomic_req_i && funct5_i == ATOMIC_SC)
    // AI_TAG: FSM_TRANSITION - atomic_fsm: S_IDLE -> S_AMO_READ when (atomic_req_i && funct5_i != ATOMIC_LR/SC)
    always_comb begin
        state_ns = state_r;
        
        case (state_r)
            S_IDLE: begin
                if (atomic_req_i) begin
                    case (atomic_op_e'(funct5_i))
                        ATOMIC_LR: state_ns = S_LR_READ;
                        ATOMIC_SC: state_ns = S_SC_CHECK;
                        default:   state_ns = S_AMO_READ;  // All other AMO operations
                    endcase
                end
            end
            
            S_LR_READ: begin
                if (mem_ready_i) begin
                    state_ns = S_LR_COMPLETE;
                end
            end
            
            S_LR_COMPLETE: begin
                state_ns = S_IDLE;
            end
            
            S_SC_CHECK: begin
                if (reservation_match) begin
                    state_ns = S_SC_WRITE;
                end else begin
                    state_ns = S_SC_COMPLETE;
                end
            end
            
            S_SC_WRITE: begin
                if (mem_ready_i) begin
                    state_ns = S_INVALIDATE;
                end
            end
            
            S_AMO_READ: begin
                if (mem_ready_i) begin
                    state_ns = S_AMO_COMPUTE;
                end
            end
            
            S_AMO_COMPUTE: begin
                state_ns = S_AMO_WRITE;
            end
            
            S_AMO_WRITE: begin
                if (mem_ready_i) begin
                    state_ns = S_INVALIDATE;
                end
            end
            
            S_INVALIDATE: begin
                if (invalidate_ack_i) begin
                    state_ns = S_AMO_COMPLETE;
                end
            end
            
            S_AMO_COMPLETE,
            S_SC_COMPLETE: begin
                state_ns = S_IDLE;
            end
            
            default: state_ns = S_IDLE;
        endcase
    end
    
    //-------------------------------------------------------------------------
    // State Register and Operation Tracking
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state_r <= S_IDLE;
            saved_mem_data <= '0;
            operation_addr <= '0;
            current_op <= ATOMIC_LR;
        end else begin
            state_r <= state_ns;
            
            // Latch operation details when starting
            if (state_r == S_IDLE && atomic_req_i) begin
                operation_addr <= rs1_data_i;
                current_op <= atomic_op_e'(funct5_i);
            end
            
            // Save memory data on read
            if ((state_r == S_LR_READ || state_r == S_AMO_READ) && mem_ready_i) begin
                saved_mem_data <= mem_rdata_i;
            end
        end
    end
    
    //-------------------------------------------------------------------------
    // Reservation Management
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            reservation_valid_r <= 1'b0;
            reservation_addr_r <= '0;
            reservation_core_r <= '0;
            reservation_timeout_r <= '0;
        end else begin
            // Clear reservation on timeout or global clear
            if (reservation_timeout_r == 0 || global_monitor_clear_i) begin
                reservation_valid_r <= 1'b0;
            end
            
            // Set reservation on LR
            if (state_r == S_LR_COMPLETE) begin
                reservation_valid_r <= 1'b1;
                reservation_addr_r <= operation_addr;
                reservation_core_r <= core_id_i;
                reservation_timeout_r <= RESERVATION_TIMEOUT;
            end
            
            // Clear reservation on successful SC
            if (state_r == S_SC_WRITE && mem_ready_i) begin
                reservation_valid_r <= 1'b0;
            end
            
            // Decrement timeout
            if (reservation_valid_r && reservation_timeout_r > 0) begin
                reservation_timeout_r <= reservation_timeout_r - 1'b1;
            end
        end
    end
    
    //-------------------------------------------------------------------------
    // Memory Interface
    //-------------------------------------------------------------------------
    // AI_TAG: FSM_OUTPUT_ACTIONS - atomic_fsm - S_LR_READ,S_AMO_READ - Assert mem_req_o, clear mem_we_o
    // AI_TAG: FSM_OUTPUT_ACTIONS - atomic_fsm - S_SC_WRITE,S_AMO_WRITE - Assert mem_req_o, mem_we_o
    assign mem_req_o = (state_r == S_LR_READ) || (state_r == S_AMO_READ) ||
                       (state_r == S_SC_WRITE) || (state_r == S_AMO_WRITE);
    
    assign mem_we_o = (state_r == S_SC_WRITE) || (state_r == S_AMO_WRITE);
    
    assign mem_addr_o = operation_addr;
    
    assign mem_wdata_o = (state_r == S_SC_WRITE) ? rs2_data_i : computed_result;
    
    assign mem_be_o = 4'b1111;  // Always 32-bit operations for RV32A
    
    //-------------------------------------------------------------------------
    // Cache Coherency Interface
    //-------------------------------------------------------------------------
    assign invalidate_req_o = (state_r == S_INVALIDATE);
    assign invalidate_addr_o = operation_addr;
    
    //-------------------------------------------------------------------------
    // Result Generation
    //-------------------------------------------------------------------------
    // AI_TAG: INTERNAL_LOGIC - Generate appropriate result based on operation
    always_comb begin
        result_o = '0;
        
        case (state_r)
            S_LR_COMPLETE: begin
                result_o = saved_mem_data;  // Return loaded value
            end
            S_SC_COMPLETE: begin
                result_o = reservation_match ? 32'h0 : 32'h1;  // 0=success, 1=failure
            end
            S_AMO_COMPLETE: begin
                result_o = saved_mem_data;  // Return original value
            end
            default: result_o = '0;
        endcase
    end
    
    //-------------------------------------------------------------------------
    // Operation Complete Signal
    //-------------------------------------------------------------------------
    assign atomic_done_o = (state_r == S_LR_COMPLETE) || 
                          (state_r == S_SC_COMPLETE) || 
                          (state_r == S_AMO_COMPLETE);
    
    //-------------------------------------------------------------------------
    // Assertions
    //-------------------------------------------------------------------------
    // AI_TAG: ASSERTION - Only word-aligned addresses for atomic operations
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    WordAligned: assert property (@(posedge clk_i) disable iff (!rst_ni)
        atomic_req_i |-> (rs1_data_i[1:0] == 2'b00));
    
    // AI_TAG: ASSERTION - Valid function code
    // AI_TAG: ASSERTION_TYPE - Both
    // AI_TAG: ASSERTION_SEVERITY - Error
    ValidFunct5: assert property (@(posedge clk_i) disable iff (!rst_ni)
        atomic_req_i |-> (funct5_i inside {5'b00000, 5'b00001, 5'b00010, 5'b00011,
                                           5'b00100, 5'b01000, 5'b01100, 5'b10000,
                                           5'b10100, 5'b11000, 5'b11100}));
    
    // AI_TAG: ASSERTION - Reservation timeout bounds
    // AI_TAG: ASSERTION_TYPE - Formal
    // AI_TAG: ASSERTION_SEVERITY - Error
    ReservationTimeout: assert property (@(posedge clk_i) disable iff (!rst_ni)
        reservation_valid_r |-> (reservation_timeout_r <= RESERVATION_TIMEOUT));

endmodule : atomic_unit

//=============================================================================
// Dependencies: riscv_base_pkg, riscv_system_config_pkg
//
// Instantiated In:
//   - core/execute_stage.sv
//
// Performance:
//   - Critical Path: AMO computation logic
//   - Max Frequency: Limited by memory access latency
//   - Area: Moderate - state machine and reservation table
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
//   - Testbench: atomic_unit_tb.sv
//   - Test Vectors: Multi-core synchronization tests
//
//----
// Revision History:
// Version | Date       | Author         | Description
//=============================================================================
// 1.0.0   | 2025-01-29 | DesignAI      | Initial release
//=============================================================================