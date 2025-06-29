//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: riscv_inter_core_types_pkg.sv
// Package: riscv_inter_core_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Package containing inter-core communication types, interfaces, and
//   data structures for multi-core RISC-V system implementation.
//   Includes message passing, synchronization, and cache coherency types.
//=============================================================================

`timescale 1ns/1ps

// AI_TAG: PACKAGE - Inter-core communication and synchronization types
// AI_TAG: FEATURE - Message passing interface definitions
// AI_TAG: FEATURE - Atomic operation and synchronization primitives
// AI_TAG: FEATURE - Cache coherency message types
// AI_TAG: FEATURE - Inter-core interrupt and notification system

package riscv_inter_core_types_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    //-----
    // Inter-Core Message Types
    //-----
    
    // AI_TAG: TYPE_DEF - Inter-core message opcodes
    typedef enum logic [3:0] {
        IC_MSG_IDLE       = 4'h0,  // No message
        IC_MSG_INTERRUPT  = 4'h1,  // Inter-processor interrupt
        IC_MSG_CACHE_INV  = 4'h2,  // Cache invalidation request
        IC_MSG_CACHE_FLUSH= 4'h3,  // Cache flush request
        IC_MSG_ATOMIC_REQ = 4'h4,  // Atomic operation request
        IC_MSG_ATOMIC_RSP = 4'h5,  // Atomic operation response
        IC_MSG_SYNC_REQ   = 4'h6,  // Synchronization request
        IC_MSG_SYNC_ACK   = 4'h7,  // Synchronization acknowledgment
        IC_MSG_DEBUG      = 4'h8,  // Debug message
        IC_MSG_PERF       = 4'h9,  // Performance monitoring
        IC_MSG_CUSTOM     = 4'hF   // Custom message type
    } inter_core_msg_opcode_e;

    // AI_TAG: TYPE_DEF - Inter-core message structure
    typedef struct packed {
        logic                        valid;        // Message valid
        inter_core_msg_opcode_e      opcode;       // Message type
        logic [HART_ID_WIDTH-1:0]    src_hart;     // Source hart ID
        logic [HART_ID_WIDTH-1:0]    dst_hart;     // Destination hart ID
        logic [ADDR_WIDTH-1:0]       addr;         // Associated address
        logic [XLEN-1:0]             data;         // Message data
        logic [7:0]                  aux;          // Auxiliary data
    } inter_core_msg_t;

    //-----
    // Atomic Operation Types
    //-----
    
    // AI_TAG: TYPE_DEF - Atomic operation types
    typedef enum logic [3:0] {
        ATOMIC_ADD      = 4'h0,  // Atomic add
        ATOMIC_AND      = 4'h1,  // Atomic AND
        ATOMIC_OR       = 4'h2,  // Atomic OR  
        ATOMIC_XOR      = 4'h3,  // Atomic XOR
        ATOMIC_MIN      = 4'h4,  // Atomic minimum
        ATOMIC_MAX      = 4'h5,  // Atomic maximum
        ATOMIC_MINU     = 4'h6,  // Atomic minimum unsigned
        ATOMIC_MAXU     = 4'h7,  // Atomic maximum unsigned
        ATOMIC_SWAP     = 4'h8,  // Atomic swap
        ATOMIC_CAS      = 4'h9,  // Compare and swap
        ATOMIC_LR       = 4'hA,  // Load reserved
        ATOMIC_SC       = 4'hB   // Store conditional
    } atomic_op_e;

    // AI_TAG: TYPE_DEF - Atomic operation request
    typedef struct packed {
        logic                    valid;        // Request valid
        atomic_op_e              op;           // Atomic operation
        logic [ADDR_WIDTH-1:0]   addr;         // Target address
        logic [XLEN-1:0]         data;         // Operation data
        logic [XLEN-1:0]         compare_data; // Compare data (for CAS)
        logic [HART_ID_WIDTH-1:0] hart_id;     // Requesting hart
        logic [7:0]              tag;          // Transaction tag
    } atomic_req_t;

    // AI_TAG: TYPE_DEF - Atomic operation response
    typedef struct packed {
        logic                    valid;        // Response valid
        logic                    success;      // Operation success
        logic [XLEN-1:0]         old_data;     // Previous value
        logic [XLEN-1:0]         new_data;     // New value (for verification)
        logic [7:0]              tag;          // Transaction tag
        logic                    error;        // Error flag
    } atomic_rsp_t;

    //-----
    // Cache Coherency Message Types
    //-----
    
    // AI_TAG: TYPE_DEF - Cache coherency operations
    typedef enum logic [3:0] {
        COHERENCY_INV_LINE     = 4'h0,  // Invalidate cache line
        COHERENCY_FLUSH_LINE   = 4'h1,  // Flush cache line
        COHERENCY_INV_ALL      = 4'h2,  // Invalidate all
        COHERENCY_FLUSH_ALL    = 4'h3,  // Flush all
        COHERENCY_PROBE        = 4'h4,  // Probe cache state
        COHERENCY_SHARE        = 4'h5,  // Share cache line
        COHERENCY_EXCLUSIVE    = 4'h6,  // Request exclusive access
        COHERENCY_WRITEBACK    = 4'h7   // Writeback notification
    } coherency_op_e;

    // AI_TAG: TYPE_DEF - Cache coherency message
    typedef struct packed {
        logic                    valid;        // Message valid
        coherency_op_e           op;           // Coherency operation
        logic [ADDR_WIDTH-1:0]   addr;         // Cache line address
        logic [CACHE_LINE_WIDTH-1:0] data;     // Cache line data
        logic [HART_ID_WIDTH-1:0] requestor;   // Requesting hart
        logic [1:0]              state;        // MESI state
        logic                    response_req; // Response required
    } coherency_msg_t;

    //-----
    // Synchronization Primitives
    //-----
    
    // AI_TAG: TYPE_DEF - Synchronization primitive types
    typedef enum logic [2:0] {
        SYNC_BARRIER     = 3'h0,  // Barrier synchronization
        SYNC_MUTEX       = 3'h1,  // Mutex lock/unlock
        SYNC_SEMAPHORE   = 3'h2,  // Semaphore operation
        SYNC_CONDITION   = 3'h3,  // Condition variable
        SYNC_EVENT       = 3'h4,  // Event signaling
        SYNC_FENCE       = 3'h5   // Memory fence
    } sync_op_e;

    // AI_TAG: TYPE_DEF - Synchronization request
    typedef struct packed {
        logic                    valid;        // Request valid
        sync_op_e                op;           // Sync operation
        logic [ADDR_WIDTH-1:0]   sync_addr;    // Sync object address
        logic [XLEN-1:0]         value;        // Operation value
        logic [HART_ID_WIDTH-1:0] hart_id;     // Requesting hart
        logic                    blocking;     // Blocking operation
        logic [15:0]             timeout;      // Timeout value
    } sync_req_t;

    // AI_TAG: TYPE_DEF - Synchronization response
    typedef struct packed {
        logic                    valid;        // Response valid
        logic                    success;      // Operation success
        logic                    timeout;      // Operation timed out
        logic [XLEN-1:0]         result;       // Operation result
        logic                    error;        // Error flag
    } sync_rsp_t;

    //-----
    // Performance Monitoring Types
    //-----
    
    // AI_TAG: TYPE_DEF - Inter-core performance counters
    typedef struct packed {
        logic [31:0]             messages_sent;       // Messages sent
        logic [31:0]             messages_received;   // Messages received
        logic [31:0]             atomic_ops;          // Atomic operations
        logic [31:0]             cache_coherency_ops; // Coherency operations
        logic [31:0]             sync_ops;            // Sync operations
        logic [31:0]             network_stalls;      // Network stalls
        logic [31:0]             avg_latency;         // Average message latency
    } inter_core_perf_t;

    //-----
    // Network Topology Types
    //-----
    
    // AI_TAG: TYPE_DEF - Network topology configuration
    typedef enum logic [1:0] {
        NETWORK_RING    = 2'h0,  // Ring topology
        NETWORK_MESH    = 2'h1,  // 2D mesh topology
        NETWORK_TORUS   = 2'h2,  // Torus topology
        NETWORK_XBAR    = 2'h3   // Crossbar topology
    } network_topology_e;

    // AI_TAG: TYPE_DEF - Routing information
    typedef struct packed {
        logic [HART_ID_WIDTH-1:0] next_hop;    // Next hop hart ID
        logic [3:0]              distance;     // Distance to destination
        logic                    valid_route;  // Route is valid
    } routing_info_t;

    //-----
    // Debug and Monitoring Types
    //-----
    
    // AI_TAG: TYPE_DEF - Inter-core debug message
    typedef struct packed {
        logic [3:0]              debug_op;     // Debug operation
        logic [HART_ID_WIDTH-1:0] target_hart; // Target hart for debug
        logic [ADDR_WIDTH-1:0]   debug_addr;   // Debug address
        logic [XLEN-1:0]         debug_data;   // Debug data
        logic                    halt_req;     // Halt request
        logic                    resume_req;   // Resume request
    } debug_msg_t;

    //-----
    // Constants and Parameters
    //-----
    
    // AI_TAG: CONSTANT - Maximum message queue depth
    localparam int MAX_MSG_QUEUE_DEPTH = 16;
    
    // AI_TAG: CONSTANT - Maximum outstanding atomic operations
    localparam int MAX_ATOMIC_OPS = 8;
    
    // AI_TAG: CONSTANT - Synchronization timeout default
    localparam int SYNC_TIMEOUT_DEFAULT = 1000;
    
    // AI_TAG: CONSTANT - Network packet size
    localparam int NETWORK_PACKET_SIZE = 128;

    //-----
    // Utility Functions
    //-----
    
    // AI_TAG: FUNCTION - Calculate routing distance between harts
    function automatic logic [3:0] calc_routing_distance(
        input logic [HART_ID_WIDTH-1:0] src_hart,
        input logic [HART_ID_WIDTH-1:0] dst_hart,
        input network_topology_e topology
    );
        case (topology)
            NETWORK_RING: begin
                logic [HART_ID_WIDTH-1:0] forward_dist = dst_hart - src_hart;
                logic [HART_ID_WIDTH-1:0] backward_dist = src_hart - dst_hart;
                return (forward_dist < backward_dist) ? forward_dist[3:0] : backward_dist[3:0];
            end
            NETWORK_MESH: begin
                // Simplified Manhattan distance for 2D mesh
                logic [HART_ID_WIDTH/2-1:0] src_x = src_hart[HART_ID_WIDTH/2-1:0];
                logic [HART_ID_WIDTH/2-1:0] src_y = src_hart[HART_ID_WIDTH-1:HART_ID_WIDTH/2];
                logic [HART_ID_WIDTH/2-1:0] dst_x = dst_hart[HART_ID_WIDTH/2-1:0];
                logic [HART_ID_WIDTH/2-1:0] dst_y = dst_hart[HART_ID_WIDTH-1:HART_ID_WIDTH/2];
                return (((dst_x > src_x) ? (dst_x - src_x) : (src_x - dst_x)) +
                        ((dst_y > src_y) ? (dst_y - src_y) : (src_y - dst_y)));
            end
            NETWORK_XBAR: begin
                return 1; // Direct connection
            end
            default: return 4'hF; // Unknown topology
        endcase
    endfunction

    // AI_TAG: FUNCTION - Check if atomic operation is valid
    function automatic logic is_atomic_op_valid(
        input atomic_op_e op,
        input logic [XLEN-1:0] addr,
        input logic [XLEN-1:0] data
    );
        // Check alignment requirements
        case (op)
            ATOMIC_ADD, ATOMIC_AND, ATOMIC_OR, ATOMIC_XOR,
            ATOMIC_MIN, ATOMIC_MAX, ATOMIC_MINU, ATOMIC_MAXU,
            ATOMIC_SWAP, ATOMIC_CAS: begin
                return (addr[1:0] == 2'b00); // 4-byte aligned
            end
            ATOMIC_LR, ATOMIC_SC: begin
                return (addr[1:0] == 2'b00) && (addr[ADDR_WIDTH-1:12] != '0); // Valid memory region
            end
            default: return 1'b0;
        endcase
    endfunction

endpackage : riscv_inter_core_types_pkg

//=============================================================================
// Dependencies: riscv_config_pkg, riscv_types_pkg
//
// Usage:
//   import riscv_inter_core_types_pkg::*;
//
// Features:
//   - Comprehensive inter-core communication types
//   - Atomic operation primitives for RISC-V A extension
//   - Cache coherency message definitions
//   - Synchronization primitive support
//   - Network topology abstraction
//   - Performance monitoring structures
//   - Debug and trace support
//
// Integration:
//   - Used by multi_core_system.sv
//   - Required for cache coherency controllers
//   - Essential for inter-core communication fabric
//   - Supports atomic memory operations
//
// Verification:
//   - Type safety for inter-core operations
//   - Protocol compliance checking
//   - Message format validation
//   - Network topology verification
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-01-27 | DesignAI          | Initial inter-core types package
//============================================================================= 