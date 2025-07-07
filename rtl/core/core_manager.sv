//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-27
//
// File: core_manager.sv
// Module: core_manager
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Verification Status: Not Verified
// Quality Status: Draft
//
// Description:
//   Manages the operation of a multi-core RISC-V system. It is responsible
//   for core startup, shutdown, inter-core communication routing, and handling
//   synchronization primitives like barriers. It acts as the central hub for
//   all multi-core coordination activities.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

// AI_TAG: FEATURE - Arbitrates and routes inter-core messages.
// AI_TAG: FEATURE - Implements stateful hardware barrier synchronization.
// AI_TAG: FEATURE - Manages core status and readiness.
// AI_TAG: INTERNAL_BLOCK - CommArbiter - Round-robin arbiter for inter-core message requests.
// AI_TAG: INTERNAL_BLOCK - CommRouter - Routes arbitrated messages to destination cores.
// AI_TAG: INTERNAL_BLOCK - BarrierSync - State machine and storage for hardware barriers.

module core_manager #(
    parameter integer NUM_CORES = riscv_core_pkg::MAX_CORES,    // AI_TAG: PARAM_DESC - The total number of cores in the system.
                                        // AI_TAG: PARAM_USAGE - Must match NUM_CORES in connected interfaces and cores.
                                        // AI_TAG: PARAM_CONSTRAINTS - Must be > 1.
    // NOTE: NUM_BARRIERS, MSG_WIDTH, etc. are inherited from the interfaces
    parameter integer CORE_ID_WIDTH = $clog2(NUM_CORES)
) (
    input  logic clk_i,    // AI_TAG: PORT_DESC - System clock
                           // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic rst_ni,   // AI_TAG: PORT_DESC - Asynchronous active-low reset
                           // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)

    // Core Status
    input  logic [NUM_CORES-1:0] core_active_i,  // AI_TAG: PORT_DESC - Bitmask indicating which cores are active and running.
                                                 // AI_TAG: PORT_CLK_DOMAIN - clk_i
    output logic [NUM_CORES-1:0] core_ready_o, // AI_TAG: PORT_DESC - Bitmask indicating manager is ready for core operations.
                                                 // AI_TAG: PORT_CLK_DOMAIN - clk_i

    // Interface for Inter-Core Communication
    // AI_TAG: IF_TYPE - Custom Inter-Core Communication
    // AI_TAG: IF_MODPORT - manager
    // AI_TAG: IF_DESC - Handles routing messages between cores.
    inter_core_comm_if.manager comm_if,

    // Interface for Synchronization Primitives
    // AI_TAG: IF_TYPE - Custom Synchronization Primitives
    // AI_TAG: IF_MODPORT - manager
    // AI_TAG: IF_DESC - Handles hardware barrier synchronization.
    sync_primitives_if.manager sync_if
);

    //-----
    // Local Parameters
    //-----
    localparam integer BARRIER_ID_WIDTH = sync_if.BARRIER_ID_WIDTH;
    localparam integer NUM_BARRIERS = sync_if.NUM_BARRIERS;

    //-----
    // Core Status Logic
    //-----
    // For now, manager is ready when the core is active.
    // This can be expanded with more complex startup sequences.
    assign core_ready_o = core_active_i;

    //-----
    // Inter-Core Communication Logic
    //-----
    // Implements a simple round-robin arbiter and a message router.

    logic [CORE_ID_WIDTH-1:0]   rr_arbiter_ptr_r;
    logic [NUM_CORES-1:0]       rr_arbiter_req_c;
    logic [NUM_CORES-1:0]       rr_arbiter_grant_c;
    logic                       rr_arbiter_grant_valid_c;
    logic [CORE_ID_WIDTH-1:0]   rr_arbiter_grant_id_c;

    // Router signals
    logic                       router_dest_ready_c;
    logic [CORE_ID_WIDTH-1:0]   router_dest_id_c;

    // Connect arbitration requests
    assign rr_arbiter_req_c = comm_if.send_valid_w;

    // Round-robin pointer update
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_rr_ptr
        if (!rst_ni) begin
            rr_arbiter_ptr_r <= '0;
        end else if (rr_arbiter_grant_valid_c) begin
            // Point to next core after the granted one
            rr_arbiter_ptr_r <= rr_arbiter_grant_id_c + 1;
        end
    end

    // Round-robin arbiter logic
    // AI_TAG: FSM_NAME - comm_arbiter_fsm
    // AI_TAG: FSM_PURPOSE - comm_arbiter_fsm - Grants one requesting core per cycle for messaging.
    always_comb begin : proc_comm_arbiter
        logic [NUM_CORES-1:0] priority_c;
        rr_arbiter_grant_c = '0;
        rr_arbiter_grant_valid_c = 1'b0;
        rr_arbiter_grant_id_c = '0;

        // Simple priority mask based on pointer
        priority_c = ({NUM_CORES{1'b1}} << rr_arbiter_ptr_r);

        for (int i = 0; i < 2 * NUM_CORES; i++) begin
            int core_idx = i % NUM_CORES;
            if (rr_arbiter_req_c[core_idx] && priority_c[core_idx] && !rr_arbiter_grant_valid_c) begin
                rr_arbiter_grant_c[core_idx] = 1'b1;
                rr_arbiter_grant_valid_c = 1'b1;
                rr_arbiter_grant_id_c = CORE_ID_WIDTH'(core_idx);
            end
        end
    end

    // Message Router
    // AI_TAG: DATAPATH_DESC - Routes message from granted source to specified destination if destination is ready.
    assign router_dest_id_c = comm_if.send_dest_id_w[rr_arbiter_grant_id_c];
    assign router_dest_ready_c = comm_if.recv_ready_w[router_dest_id_c];

    always_comb begin : proc_comm_router
        // Default outputs
        comm_if.send_ready_w = '0;
        comm_if.recv_valid_w = '0;
        comm_if.recv_source_id_w = '{default:'0};
        comm_if.recv_message_w = '{default:'0};

        if (rr_arbiter_grant_valid_c) begin
            // Grant is valid, check if destination is ready
            if (router_dest_ready_c) begin
                // Tell granted core we are ready to take its message
                comm_if.send_ready_w[rr_arbiter_grant_id_c] = 1'b1;

                // Drive the message to the destination core
                comm_if.recv_valid_w[router_dest_id_c] = 1'b1;
                comm_if.recv_source_id_w[router_dest_id_c] = rr_arbiter_grant_id_c;
                comm_if.recv_message_w[router_dest_id_c] = comm_if.send_message_w[rr_arbiter_grant_id_c];
            end
        end
    end


    //-----
    // Barrier Synchronization Logic
    //-----
    // AI_TAG: INTERNAL_STORAGE - barrier_arrival_mask_r - Bitmask of cores that have arrived at each barrier.
    // AI_TAG: INTERNAL_STORAGE - barrier_release_mask_r - Bitmask of cores that have acknowledged release from each barrier.

    logic [NUM_BARRIERS-1:0] [NUM_CORES-1:0] barrier_arrival_mask_r, barrier_arrival_mask_ns;
    logic [NUM_BARRIERS-1:0] [NUM_CORES-1:0] barrier_release_mask_r, barrier_release_mask_ns;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_barrier_regs
        if (!rst_ni) begin
            barrier_arrival_mask_r <= '{default:'0};
            barrier_release_mask_r <= '{default:'0};
        end else begin
            barrier_arrival_mask_r <= barrier_arrival_mask_ns;
            barrier_release_mask_r <= barrier_release_mask_ns;
        end
    end

    // AI_TAG: FSM_NAME - barrier_sync_fsm
    // AI_TAG: FSM_PURPOSE - barrier_sync_fsm - For each barrier, tracks arrivals and coordinates release.
    always_comb begin : proc_barrier_logic
        logic [BARRIER_ID_WIDTH-1:0]            current_barrier_id;
        logic                                   barrier_is_full_c;

        // Default assignments
        sync_if.arrive_ready_w = '0;
        sync_if.release_valid_w = '0;
        barrier_arrival_mask_ns = barrier_arrival_mask_r;
        barrier_release_mask_ns = barrier_release_mask_r;

        // Check for arrivals from each core
        for (int i = 0; i < NUM_CORES; i++) begin
            current_barrier_id = sync_if.barrier_id_w[i];
            barrier_is_full_c = &barrier_arrival_mask_r[current_barrier_id];

            // Core 'i' wants to arrive at a barrier
            if (sync_if.arrive_valid_w[i]) begin
                // Manager can accept arrival if the barrier is not already full and this core hasn't already arrived.
                if (!barrier_arrival_mask_r[current_barrier_id][i] && !barrier_is_full_c) begin
                    sync_if.arrive_ready_w[i] = 1'b1;
                    barrier_arrival_mask_ns[current_barrier_id][i] = 1'b1;
                end
            end
        end

        // Check for release conditions and drive release signals
        for (int barrier_idx = 0; barrier_idx < NUM_BARRIERS; barrier_idx++) begin
            logic all_arrived_c;
            logic all_released_c;

            all_arrived_c = &barrier_arrival_mask_r[barrier_idx];
            all_released_c = &barrier_release_mask_r[barrier_idx];

            if (all_arrived_c && !all_released_c) begin
                // All cores have arrived. Start the release phase.
                for (int i = 0; i < NUM_CORES; i++) begin
                    // Assert release valid to every core that was part of this barrier sync
                    if (barrier_arrival_mask_r[barrier_idx][i]) begin
                        sync_if.release_valid_w[i] = 1'b1;
                        if (sync_if.release_ready_w[i]) begin
                            barrier_release_mask_ns[barrier_idx][i] = 1'b1;
                        end
                    end
                end
            end else if (all_arrived_c && all_released_c) begin
                // All cores have been released, reset the barrier state for reuse
                barrier_arrival_mask_ns[barrier_idx] = '0;
                barrier_release_mask_ns[barrier_idx] = '0;
            end
        end
    end

endmodule : core_manager

//=============================================================================
// Dependencies:
//   - rtl/interfaces/inter_core_comm_if.sv
//   - rtl/interfaces/sync_primitives_if.sv
//
// Performance:
//   - Critical Path: TBD, likely in the arbiter or barrier logic.
//   - Max Frequency: TBD
//   - Area: TBD
//
// Verification Coverage:
//   - Code Coverage: N/A
//   - Functional Coverage: N/A
//   - Branch Coverage: N/A
//
// Synthesis:
//   - Target Technology: ASIC/FPGA
//   - Synthesis Tool: N/A
//   - Clock Domains: 1 (clk_i)
//   - Constraints File: N/A
//
// Testing:
//   - Testbench: riscv_core_integration_tb (not yet updated for this)
//   - Test Vectors: N/A
//
//----
// Revision History:
// Version | Date       | Author             | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI           | Initial fleshed-out implementation with arbiter and barrier logic.
// 0.1.0   | 2025-06-27 | DesignAI           | Initial skeleton release
//=============================================================================

`default_nettype wire 