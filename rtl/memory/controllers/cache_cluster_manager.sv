//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-28
//
// File: cache_cluster_manager.sv
// Module: cache_cluster_manager
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Cache cluster manager that instantiates and manages multiple L2 and L3
//   cache instances based on the system topology configuration. Supports
//   various cache topologies from unified to NUMA-aware distributions.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

import riscv_core_pkg::*;
import riscv_cache_topology_pkg::*;

module cache_cluster_manager #(
    parameter integer NUM_CORES = DEFAULT_NUM_CORES,
    parameter cache_topology_e CACHE_TOPOLOGY = CACHE_TOPOLOGY_UNIFIED,
    parameter integer L2_CACHE_SIZE = DEFAULT_L2_CACHE_SIZE,
    parameter integer L3_CACHE_SIZE = DEFAULT_L3_CACHE_SIZE
) (
    input  logic clk_i,
    input  logic rst_ni,
    
    // Topology configuration input
    input  system_cache_topology_t topology_config_i,
    
    // L1 cache interfaces from cores (input)
    memory_req_rsp_if.slave l1_dcache_if [NUM_CORES],
    memory_req_rsp_if.slave l1_icache_if [NUM_CORES],
    
    // External memory interfaces (output)
    memory_req_rsp_if.master mem_if [MAX_MEMORY_CONTROLLERS],
    
    // Cache coherency interfaces
    cache_coherency_if.cache_cluster_port coherency_if [NUM_CORES],
    
    // Status and control
    output logic [MAX_L2_INSTANCES-1:0]   l2_instance_active_o,
    output logic [MAX_L3_INSTANCES-1:0]   l3_instance_active_o,
    output logic [31:0]                   cluster_status_o,
    output logic [31:0]                   cache_miss_count_o,
    output logic                          topology_valid_o,

    // Performance monitoring
    // TODO: Split into separate I-cache and D-cache miss signals when routing is updated.
    output logic [NUM_CORES-1:0]           l1_icache_miss_o,
    output logic [NUM_CORES-1:0]           l1_dcache_miss_o
);

    //-------------------------------------------------------------------------
    // Local Parameters and Types
    //-------------------------------------------------------------------------
    
    localparam integer MAX_CORES_PER_L2 = NUM_CORES;
    localparam integer MAX_L2_PER_L3 = MAX_L2_INSTANCES;
    
    //-------------------------------------------------------------------------
    // Internal Interfaces and Signals
    //-------------------------------------------------------------------------
    
    // L2 cache interfaces (connecting L1s to L2s)
    memory_req_rsp_if l2_l1_if [MAX_L2_INSTANCES][MAX_CORES_PER_L2] (
        .clk(clk_i),
        .rst_n(rst_ni)
    );
    
    // L3 cache interfaces (connecting L2s to L3s)
    memory_req_rsp_if l2_l3_if [MAX_L2_INSTANCES] (
        .clk(clk_i),
        .rst_n(rst_ni)
    );
    
    // L3 to memory interfaces
    memory_req_rsp_if l3_mem_if [MAX_L3_INSTANCES] (
        .clk(clk_i),
        .rst_n(rst_ni)
    );
    
    // Inter-L2 coherency interfaces for distributed coherency
    cache_coherency_if l2_coherency_if [MAX_L2_INSTANCES] (
        .clk(clk_i),
        .rst_n(rst_ni)
    );
    
    // Configuration and status signals
    logic [MAX_L2_INSTANCES-1:0] l2_enable;
    logic [MAX_L3_INSTANCES-1:0] l3_enable;
    logic [31:0] total_cache_misses [MAX_L2_INSTANCES];
    logic topology_validated_r;
    logic [NUM_CORES-1:0] l1_miss_from_l2s [MAX_L2_INSTANCES-1:0];
    
    //-------------------------------------------------------------------------
    // Core-to-L2 Routing Logic
    //-------------------------------------------------------------------------
    
    // AI_TAG: ROUTING_LOGIC - Route L1 requests to appropriate L2 instances
    generate
        for (genvar core_id = 0; core_id < NUM_CORES; core_id++) begin : gen_core_routing
            
            logic [3:0] target_l2_instance;
            logic [3:0] l2_core_index;
            
            // Determine which L2 instance serves this core
            always_comb begin
                target_l2_instance = get_l2_for_core(core_id[3:0], topology_config_i);
                l2_core_index = 0;
                
                // Find the local index within the L2 cache for this core
                for (int i = 0; i < core_id; i++) begin
                    if (topology_config_i.clusters[target_l2_instance].core_mask[i]) begin
                        l2_core_index++;
                    end
                end
            end
            
            // Connect core's L1 I-cache to the same L2 target
            // NOTE: A proper arbiter is needed if both can request simultaneously.
            // For now, we assume I-cache and D-cache requests from a single core
            // are serialized and won't conflict at the input to the L2.
            // This is a simplifying assumption for this stage of development.
            
            // --- BEGIN FIX: Add arbiter for I-cache and D-cache requests ---
            always_comb begin
                // Default assignments
                l2_l1_if[target_l2_instance][l2_core_index].req_valid = 1'b0;
                l2_l1_if[target_l2_instance][l2_core_index].req = '0;
                l1_icache_if[core_id].req_ready = 1'b0;
                l1_dcache_if[core_id].req_ready = 1'b0;

                // Prioritize I-cache over D-cache
                if (l1_icache_if[core_id].req_valid) begin
                    l2_l1_if[target_l2_instance][l2_core_index].req_valid = l1_icache_if[core_id].req_valid;
                    l2_l1_if[target_l2_instance][l2_core_index].req       = l1_icache_if[core_id].req;
                    l1_icache_if[core_id].req_ready = l2_l1_if[target_l2_instance][l2_core_index].req_ready;
                    l1_dcache_if[core_id].req_ready = 1'b0;
                end else if (l1_dcache_if[core_id].req_valid) begin
                    l2_l1_if[target_l2_instance][l2_core_index].req_valid = l1_dcache_if[core_id].req_valid;
                    l2_l1_if[target_l2_instance][l2_core_index].req       = l1_dcache_if[core_id].req;
                    l1_dcache_if[core_id].req_ready = l2_l1_if[target_l2_instance][l2_core_index].req_ready;
                    l1_icache_if[core_id].req_ready = 1'b0;
                end
            end
            
            // Route L2 responses back to both I-cache and D-cache interfaces.
            // The core_subsystem will use the transaction ID to accept the correct one.
            assign l1_dcache_if[core_id].rsp_valid = l2_l1_if[target_l2_instance][l2_core_index].rsp_valid;
            assign l1_dcache_if[core_id].rsp = l2_l1_if[target_l2_instance][l2_core_index].rsp;
            assign l1_icache_if[core_id].rsp_valid = l2_l1_if[target_l2_instance][l2_core_index].rsp_valid;
            assign l1_icache_if[core_id].rsp = l2_l1_if[target_l2_instance][l2_core_index].rsp;
            
            // The ready signal can be combined as only one will be active
            assign l2_l1_if[target_l2_instance][l2_core_index].rsp_ready = l1_dcache_if[core_id].rsp_ready || l1_icache_if[core_id].rsp_ready;
            // --- END FIX ---

        end : gen_core_routing
    endgenerate
    
    //-------------------------------------------------------------------------
    // L2 Cache Instance Generation
    //-------------------------------------------------------------------------
    
    generate
        for (genvar l2_id = 0; l2_id < MAX_L2_INSTANCES; l2_id++) begin : gen_l2_instances
            
            // Calculate the number of cores served by this L2 instance
            logic [3:0] cores_served;
            always_comb begin
                cores_served = 0;
                if (l2_id < topology_config_i.num_l2_instances) begin
                    cores_served = topology_config_i.clusters[l2_id].num_cores;
                end
            end
            
            // L2 cache instance
            l2_cache #(
                .L2_CACHE_SIZE(L2_CACHE_SIZE),
                .NUM_CORES(MAX_CORES_PER_L2),  // Use max for interface sizing
                .NUM_WAYS(DEFAULT_L2_CACHE_WAYS),
                .CACHE_LINE_SIZE(DEFAULT_CACHE_LINE_SIZE)
            ) u_l2_cache (
                .clk_i(clk_i),
                .rst_ni(rst_ni && l2_enable[l2_id]),
                
                // Interfaces from L1 caches
                .l1_if(l2_l1_if[l2_id]),
                
                // Interface to L3 cache
                .l3_if(l2_l3_if[l2_id]),
                
                // Cache coherency interface
                .coherency_if(l2_coherency_if[l2_id]),

                // Performance Monitoring
                .l1_miss_o(l1_miss_from_l2s[l2_id])
            );
            
            // Enable L2 instance based on topology
            assign l2_enable[l2_id] = (l2_id < topology_config_i.num_l2_instances);
            
        end : gen_l2_instances
    endgenerate
    
    //-------------------------------------------------------------------------
    // L2-to-L3 Routing and Interconnect
    //-------------------------------------------------------------------------
    
    // AI_TAG: INTERCONNECT_LOGIC - Route L2 requests to appropriate L3 instances
    generate
        for (genvar l2_id = 0; l2_id < MAX_L2_INSTANCES; l2_id++) begin : gen_l2_l3_routing
            
            logic [3:0] target_l3_instance;
            
            // Determine which L3 instance serves this L2
            always_comb begin
                target_l3_instance = 0;
                if (l2_id < topology_config_i.num_l2_instances) begin
                    target_l3_instance = topology_config_i.clusters[l2_id].l3_instance_id;
                end
            end
            
            // Address-based routing for more complex topologies
            logic use_address_routing;
            logic [3:0] address_based_l3;
            
            assign use_address_routing = (topology_config_i.topology_type == CACHE_TOPOLOGY_NUMA) ||
                                       (topology_config_i.topology_type == CACHE_TOPOLOGY_DISTRIBUTED);
            
            always_comb begin
                if (use_address_routing && l2_l3_if[l2_id].req_valid) begin
                    address_based_l3 = get_l3_instance_for_address(l2_l3_if[l2_id].req.addr, topology_config_i);
                end else begin
                    address_based_l3 = target_l3_instance;
                end
            end
            
            // Simple interconnect - direct connection for now
            // In full implementation, this would be a proper interconnect fabric
            if (l2_id < MAX_L3_INSTANCES) begin : gen_direct_l3_connection
                assign l3_mem_if[l2_id].req_valid = l2_l3_if[l2_id].req_valid && l2_enable[l2_id];
                assign l3_mem_if[l2_id].req = l2_l3_if[l2_id].req;
                assign l2_l3_if[l2_id].req_ready = l3_mem_if[l2_id].req_ready;
                assign l2_l3_if[l2_id].rsp_valid = l3_mem_if[l2_id].rsp_valid;
                assign l2_l3_if[l2_id].rsp = l3_mem_if[l2_id].rsp;
                assign l3_mem_if[l2_id].rsp_ready = l2_l3_if[l2_id].rsp_ready;
            end
            
        end : gen_l2_l3_routing
    endgenerate
    
    //-------------------------------------------------------------------------
    // L3 Cache Instance Generation
    //-------------------------------------------------------------------------
    
    generate
        for (genvar l3_id = 0; l3_id < MAX_L3_INSTANCES; l3_id++) begin : gen_l3_instances
            
            // L3 cache instance
            l3_cache #(
                .L3_CACHE_SIZE(L3_CACHE_SIZE),
                .NUM_WAYS(DEFAULT_L3_CACHE_WAYS),
                .CACHE_LINE_SIZE(DEFAULT_CACHE_LINE_SIZE)
            ) u_l3_cache (
                .clk_i(clk_i),
                .rst_ni(rst_ni && l3_enable[l3_id]),
                
                // Interface from L2 cache(s)
                .l2_if(l3_mem_if[l3_id]),
                
                // Interface to external memory
                .mem_if(mem_if[l3_id])
            );
            
            // Enable L3 instance based on topology
            assign l3_enable[l3_id] = (l3_id < topology_config_i.num_l3_instances);
            
        end : gen_l3_instances
    endgenerate
    
    //-------------------------------------------------------------------------
    // Distributed Cache Coherency Controller
    //-------------------------------------------------------------------------
    
    // AI_TAG: COHERENCY_MANAGER - Manage coherency across multiple cache instances
    generate
        if (CACHE_TOPOLOGY != CACHE_TOPOLOGY_UNIFIED) begin : gen_distributed_coherency
            
            // Distributed coherency controller for multi-cache scenarios
            cache_coherency_controller #(
                .NUM_CORES(NUM_CORES),
                .ADDR_WIDTH(ADDR_WIDTH),
                .L2_CACHE_WAYS(DEFAULT_L2_CACHE_WAYS),
                .L2_CACHE_SETS(L2_CACHE_SIZE / (DEFAULT_CACHE_LINE_SIZE * DEFAULT_L2_CACHE_WAYS))
            ) u_distributed_coherency_controller (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                
                // Connect to all cores' coherency interfaces
                .coherency_if(coherency_if[0]), // Simplified - full implementation needs array
                
                // Interface to memory for misses and writebacks
                .mem_if(l3_mem_if[0]), // Simplified connection
                
                // L2 cache directory interface
                .l2_tag_match_way_i(8'h01),
                .l2_line_state_i(CACHE_SHARED),
                .l2_sharer_list_i({NUM_CORES{1'b1}}),
                .l2_update_en_o(),
                .l2_way_select_o()
            );
            
        end : gen_distributed_coherency
    endgenerate
    
    //-------------------------------------------------------------------------
    // Topology Validation and Management
    //-------------------------------------------------------------------------
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_topology_validation
        if (!rst_ni) begin
            topology_validated_r <= 1'b0;
        end else begin
            topology_validated_r <= validate_cache_topology(topology_config_i, NUM_CORES);
        end
    end
    
    //-------------------------------------------------------------------------
    // Status and Monitoring
    //-------------------------------------------------------------------------
    
    // Aggregate cache miss counts
    always_comb begin
        cache_miss_count_o = 0;
        for (int i = 0; i < MAX_L2_INSTANCES; i++) begin
            if (l2_enable[i]) begin
                cache_miss_count_o += total_cache_misses[i];
            end
        end
    end
    
    // Instance activity status
    assign l2_instance_active_o = l2_enable;
    assign l3_instance_active_o = l3_enable;
    assign topology_valid_o = topology_validated_r;
    
    // Cluster status encoding
    assign cluster_status_o = {
        8'h0,                                    // Reserved [31:24]
        topology_config_i.num_memory_controllers[1:0], // Memory controllers [23:22]
        topology_config_i.num_l3_instances[1:0],        // L3 instances [21:20]
        topology_config_i.num_l2_instances[1:0],        // L2 instances [19:18]
        topology_config_i.num_clusters[1:0],            // Clusters [17:16]
        topology_config_i.numa_enabled,                 // NUMA enabled [15]
        topology_config_i.adaptive_clustering,          // Adaptive clustering [14]
        2'b0,                                    // Reserved [13:12]
        topology_config_i.topology_type[2:0],           // Topology type [11:9]
        1'b0,                                    // Reserved [8]
        l3_instance_active_o[7:0]                       // L3 active status [7:0]
    };
    
    //-------------------------------------------------------------------------
    // Performance Signal Aggregation
    //-------------------------------------------------------------------------
    logic [NUM_CORES-1:0] combined_l1_misses;
    always_comb begin
        combined_l1_misses = '0;
        for (int i = 0; i < MAX_L2_INSTANCES; i++) begin
            combined_l1_misses |= l1_miss_from_l2s[i];
        end
    end

    assign l1_icache_miss_o = combined_l1_misses;
    assign l1_dcache_miss_o = combined_l1_misses;

    //-------------------------------------------------------------------------
    // Assertions for Design Validation
    //-------------------------------------------------------------------------
    
    // AI_TAG: ASSERTION - Topology configuration should be valid
    TopologyValid: assert property (@(posedge clk_i) disable iff (!rst_ni)
        topology_validated_r == 1'b1)
        else $error("Invalid cache topology configuration detected");
    
    // AI_TAG: ASSERTION - Active instances should match configuration
    ActiveInstancesMatch: assert property (@(posedge clk_i) disable iff (!rst_ni)
        ($countones(l2_instance_active_o) == topology_config_i.num_l2_instances) &&
        ($countones(l3_instance_active_o) == topology_config_i.num_l3_instances))
        else $warning("Active cache instances do not match topology configuration");
    
    // AI_TAG: ASSERTION - All cores should be served by an L2 cache
    AllCoresServed: assert property (@(posedge clk_i) disable iff (!rst_ni)
        validate_cache_topology(topology_config_i, NUM_CORES) == 1'b1)
        else $error("Not all cores are served by cache topology");

endmodule : cache_cluster_manager

`default_nettype wire 