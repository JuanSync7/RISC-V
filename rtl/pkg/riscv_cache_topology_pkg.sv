//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-28
//
// File: riscv_cache_topology_pkg.sv
// Module: riscv_cache_topology_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Cache topology configuration package that supports multiple L2/L3 cache
//   arrangements, cache clustering, and NUMA-aware cache hierarchies.
//   Enables flexible cache architectures from single cache to distributed
//   multi-cache systems.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_cache_topology_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;
    import riscv_cache_types_pkg::*;

    //-------------------------------------------------------------------------
    // Cache Topology Types
    //-------------------------------------------------------------------------
    
    // AI_TAG: ENUM - Cache topology configurations
    typedef enum logic [2:0] {
        CACHE_TOPOLOGY_UNIFIED    = 3'b000,  // Single L2 + Single L3 (current)
        CACHE_TOPOLOGY_CLUSTERED  = 3'b001,  // Multiple L2 clusters + Single L3
        CACHE_TOPOLOGY_DISTRIBUTED = 3'b010, // Multiple L2 + Multiple L3
        CACHE_TOPOLOGY_NUMA       = 3'b011,  // NUMA-aware cache distribution
        CACHE_TOPOLOGY_HIERARCHICAL = 3'b100, // Multi-level cache clusters
        CACHE_TOPOLOGY_CUSTOM     = 3'b111   // User-defined topology
    } cache_topology_e;

    //-------------------------------------------------------------------------
    // Cache Cluster Configuration
    //-------------------------------------------------------------------------
    
    // AI_TAG: PARAM - Maximum number of cache clusters supported
    parameter integer MAX_CACHE_CLUSTERS = 4;
    parameter integer MAX_L2_INSTANCES = 4;
    parameter integer MAX_L3_INSTANCES = 2;
    parameter integer MAX_MEMORY_CONTROLLERS = 2;
    
    // AI_TAG: STRUCT - Cache cluster configuration
    typedef struct packed {
        logic [3:0]             cluster_id;           // Unique cluster ID
        logic [3:0]             num_cores;            // Cores in this cluster
        logic [7:0]             core_mask;            // Which cores belong to cluster
        logic [31:0]            l2_cache_size;        // L2 cache size for cluster
        logic [3:0]             l2_cache_ways;        // L2 associativity
        logic [3:0]             l3_instance_id;       // Which L3 this cluster uses
        logic                   has_local_l3;         // Does cluster have local L3?
        logic [1:0]             memory_controller_id; // Which memory controller
        logic [7:0]             bandwidth_allocation; // Bandwidth percentage
        logic                   coherency_domain;     // Coherency domain membership
    } cache_cluster_config_t;
    
    // AI_TAG: STRUCT - System cache topology configuration
    typedef struct packed {
        cache_topology_e        topology_type;        // Topology selection
        logic [3:0]             num_l2_instances;     // Number of L2 caches
        logic [3:0]             num_l3_instances;     // Number of L3 caches
        logic [3:0]             num_clusters;         // Number of cache clusters
        logic [1:0]             num_memory_controllers; // Number of memory controllers
        logic                   numa_enabled;         // NUMA support enabled
        logic                   adaptive_clustering;  // Dynamic cluster assignment
        logic [15:0]            interconnect_type;    // Interconnect configuration
        cache_cluster_config_t  clusters[MAX_CACHE_CLUSTERS-1:0]; // Cluster configs
    } system_cache_topology_t;

    //-------------------------------------------------------------------------
    // Cache Instance Configuration
    //-------------------------------------------------------------------------
    
    // AI_TAG: STRUCT - L2 cache instance configuration
    typedef struct packed {
        logic [3:0]             instance_id;          // L2 instance ID
        logic [31:0]            cache_size;           // Cache size in bytes
        logic [3:0]             num_ways;             // Associativity
        logic [3:0]             num_cores_served;     // Number of cores served
        logic [7:0]             core_mask;            // Which cores this L2 serves
        logic [3:0]             l3_target;            // Target L3 instance
        logic [31:0]            base_address;         // Address range start
        logic [31:0]            address_mask;         // Address range mask
        logic                   coherency_enabled;    // Coherency participation
        logic [7:0]             qos_class;            // QoS classification
    } l2_instance_config_t;
    
    // AI_TAG: STRUCT - L3 cache instance configuration  
    typedef struct packed {
        logic [3:0]             instance_id;          // L3 instance ID
        logic [31:0]            cache_size;           // Cache size in bytes
        logic [4:0]             num_ways;             // Associativity
        logic [3:0]             num_l2_served;        // Number of L2 caches served
        logic [15:0]            l2_mask;              // Which L2 caches served
        logic [1:0]             memory_controller;    // Memory controller assignment
        logic [31:0]            base_address;         // Address range start
        logic [31:0]            address_mask;         // Address range mask
        logic                   victim_cache_mode;    // Victim cache operation
        logic [7:0]             bandwidth_allocation; // Memory bandwidth %
    } l3_instance_config_t;

    //-------------------------------------------------------------------------
    // Cache Interconnect Configuration
    //-------------------------------------------------------------------------
    
    // AI_TAG: ENUM - Cache interconnect types
    typedef enum logic [2:0] {
        INTERCONNECT_BUS      = 3'b000,  // Shared bus (single L2/L3)
        INTERCONNECT_CROSSBAR = 3'b001,  // Full crossbar
        INTERCONNECT_RING     = 3'b010,  // Ring topology
        INTERCONNECT_MESH     = 3'b011,  // 2D mesh
        INTERCONNECT_TREE     = 3'b100,  // Hierarchical tree
        INTERCONNECT_CUSTOM   = 3'b111   // Custom topology
    } cache_interconnect_e;
    
    // AI_TAG: STRUCT - Interconnect routing table entry
    typedef struct packed {
        logic [7:0]             source_id;            // Source cache/core ID
        logic [7:0]             destination_id;       // Destination cache ID
        logic [3:0]             hop_count;            // Number of hops
        logic [7:0]             route_path;           // Encoded route path
        logic [3:0]             priority;             // Routing priority
        logic                   coherency_path;       // Used for coherency traffic
    } cache_route_entry_t;

    //-------------------------------------------------------------------------
    // Predefined Cache Topologies
    //-------------------------------------------------------------------------
    
    // AI_TAG: FUNCTION - Get default unified topology (current architecture)
    function automatic system_cache_topology_t get_unified_topology(
        input integer num_cores,
        input integer l2_size,
        input integer l3_size
    );
        system_cache_topology_t topology;
        topology.topology_type = CACHE_TOPOLOGY_UNIFIED;
        topology.num_l2_instances = 1;
        topology.num_l3_instances = 1;
        topology.num_clusters = 1;
        topology.num_memory_controllers = 1;
        topology.numa_enabled = 1'b0;
        topology.adaptive_clustering = 1'b0;
        topology.interconnect_type = {12'b0, INTERCONNECT_BUS};
        
        // Single cluster serving all cores
        topology.clusters[0].cluster_id = 0;
        topology.clusters[0].num_cores = num_cores;
        topology.clusters[0].core_mask = (1 << num_cores) - 1;
        topology.clusters[0].l2_cache_size = l2_size;
        topology.clusters[0].l2_cache_ways = DEFAULT_L2_CACHE_WAYS;
        topology.clusters[0].l3_instance_id = 0;
        topology.clusters[0].has_local_l3 = 1'b1;
        topology.clusters[0].memory_controller_id = 0;
        topology.clusters[0].bandwidth_allocation = 8'hFF;
        topology.clusters[0].coherency_domain = 1'b1;
        
        return topology;
    endfunction
    
    // AI_TAG: FUNCTION - Get clustered topology (2 L2 clusters + 1 L3)
    function automatic system_cache_topology_t get_clustered_topology(
        input integer num_cores,
        input integer l2_size,
        input integer l3_size
    );
        system_cache_topology_t topology;
        topology.topology_type = CACHE_TOPOLOGY_CLUSTERED;
        topology.num_l2_instances = 2;
        topology.num_l3_instances = 1;
        topology.num_clusters = 2;
        topology.num_memory_controllers = 1;
        topology.numa_enabled = 1'b0;
        topology.adaptive_clustering = 1'b0;
        topology.interconnect_type = {12'b0, INTERCONNECT_CROSSBAR};
        
        // Cluster 0: Cores 0-(num_cores/2-1)
        topology.clusters[0].cluster_id = 0;
        topology.clusters[0].num_cores = num_cores / 2;
        topology.clusters[0].core_mask = (1 << (num_cores/2)) - 1;
        topology.clusters[0].l2_cache_size = l2_size;
        topology.clusters[0].l2_cache_ways = DEFAULT_L2_CACHE_WAYS;
        topology.clusters[0].l3_instance_id = 0;
        topology.clusters[0].has_local_l3 = 1'b0;
        topology.clusters[0].memory_controller_id = 0;
        topology.clusters[0].bandwidth_allocation = 8'h80; // 50%
        topology.clusters[0].coherency_domain = 1'b1;
        
        // Cluster 1: Cores (num_cores/2)-(num_cores-1)
        topology.clusters[1].cluster_id = 1;
        topology.clusters[1].num_cores = num_cores / 2;
        topology.clusters[1].core_mask = ((1 << (num_cores/2)) - 1) << (num_cores/2);
        topology.clusters[1].l2_cache_size = l2_size;
        topology.clusters[1].l2_cache_ways = DEFAULT_L2_CACHE_WAYS;
        topology.clusters[1].l3_instance_id = 0;
        topology.clusters[1].has_local_l3 = 1'b0;
        topology.clusters[1].memory_controller_id = 0;
        topology.clusters[1].bandwidth_allocation = 8'h80; // 50%
        topology.clusters[1].coherency_domain = 1'b1;
        
        return topology;
    endfunction
    
    // AI_TAG: FUNCTION - Get NUMA topology (2 L2 + 2 L3 + 2 Memory Controllers)
    function automatic system_cache_topology_t get_numa_topology(
        input integer num_cores,
        input integer l2_size,
        input integer l3_size
    );
        system_cache_topology_t topology;
        topology.topology_type = CACHE_TOPOLOGY_NUMA;
        topology.num_l2_instances = 2;
        topology.num_l3_instances = 2;
        topology.num_clusters = 2;
        topology.num_memory_controllers = 2;
        topology.numa_enabled = 1'b1;
        topology.adaptive_clustering = 1'b1;
        topology.interconnect_type = {12'b0, INTERCONNECT_MESH};
        
        // NUMA Node 0: Cores 0-(num_cores/2-1)
        topology.clusters[0].cluster_id = 0;
        topology.clusters[0].num_cores = num_cores / 2;
        topology.clusters[0].core_mask = (1 << (num_cores/2)) - 1;
        topology.clusters[0].l2_cache_size = l2_size;
        topology.clusters[0].l2_cache_ways = DEFAULT_L2_CACHE_WAYS;
        topology.clusters[0].l3_instance_id = 0;
        topology.clusters[0].has_local_l3 = 1'b1;
        topology.clusters[0].memory_controller_id = 0;
        topology.clusters[0].bandwidth_allocation = 8'hFF; // Full local bandwidth
        topology.clusters[0].coherency_domain = 1'b1;
        
        // NUMA Node 1: Cores (num_cores/2)-(num_cores-1)
        topology.clusters[1].cluster_id = 1;
        topology.clusters[1].num_cores = num_cores / 2;
        topology.clusters[1].core_mask = ((1 << (num_cores/2)) - 1) << (num_cores/2);
        topology.clusters[1].l2_cache_size = l2_size;
        topology.clusters[1].l2_cache_ways = DEFAULT_L2_CACHE_WAYS;
        topology.clusters[1].l3_instance_id = 1;
        topology.clusters[1].has_local_l3 = 1'b1;
        topology.clusters[1].memory_controller_id = 1;
        topology.clusters[1].bandwidth_allocation = 8'hFF; // Full local bandwidth
        topology.clusters[1].coherency_domain = 1'b1;
        
        return topology;
    endfunction

    //-------------------------------------------------------------------------
    // Cache Routing and Address Mapping Functions
    //-------------------------------------------------------------------------
    
    // AI_TAG: FUNCTION - Determine which L2 cache should handle an address
    function automatic logic [3:0] get_l2_instance_for_address(
        input logic [ADDR_WIDTH-1:0] address,
        input system_cache_topology_t topology
    );
        logic [3:0] l2_instance;
        
        case (topology.topology_type)
            CACHE_TOPOLOGY_UNIFIED: begin
                l2_instance = 0; // Single L2
            end
            CACHE_TOPOLOGY_CLUSTERED, CACHE_TOPOLOGY_NUMA: begin
                // Simple address interleaving for cache clusters
                l2_instance = address[DEFAULT_CACHE_LINE_SIZE_BITS +: 2] % topology.num_l2_instances;
            end
            CACHE_TOPOLOGY_DISTRIBUTED: begin
                // More sophisticated address mapping
                l2_instance = address[DEFAULT_CACHE_LINE_SIZE_BITS +: 3] % topology.num_l2_instances;
            end
            default: begin
                l2_instance = 0;
            end
        endcase
        
        return l2_instance;
    endfunction
    
    // AI_TAG: FUNCTION - Determine which L3 cache should handle an address
    function automatic logic [3:0] get_l3_instance_for_address(
        input logic [ADDR_WIDTH-1:0] address,
        input system_cache_topology_t topology
    );
        logic [3:0] l3_instance;
        
        case (topology.topology_type)
            CACHE_TOPOLOGY_UNIFIED, CACHE_TOPOLOGY_CLUSTERED: begin
                l3_instance = 0; // Single L3
            end
            CACHE_TOPOLOGY_NUMA, CACHE_TOPOLOGY_DISTRIBUTED: begin
                // NUMA-aware mapping - high address bits determine node
                l3_instance = address[ADDR_WIDTH-1 -: 2] % topology.num_l3_instances;
            end
            default: begin
                l3_instance = 0;
            end
        endcase
        
        return l3_instance;
    endfunction
    
    // AI_TAG: FUNCTION - Get core-to-L2 mapping
    function automatic logic [3:0] get_l2_for_core(
        input logic [3:0] core_id,
        input system_cache_topology_t topology
    );
        logic [3:0] l2_instance = 0;
        
        // Search through clusters to find which L2 serves this core
        for (int i = 0; i < topology.num_clusters; i++) begin
            if (topology.clusters[i].core_mask[core_id]) begin
                l2_instance = i; // Assuming L2 instance ID matches cluster ID
                break;
            end
        end
        
        return l2_instance;
    endfunction

    //-------------------------------------------------------------------------
    // Validation Functions
    //-------------------------------------------------------------------------
    
    // AI_TAG: FUNCTION - Validate cache topology configuration
    function automatic logic validate_cache_topology(
        input system_cache_topology_t topology,
        input integer total_cores
    );
        logic valid = 1'b1;
        logic [7:0] core_coverage = 0;
        
        // Check if all cores are covered by clusters
        for (int i = 0; i < topology.num_clusters; i++) begin
            core_coverage |= topology.clusters[i].core_mask;
        end
        
        // All cores should be covered
        if (core_coverage != ((1 << total_cores) - 1)) begin
            valid = 1'b0;
        end
        
        // Check that cluster counts match instance counts
        if (topology.num_clusters > topology.num_l2_instances) begin
            valid = 1'b0;
        end
        
        return valid;
    endfunction

endpackage : riscv_cache_topology_pkg

`default_nettype wire 