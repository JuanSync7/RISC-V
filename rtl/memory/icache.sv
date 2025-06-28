////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-28
// Design Name:   RV32IM Core
// Module Name:   icache
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   Instruction Cache (ICache) for the RISC-V core.
//                Implements a 2-way set associative cache with LRU replacement
//                policy. Target: >90% hit rate for typical workloads.
//                Size: 4KB, Line Size: 32 bytes, Ways: 2
//
// Dependencies:  riscv_core_pkg.sv
//
// Revision:
// Revision 1.0.0 - File Created
// Additional Comments:
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps
`default_nettype none

module icache #(
    // AI_TAG: PARAM_DESC - CACHE_SIZE - Total cache size in bytes.
    // AI_TAG: PARAM_USAGE - Determines the total memory capacity of the cache.
    // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2 for efficient indexing.
    parameter integer CACHE_SIZE = 4096,  // 4KB
    
    // AI_TAG: PARAM_DESC - LINE_SIZE - Size of each cache line in bytes.
    // AI_TAG: PARAM_USAGE - Determines the granularity of cache operations.
    // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2 and >= 4 bytes.
    parameter integer LINE_SIZE = 32,     // 32 bytes
    
    // AI_TAG: PARAM_DESC - WAYS - Number of ways in the set associative cache.
    // AI_TAG: PARAM_USAGE - Determines the associativity of the cache.
    // AI_TAG: PARAM_CONSTRAINTS - Must be a power of 2 for efficient indexing.
    parameter integer WAYS = 2            // 2-way set associative
) (
    // AI_TAG: PORT_DESC - clk_i - System clock for synchronous operations.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        clk_i,
    
    // AI_TAG: PORT_DESC - rst_ni - Asynchronous active-low reset.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i (async assert)
    // AI_TAG: PORT_TIMING - Asynchronous
    input  logic        rst_ni,

    // --- Cache Request Interface ---
    // AI_TAG: PORT_DESC - pc_i - Program counter for instruction fetch.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_TIMING - Combinatorial
    input  addr_t       pc_i,
    
    // AI_TAG: PORT_DESC - valid_i - Valid signal for the request.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_TIMING - Combinatorial
    input  logic        valid_i,
    
    // AI_TAG: PORT_DESC - ready_o - Cache is ready to accept new requests.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_DEFAULT_STATE - 1'b1 (ready by default)
    // AI_TAG: PORT_TIMING - Combinatorial
    output logic        ready_o,
    
    // AI_TAG: PORT_DESC - instruction_o - Fetched instruction data.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_DEFAULT_STATE - 32'h0
    // AI_TAG: PORT_TIMING - Combinatorial
    output word_t       instruction_o,
    
    // AI_TAG: PORT_DESC - hit_o - Indicates if the request was a cache hit.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_DEFAULT_STATE - 1'b0
    // AI_TAG: PORT_TIMING - Combinatorial
    output logic        hit_o,
    
    // AI_TAG: PORT_DESC - valid_o - Indicates if the instruction data is valid.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_DEFAULT_STATE - 1'b0
    // AI_TAG: PORT_TIMING - Combinatorial
    output logic        valid_o,

    // --- Memory Interface (AXI4-Lite) ---
    // AI_TAG: PORT_DESC - mem_arvalid_o - AXI4 read address valid.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    output logic        mem_arvalid_o,
    
    // AI_TAG: PORT_DESC - mem_arready_i - AXI4 read address ready.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        mem_arready_i,
    
    // AI_TAG: PORT_DESC - mem_araddr_o - AXI4 read address.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    output addr_t       mem_araddr_o,
    
    // AI_TAG: PORT_DESC - mem_rvalid_i - AXI4 read data valid.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        mem_rvalid_i,
    
    // AI_TAG: PORT_DESC - mem_rdata_i - AXI4 read data.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  word_t       mem_rdata_i,
    
    // AI_TAG: PORT_DESC - mem_rready_o - AXI4 read data ready.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    output logic        mem_rready_o,

    // --- Cache Control Interface ---
    // AI_TAG: PORT_DESC - flush_i - Flush the entire cache.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    input  logic        flush_i,
    
    // AI_TAG: PORT_DESC - flush_done_o - Flush operation completed.
    // AI_TAG: PORT_CLK_DOMAIN - clk_i
    // AI_TAG: PORT_DEFAULT_STATE - 1'b0
    // AI_TAG: PORT_TIMING - Combinatorial
    output logic        flush_done_o
);

    // AI_TAG: INTERNAL_CALCULATION - Cache parameters
    localparam integer SETS = CACHE_SIZE / (LINE_SIZE * WAYS);
    localparam integer INDEX_BITS = $clog2(SETS);
    localparam integer OFFSET_BITS = $clog2(LINE_SIZE);
    localparam integer TAG_BITS = ADDR_WIDTH - INDEX_BITS - OFFSET_BITS;
    localparam integer WORDS_PER_LINE = LINE_SIZE / 4;  // 4 bytes per word
    
    // AI_TAG: INTERNAL_STORAGE - Cache line structure
    typedef struct packed {
        logic                    valid;      // Valid bit
        logic [TAG_BITS-1:0]     tag;        // Tag bits
        word_t                   data [WORDS_PER_LINE-1:0];  // Data array
        logic                    lru;        // LRU bit (for 2-way cache)
    } cache_line_t;
    
    // AI_TAG: INTERNAL_STORAGE - Cache memory array (2-way set associative)
    cache_line_t cache_mem [WAYS-1:0][SETS-1:0];
    
    // AI_TAG: INTERNAL_LOGIC - Address decomposition
    logic [INDEX_BITS-1:0]   index;
    logic [OFFSET_BITS-1:0]  offset;
    logic [TAG_BITS-1:0]     tag;
    
    // AI_TAG: INTERNAL_LOGIC - Cache lookup signals
    logic [WAYS-1:0]         way_hit;
    logic [WAYS-1:0]         way_valid;
    logic [WAYS-1:0]         way_tag_match;
    logic                    any_hit;
    logic [$clog2(WAYS)-1:0] hit_way;
    
    // AI_TAG: INTERNAL_LOGIC - Cache state machine
    typedef enum logic [2:0] {
        IDLE,           // Ready for new requests
        MISS_WAIT,      // Waiting for memory response
        MISS_FILL,      // Filling cache line
        FLUSH_STATE     // Flushing cache
    } cache_state_e;
    
    cache_state_e cache_state_r, cache_state_next;
    
    // AI_TAG: INTERNAL_LOGIC - Miss handling signals
    logic                    miss_detected;
    logic [INDEX_BITS-1:0]   miss_index;
    logic [TAG_BITS-1:0]     miss_tag;
    logic [$clog2(WAYS)-1:0] replace_way;
    logic [OFFSET_BITS-1:0]  fill_offset;
    logic                    fill_complete;
    
    // AI_TAG: INTERNAL_LOGIC - Address decomposition
    assign index  = pc_i[INDEX_BITS+OFFSET_BITS-1:OFFSET_BITS];
    assign offset = pc_i[OFFSET_BITS-1:0];
    assign tag    = pc_i[ADDR_WIDTH-1:INDEX_BITS+OFFSET_BITS];
    
    // AI_TAG: INTERNAL_LOGIC - Cache lookup logic
    always_comb begin
        for (int way = 0; way < WAYS; way++) begin
            way_valid[way] = cache_mem[way][index].valid;
            way_tag_match[way] = (cache_mem[way][index].tag == tag);
            way_hit[way] = way_valid[way] && way_tag_match[way];
        end
        
        any_hit = |way_hit;
        hit_way = way_hit[0] ? 0 : 1;  // For 2-way cache
    end
    
    // AI_TAG: INTERNAL_LOGIC - LRU replacement logic (for 2-way cache)
    always_comb begin
        if (WAYS == 2) begin
            // Use LRU bit to determine replacement way
            replace_way = cache_mem[0][miss_index].lru ? 0 : 1;
        end else begin
            replace_way = 0;  // Default for single-way cache
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - Cache state machine
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            cache_state_r <= IDLE;
        end else begin
            cache_state_r <= cache_state_next;
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - State machine next state logic
    always_comb begin
        cache_state_next = cache_state_r;
        
        case (cache_state_r)
            IDLE: begin
                if (flush_i) begin
                    cache_state_next = FLUSH_STATE;
                end else if (valid_i && !any_hit) begin
                    cache_state_next = MISS_WAIT;
                end
            end
            
            MISS_WAIT: begin
                if (mem_arready_i && mem_arvalid_o) begin
                    cache_state_next = MISS_FILL;
                end
            end
            
            MISS_FILL: begin
                if (fill_complete) begin
                    cache_state_next = IDLE;
                end
            end
            
            FLUSH_STATE: begin
                cache_state_next = IDLE;
            end
            
            default: begin
                cache_state_next = IDLE;
            end
        endcase
    end
    
    // AI_TAG: INTERNAL_LOGIC - Miss detection and handling
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            miss_detected <= 1'b0;
            miss_index <= '0;
            miss_tag <= '0;
            fill_offset <= '0;
        end else begin
            if (cache_state_r == IDLE && valid_i && !any_hit) begin
                miss_detected <= 1'b1;
                miss_index <= index;
                miss_tag <= tag;
                fill_offset <= '0;
            end else if (cache_state_r == MISS_FILL && mem_rvalid_i && mem_rready_o) begin
                fill_offset <= fill_offset + 1;
                if (fill_offset == WORDS_PER_LINE - 1) begin
                    miss_detected <= 1'b0;
                end
            end
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - Fill completion detection
    assign fill_complete = (fill_offset == WORDS_PER_LINE - 1) && mem_rvalid_i && mem_rready_o;
    
    // AI_TAG: INTERNAL_LOGIC - Cache data access
    always_comb begin
        if (any_hit) begin
            // Hit - return data from cache
            instruction_o = cache_mem[hit_way][index].data[offset[OFFSET_BITS-1:2]];
            hit_o = 1'b1;
            valid_o = 1'b1;
        end else if (cache_state_r == MISS_FILL && mem_rvalid_i && mem_rready_o) begin
            // Miss fill - return data from memory
            instruction_o = mem_rdata_i;
            hit_o = 1'b0;
            valid_o = 1'b1;
        end else begin
            // No valid data
            instruction_o = '0;
            hit_o = 1'b0;
            valid_o = 1'b0;
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - Cache ready signal
    assign ready_o = (cache_state_r == IDLE) && !flush_i;
    
    // AI_TAG: INTERNAL_LOGIC - Memory interface control
    assign mem_arvalid_o = (cache_state_r == MISS_WAIT);
    assign mem_araddr_o = {miss_tag, miss_index, fill_offset, 2'b00};  // Aligned to word boundary
    assign mem_rready_o = (cache_state_r == MISS_FILL);
    
    // AI_TAG: INTERNAL_LOGIC - Cache update logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // AI_TAG: RESET_STRATEGY - Clear all cache entries on reset
            for (int way = 0; way < WAYS; way++) begin
                for (int set = 0; set < SETS; set++) begin
                    cache_mem[way][set].valid <= 1'b0;
                    cache_mem[way][set].tag <= '0;
                    cache_mem[way][set].lru <= 1'b0;
                    for (int word = 0; word < WORDS_PER_LINE; word++) begin
                        cache_mem[way][set].data[word] <= '0;
                    end
                end
            end
        end else if (cache_state_r == MISS_FILL && mem_rvalid_i && mem_rready_o) begin
            // Fill cache line with memory data
            cache_mem[replace_way][miss_index].data[fill_offset] <= mem_rdata_i;
            
            if (fill_offset == WORDS_PER_LINE - 1) begin
                // Complete the cache line fill
                cache_mem[replace_way][miss_index].valid <= 1'b1;
                cache_mem[replace_way][miss_index].tag <= miss_tag;
                
                // Update LRU bit for 2-way cache
                if (WAYS == 2) begin
                    cache_mem[0][miss_index].lru <= (replace_way == 1);
                    cache_mem[1][miss_index].lru <= (replace_way == 0);
                end
            end
        end else if (cache_state_r == FLUSH_STATE) begin
            // AI_TAG: RESET_STRATEGY - Clear all valid bits during flush
            for (int way = 0; way < WAYS; way++) begin
                for (int set = 0; set < SETS; set++) begin
                    cache_mem[way][set].valid <= 1'b0;
                end
            end
        end else if (any_hit && valid_i) begin
            // Update LRU bit on cache hit (for 2-way cache)
            if (WAYS == 2) begin
                cache_mem[0][index].lru <= (hit_way == 1);
                cache_mem[1][index].lru <= (hit_way == 0);
            end
        end
    end
    
    // AI_TAG: INTERNAL_LOGIC - Flush completion signal
    assign flush_done_o = (cache_state_r == FLUSH_STATE);

endmodule : icache

`default_nettype wire 