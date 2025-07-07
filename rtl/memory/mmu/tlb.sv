`timescale 1ns / 1ps

import mmu_pkg::*;

module tlb #(
  parameter int TLB_SIZE = MMU_TLB_SIZE,
  parameter int TLB_ASSOC = MMU_TLB_ASSOC,
  parameter int VADDR_WIDTH = MMU_VADDR_WIDTH,
  parameter int PADDR_WIDTH = MMU_PADDR_WIDTH,
  parameter int PAGE_SIZE_BITS = MMU_PAGE_SIZE_BITS
) (
  input  logic                   clk,
  input  logic                   rst_n,

  // TLB lookup request
  input  mmu_request_t           mmu_req_i,
  input  logic                   req_valid_i,
  output logic                   req_ready_o,

  // TLB lookup response
  output logic [PADDR_WIDTH-1:0] paddr_o,
  output logic                   hit_o,
  output logic                   fault_o,
  output logic [3:0]             fault_type_o,

  // TLB update interface (from page table walker)
  input  tlb_entry_t             tlb_entry_i,
  input  logic                   tlb_update_valid_i,
  output logic                   tlb_update_ready_o,

  // TLB invalidate interface
  input  logic                   tlb_invalidate_valid_i,
  input  logic [VADDR_WIDTH-1:0] tlb_invalidate_vaddr_i,
  output logic                   tlb_invalidate_ready_o
);

  // Derived parameters
  localparam int VPN_WIDTH = VADDR_WIDTH - PAGE_SIZE_BITS;
  localparam int PPN_WIDTH = PADDR_WIDTH - PAGE_SIZE_BITS;
  localparam int NUM_SETS = TLB_SIZE / TLB_ASSOC;
  localparam int SET_BITS = $clog2(NUM_SETS);
  localparam int TAG_BITS = VPN_WIDTH - SET_BITS;

  // TLB memory: array of sets, each set is an array of ways
  tlb_entry_t tlb_mem[NUM_SETS][TLB_ASSOC];
  logic lru_counter[NUM_SETS]; // LRU for each set (0 for way 0, 1 for way 1)

  // Internal signals
  logic [SET_BITS-1:0]  set_index;
  logic [TAG_BITS-1:0]  tag;
  logic [PAGE_SIZE_BITS-1:0] page_offset;

  logic [TLB_ASSOC-1:0] hit_way;
  logic                 tlb_hit_internal;
  logic [PPN_WIDTH-1:0] ppn_out_internal;
  logic                 fault_internal;
  logic [3:0]           fault_type_internal;

  assign set_index = mmu_req_i.vaddr[PAGE_SIZE_BITS + SET_BITS - 1 : PAGE_SIZE_BITS];
  assign tag = mmu_req_i.vaddr[VADDR_WIDTH - 1 : PAGE_SIZE_BITS + SET_BITS];
  assign page_offset = mmu_req_i.vaddr[PAGE_SIZE_BITS - 1 : 0];

  // TLB lookup logic
  always_comb begin
    tlb_hit_internal = 1'b0;
    ppn_out_internal = '0;
    fault_internal = 1'b0;
    fault_type_internal = '0;
    hit_way = '0;

    for (int i = 0; i < TLB_ASSOC; i++) begin
      if (tlb_mem[set_index][i].valid && (tlb_mem[set_index][i].vpn == tag)) begin
        tlb_hit_internal = 1'b1;
        hit_way[i] = 1'b1;
        ppn_out_internal = tlb_mem[set_index][i].ppn;

        // Permission checks
        if (mmu_req_i.is_fetch && !tlb_mem[set_index][i].execute) begin
          fault_internal = 1'b1;
          fault_type_internal = EXC_CAUSE_INSTR_PAGE_FAULT;
        end else if (mmu_req_i.is_write && !tlb_mem[set_index][i].write) begin
          fault_internal = 1'b1;
          fault_type_internal = EXC_CAUSE_STORE_PAGE_FAULT;
        end else if (!mmu_req_i.is_write && !mmu_req_i.is_fetch && !tlb_mem[set_index][i].read) begin
          fault_internal = 1'b1;
          fault_type_internal = EXC_CAUSE_LOAD_PAGE_FAULT;
        end
        break;
      end
    end
  end

  assign paddr_o = {ppn_out_internal, page_offset};
  assign hit_o = tlb_hit_internal;
  assign fault_o = fault_internal;
  assign fault_type_o = fault_type_internal;

  // TLB update logic
  assign tlb_update_ready_o = 1'b1; // Always ready to accept updates for now

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < NUM_SETS; i++) begin
        for (int j = 0; j < TLB_ASSOC; j++) begin
          tlb_mem[i][j].valid <= 1'b0;
        end
        lru_counter[i] <= '0;
      end
    end else begin
      // Handle TLB updates
      if (tlb_update_valid_i && tlb_update_ready_o) begin
        // LRU replacement for 2-way associative TLB
        if (TLB_ASSOC == 2) begin
          if (lru_counter[set_index] == 1'b0) begin // Way 0 is LRU
            tlb_mem[set_index][0] <= tlb_entry_i;
            lru_counter[set_index] <= 1'b1; // Way 0 becomes MRU
          end else begin // Way 1 is LRU
            tlb_mem[set_index][1] <= tlb_entry_i;
            lru_counter[set_index] <= 1'b0; // Way 1 becomes MRU
          end
        end else begin
          // For now, simple direct write to way 0 for other associativities
          tlb_mem[set_index][0] <= tlb_entry_i;
        end
      end

      // Handle TLB invalidation
      if (tlb_invalidate_valid_i && tlb_invalidate_ready_o) begin
        logic [SET_BITS-1:0] invalidate_set_index;
        logic [TAG_BITS-1:0] invalidate_tag;

        invalidate_set_index = tlb_invalidate_vaddr_i[PAGE_SIZE_BITS + SET_BITS - 1 : PAGE_SIZE_BITS];
        invalidate_tag = tlb_invalidate_vaddr_i[VADDR_WIDTH - 1 : PAGE_SIZE_BITS + SET_BITS];

        for (int i = 0; i < TLB_ASSOC; i++) begin
          if (tlb_mem[invalidate_set_index][i].valid && (tlb_mem[invalidate_set_index][i].vpn == invalidate_tag)) begin
            tlb_mem[invalidate_set_index][i].valid <= 1'b0;
            break;
          end
        end
      end

      // Update LRU on hit
      if (req_valid_i && req_ready_o && tlb_hit_internal) begin
        if (TLB_ASSOC == 2) begin
          if (hit_way[0]) begin // Hit on way 0
            lru_counter[set_index] <= 1'b1; // Way 0 becomes MRU, Way 1 becomes LRU
          end else if (hit_way[1]) begin // Hit on way 1
            lru_counter[set_index] <= 1'b0; // Way 1 becomes MRU, Way 0 becomes LRU
          end
        end
      end
    end
  end

  // Request ready logic
  assign req_ready_o = 1'b1; // TLB is combinational for lookup, always ready for request

endmodule
